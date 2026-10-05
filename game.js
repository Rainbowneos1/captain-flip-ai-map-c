/* =====================================================================================
 * 《航海争夺》浏览器引擎（地图 C）——纯逻辑、无 DOM、无网络。
 *
 * 本文件是 `cfs/engine.py` + `cfs/belief.py` + `cfs/encode.py` 三者的**逐行忠实移植**，
 * 目的只有一个：让网页里跑出来的局面、特征与决策，跟训练/评估时的 Python 完全一致。
 * 因此这里刻意保留了 Python 侧的结构（生成器驱动、同样的常量、同样的字段名），
 * 而不是重写成"更好看"的 JS 风格。
 *
 *   CFS.ROLES / ROLE_KEYS / N_ROLES     角色表（索引顺序 = 训练用的 ROLE_INDEX）
 *   CFS.MAP_C                           地图 C 的 5 列定义
 *   CFS.Game                            对局（生成器协程 + 决策点协议）
 *   CFS.MeanFieldBelief                 均值场牌堆后验（信念特征）
 *   CFS.BeliefDriver                    公共视图序列 → 信念事件
 *   CFS.encode / CFS.FeatureConfig      公共视图 → 网络输入（599/580 维）
 *   CFS.runScript                       与 jsref/engine.mjs 同构的脚本驱动（对拍用）
 *
 * 决策点（地图 C 只会出现前三种）：
 *   PHASE_FLIP=0    动作 0=保持朝上面放置 / 1=翻面（不可逆）
 *   PHASE_COL=1     动作 = 列号 0..4
 *   PHASE_MONKEY=2  动作 = 相邻方块在 view.monkeyNeighbors 里的下标
 *   PHASE_FLIP_TILE=3（地图 E 专属，地图 C 不会出现）
 * ===================================================================================== */
(function (global) {
  'use strict';

  // ============================== 常量（cfs/engine.py L33-L78） ==============================
  var ROLE_KEYS = ['chef', 'parrot', 'cartographer', 'navigator', 'gunner',
                   'monkey', 'lookout', 'carpenter', 'sailor'];
  var N_ROLES = ROLE_KEYS.length;              // 9
  var ROLE_INDEX = {};
  for (var _i = 0; _i < N_ROLES; _i++) ROLE_INDEX[ROLE_KEYS[_i]] = _i;

  var CHEF = 0, PARROT = 1, CARTOGRAPHER = 2, NAVIGATOR = 3, GUNNER = 4,
      MONKEY = 5, LOOKOUT = 6, CARPENTER = 7, SAILOR = 8;

  var ROLES = {
    chef:         { name: '厨师',   emoji: '👨‍🍳', short: '厨' },
    parrot:       { name: '鹦鹉',   emoji: '🦜', short: '鹦' },
    cartographer: { name: '制图师', emoji: '🗺️', short: '图' },
    navigator:    { name: '领航员', emoji: '🧭', short: '航' },
    gunner:       { name: '炮手',   emoji: '💣', short: '炮' },
    monkey:       { name: '猴子',   emoji: '🐒', short: '猴' },
    lookout:      { name: '瞭望员', emoji: '🚩', short: '瞭' },
    carpenter:    { name: '木匠',   emoji: '🪚', short: '木' },
    sailor:       { name: '水手',   emoji: '⚓', short: '水' }
  };

  var N_COLS = 5, N_ROWS = 5;

  // 地图 C：每列自下而上的行号 + 列奖励（rows 升序 ⇒ 从下往上填）。
  // 列奖励：第 0 列 treasure（填满即得藏宝图）；第 1 列 end_if_same（终局此列角色全同 +6）；
  //         第 3 列 end_if_all_distinct（终局此列角色互不相同 +4）；第 2 / 第 4 列无奖励。
  // end_if_same / end_if_all_distinct 在列被填满时**什么都不做**（不是漏写），
  // 只在终局计分里结算 —— 见 `_computeEndScores` 第 5 步。
  var MAP_C = {
    key: 'C',
    columns: [
      { rows: [0, 1, 2],       reward: { type: 'treasure' } },
      { rows: [0, 1, 2],       reward: { type: 'end_if_same', score: 6 } },
      { rows: [0, 1],          reward: null },
      { rows: [0, 1, 2, 3, 4], reward: { type: 'end_if_all_distinct', score: 4 } },
      { rows: [0, 1],          reward: null }
    ]
  };

  var PHASE_FLIP = 0, PHASE_COL = 1, PHASE_MONKEY = 2, PHASE_FLIP_TILE = 3, PHASE_DONE = 9;
  var PHASE_NAMES = ['flip', 'col', 'monkey', 'flip_tile'];

  var BOOM_RULE_LOSE = 'lose';   // 现行规则：炮手 ≥3 判负且该方记 0 分
  var BOOM_COUNT = 3;

  var NEIGHBOR_DIRS = [[-1, 0], [1, 0], [0, -1], [0, 1]];  // 下、上、左、右

  var DEFAULT_MAX_DECISIONS = 4000;

  // ============================== Tile / Player ==============================
  function Tile(f0, f1, up) {
    this.f0 = f0; this.f1 = f1; this.up = up | 0;
  }
  Tile.prototype.role = function () { return this.up === 0 ? this.f0 : this.f1; };
  Tile.prototype.back = function () { return this.up === 0 ? this.f1 : this.f0; };
  Tile.prototype.flip = function () { this.up = 1 - this.up; };

  function upRole(t) { return t.up === 0 ? t.f0 : t.f1; }

  function Player(index) {
    this.index = index;
    this.score = 0;
    this.grid = [];
    for (var r = 0; r < N_ROWS; r++) {
      var row = [];
      for (var c = 0; c < N_COLS; c++) row.push(null);
      this.grid.push(row);
    }
    this.finished = [false, false, false, false, false];
    this.gunners = 0;
  }

  // ============================== 牌堆（index.html createDeck/drawTile） ==============================
  function makeDeck(rng) {
    var deck = [], i, j, k, up;
    for (i = 0; i < N_ROLES; i++) {
      for (j = i + 1; j < N_ROLES; j++) {
        for (k = 0; k < 2; k++) {
          up = rng() < 0.5 ? 0 : 1;
          deck.push(new Tile(i, j, up));
        }
      }
    }
    for (i = deck.length - 1; i > 0; i--) {
      j = Math.floor(rng() * (i + 1));
      var tmp = deck[i]; deck[i] = deck[j]; deck[j] = tmp;
    }
    return deck;
  }

  // 把「建牌+洗牌+尾部弹出」展平成抽牌顺序（与 cfs.engine.draw_order_from_seed 等价）
  function drawOrderFromRng(rng) {
    var deck = makeDeck(rng), out = [], i;
    for (i = deck.length - 1; i >= 0; i--) out.push([deck[i].f0, deck[i].f1, deck[i].up]);
    return out;
  }

  function mulberry32(a) {
    return function () {
      a |= 0; a = (a + 0x6D2B79F5) | 0;
      var t = Math.imul(a ^ (a >>> 15), 1 | a);
      t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
      return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
    };
  }

  // ============================== Game ==============================
  /**
   * opts:
   *   seed        整数种子（用内置 RNG 造牌堆）
   *   drawOrder   [[f0,f1,up], ...] 固定抽牌顺序（优先于 seed；对拍/复现用）
   *   rng        () => [0,1) 自定义随机源（优先于 seed）
   *   maxDecisions 决策点上限（猴子互翻兜底）
   *   onEvent    事件回调（仅用于界面日志，不影响逻辑）
   */
  function Game(opts) {
    opts = opts || {};
    this.boomRule = opts.boomRule || BOOM_RULE_LOSE;
    this.seed = (opts.seed === undefined || opts.seed === null) ? null : opts.seed;
    this._fixedDraw = opts.drawOrder ? opts.drawOrder.map(function (t) {
      return [t[0] | 0, t[1] | 0, t[2] | 0];
    }) : null;
    if (!this._fixedDraw && this.seed === null && !opts.rng) {
      throw new Error('需要 seed / drawOrder / rng 之一');
    }
    this._rng = opts.rng || mulberry32((this.seed === null ? 1 : this.seed) >>> 0);
    this.maxDecisions = opts.maxDecisions || DEFAULT_MAX_DECISIONS;
    this.onEvent = opts.onEvent || null;

    this._initState();
    this._gen = this._runGame();
    var first = this._gen.next();
    this.decision = first.value;
    this.phase = this.decision[0];
  }

  Game.prototype._initState = function () {
    this.players = [new Player(0), new Player(1)];
    this.treasureOwner = null;
    this.colFirstCompleted = [null, null, null, null, null];
    this.outerTurn = 0;
    this.turnsTotal = 0;
    this.discards = 0;
    this.acting = 0;
    this.phase = PHASE_FLIP;
    this.curTile = null;
    this.curFlipped = false;
    this.placeable = [0, 1, 2, 3, 4];
    this.monkeyNeighbors = [];
    this.flipTileCells = [];
    this._queue = this._fixedDraw ? this._fixedDraw.slice() : drawOrderFromRng(this._rng);
    this._queuePos = 0;
    this._refills = 0;
    this.winner = null;
    this.revealSerial = 0;
    this.lastReveal = null;
    this.done = false;
    this.truncated = false;
    this.decisionCount = 0;
  };

  Game.prototype._draw = function () {
    if (this._queuePos >= this._queue.length) {
      if (this._fixedDraw) throw new Error('drawOrder exhausted');
      this._queue = drawOrderFromRng(this._rng);
      this._queuePos = 0;
      this._refills++;
    }
    var e = this._queue[this._queuePos];
    this._queuePos++;
    return new Tile(e[0], e[1], e[2]);
  };

  Game.prototype._emit = function (ev) {
    if (this.onEvent) { ev.turn = this.outerTurn; this.onEvent(ev); }
  };

  // -------- 规则工具 --------
  Game.prototype._columnFull = function (p, col) {
    var rows = MAP_C.columns[col].rows;
    for (var i = 0; i < rows.length; i++) if (p.grid[rows[i]][col] === null) return false;
    return true;
  };

  Game.prototype._placeableColumns = function (p) {
    var res = [];
    for (var c = 0; c < N_COLS; c++) {
      if (this._columnFull(p, c)) continue;
      var req = MAP_C.columns[c].requiresMinScore;
      if (req !== undefined && req !== null && p.score < req) continue;
      res.push(c);
    }
    return res;
  };

  Game.prototype._bottomEmptyRow = function (p, col) {
    var rows = MAP_C.columns[col].rows;
    for (var i = 0; i < rows.length; i++) if (p.grid[rows[i]][col] === null) return rows[i];
    return null;
  };

  Game.prototype._neighbors = function (p, row, col) {
    var res = [];
    for (var i = 0; i < NEIGHBOR_DIRS.length; i++) {
      var nr = row + NEIGHBOR_DIRS[i][0], nc = col + NEIGHBOR_DIRS[i][1];
      if (nr >= 0 && nr < N_ROWS && nc >= 0 && nc < N_COLS && p.grid[nr][nc] !== null) {
        res.push([nr, nc]);
      }
    }
    return res;
  };

  Game.prototype._flip = function (tile) {
    var old = upRole(tile);
    tile.flip();
    this.lastReveal = [old, upRole(tile)];
    this.revealSerial++;
  };

  Game.prototype._addScore = function (pidx, delta) {
    var p = this.players[pidx];
    var s = p.score + delta;
    p.score = s > 0 ? s : 0;           // index.html addScore：max(0, score + delta)
    return p.score;
  };

  // -------- 协程主体（cfs/engine.py _do_turn / _resolve_role / _resolve_column_reward） --------
  Game.prototype._doTurn = function* (pidx) {
    var p = this.players[pidx];
    this.acting = pidx;
    this.turnsTotal++;

    var tile = this._draw();
    this.curTile = tile;
    this.curFlipped = false;
    this.phase = PHASE_FLIP;
    this._emit({ k: 'draw', p: pidx, role: upRole(tile) });
    var act = yield [PHASE_FLIP, [0, 1]];
    if (act === 1) {
      this._flip(tile);
      this.curFlipped = true;
      this._emit({ k: 'flip', p: pidx, from: this.lastReveal[0], to: this.lastReveal[1] });
    }

    var cols = this._placeableColumns(p);
    this.placeable = cols.slice();
    if (cols.length === 0) {
      this.discards++;                 // 没有合法列 → 方块直接弃掉，回合照常收尾
      this._emit({ k: 'discard', p: pidx, role: upRole(tile) });
      return;
    }

    this.phase = PHASE_COL;
    var col = yield [PHASE_COL, cols.slice()];
    if (cols.indexOf(col) < 0) throw new Error('illegal column ' + col + ' legal=' + cols);
    var row = this._bottomEmptyRow(p, col);
    if (row === null) { this.discards++; this._emit({ k: 'discard', p: pidx, role: upRole(tile) }); return; }
    p.grid[row][col] = tile;
    this._emit({ k: 'place', p: pidx, role: upRole(tile), row: row, col: col });

    yield* this._resolveRole(pidx, row, col, tile);

    if (this._columnFull(p, col) && !p.finished[col]) {
      p.finished[col] = true;          // 先置位，再结算（index.html L493-L496）
      this._emit({ k: 'colDone', p: pidx, col: col });
      yield* this._resolveColumnReward(pidx, col);
    }
  };

  Game.prototype._resolveRole = function* (pidx, row, col, tile) {
    var p = this.players[pidx];
    var role = upRole(tile);
    var n, r, c, t2;
    if (role === CHEF) {
      var cnt = 0;
      for (c = 0; c < N_COLS; c++) if (p.grid[row][c] !== null) cnt++;
      this._addScore(pidx, cnt);
      this._emit({ k: 'score', p: pidx, delta: cnt, why: 'chef' });
    } else if (role === PARROT) {
      this._emit({ k: 'parrot', p: pidx });
      yield* this._doTurn(pidx);       // 嵌套整个回合（可递归）
    } else if (role === CARTOGRAPHER) {
      this.treasureOwner = pidx;
      this._emit({ k: 'treasure', p: pidx, why: 'cartographer' });
    } else if (role === NAVIGATOR) {
      n = 0;
      for (r = 0; r < N_ROWS; r++) for (c = 0; c < N_COLS; c++) {
        t2 = p.grid[r][c];
        if (t2 !== null && upRole(t2) === CARTOGRAPHER) n++;
      }
      this._addScore(pidx, 2 * n);
      this._emit({ k: 'score', p: pidx, delta: 2 * n, why: 'navigator', n: n });
    } else if (role === GUNNER) {
      this._addScore(pidx, 5);
      this._emit({ k: 'score', p: pidx, delta: 5, why: 'gunner' });
    } else if (role === MONKEY) {
      this._addScore(pidx, 1);
      this._emit({ k: 'score', p: pidx, delta: 1, why: 'monkey' });
      var nbrs = this._neighbors(p, row, col);
      if (nbrs.length > 0) {
        this.monkeyNeighbors = nbrs.slice();
        this.phase = PHASE_MONKEY;
        var idx = yield [PHASE_MONKEY, nbrs.map(function (_, i2) { return i2; })];
        var r2 = nbrs[idx][0], c2 = nbrs[idx][1];
        var t = p.grid[r2][c2];
        if (t !== null) {
          this._flip(t);
          this._emit({ k: 'monkeyFlip', p: pidx, row: r2, col: c2, from: this.lastReveal[0], to: this.lastReveal[1] });
          yield* this._resolveRole(pidx, r2, c2, t);   // 新面效果递归
        }
      }
    }
    // lookout / carpenter / sailor：放置时无效果
  };

  Game.prototype._resolveColumnReward = function* (pidx, col) {
    var p = this.players[pidx];
    var reward = MAP_C.columns[col].reward;
    if (!reward) return;
    var kind = reward.type, r, c, t;
    if (kind === 'treasure') {
      this.treasureOwner = pidx;
      this._emit({ k: 'treasure', p: pidx, why: 'column', col: col });
    } else if (kind === 'score') {
      this._addScore(pidx, reward.amount);
      this._emit({ k: 'score', p: pidx, delta: reward.amount, why: 'column', col: col });
    } else if (kind === 'first_complete') {
      if (this.colFirstCompleted[col] === null) {
        this.colFirstCompleted[col] = pidx;
        this._addScore(pidx, reward.first);
      } else {
        this._addScore(pidx, reward.second);
      }
    } else if (kind === 'lose_score') {
      this._addScore(pidx, -reward.amount);
    } else if (kind === 'score_per_completed_cols') {
      var done = 0;
      for (c = 0; c < N_COLS; c++) if (p.finished[c]) done++;
      this._addScore(pidx, reward.multiplier * done);
    } else if (kind === 'score_distinct_roles') {
      var seen = {};
      var rows = MAP_C.columns[col].rows;
      for (r = 0; r < rows.length; r++) {
        t = p.grid[rows[r]][col];
        if (t !== null) seen[upRole(t)] = 1;
      }
      this._addScore(pidx, reward.multiplier * Object.keys(seen).length);
    } else if (kind === 'if_same_then') {
      var rows2 = MAP_C.columns[col].rows;
      var first = upRole(p.grid[rows2[0]][col]), same = true;
      for (r = 1; r < rows2.length; r++) if (upRole(p.grid[rows2[r]][col]) !== first) same = false;
      if (same) {
        if (reward.action === 'treasure') this.treasureOwner = pidx;
        else if (reward.action === 'extra_turn') yield* this._doTurn(pidx);
      }
    } else if (kind === 'if_all_distinct_then') {
      var rows3 = MAP_C.columns[col].rows, rolesArr = [], uniq = {};
      for (r = 0; r < rows3.length; r++) {
        var rr = upRole(p.grid[rows3[r]][col]);
        rolesArr.push(rr); uniq[rr] = 1;
      }
      if (Object.keys(uniq).length === rolesArr.length && reward.action === 'flip_tile') {
        var cells = [];
        for (r = 0; r < N_ROWS; r++) for (c = 0; c < N_COLS; c++) if (p.grid[r][c] !== null) cells.push([r, c]);
        if (cells.length > 0) {
          this.flipTileCells = cells.slice();
          this.phase = PHASE_FLIP_TILE;
          var idx = yield [PHASE_FLIP_TILE, cells.map(function (_, i2) { return i2; })];
          var r2 = cells[idx][0], c2 = cells[idx][1];
          var t2 = p.grid[r2][c2];
          if (t2 !== null) { this._flip(t2); yield* this._resolveRole(pidx, r2, c2, t2); }
        }
      }
    } else if (kind === 'flip_prisoner' || kind === 'release_prisoner') {
      throw new Error('地图 G 的囚徒奖励（flip_prisoner / release_prisoner）不属于本部署：'
        + '本页引擎只实现地图 C 的列奖励');
    }
    // end_if_same / end_if_all_distinct：地图 C 的第 1 / 第 3 列。列被填满时**什么都不做**
    //（不是漏写），留待终局计分 —— 见 _computeEndScores 第 5 步。
  };

  // -------- 终局计分与胜负（cfs/engine.py _compute_end_scores） --------
  Game.prototype._computeEndScores = function () {
    for (var pidx = 0; pidx < 2; pidx++) {
      var p = this.players[pidx], g = p.grid, r, c, rr, cc, t, t2;
      // 1) 瞭望员：所在列最顶端 → +4（逐个结算）
      for (r = 0; r < N_ROWS; r++) for (c = 0; c < N_COLS; c++) {
        t = g[r][c];
        if (t !== null && upRole(t) === LOOKOUT) {
          var hasAbove = false;
          for (rr = r + 1; rr < N_ROWS; rr++) if (g[rr][c] !== null) { hasAbove = true; break; }
          if (!hasAbove) { this._addScore(pidx, 4); this._emit({ k: 'score', p: pidx, delta: 4, why: 'lookout' }); }
        }
      }
      // 2) 木匠：同行同列均无炮手 → +3（逐个结算）
      for (r = 0; r < N_ROWS; r++) for (c = 0; c < N_COLS; c++) {
        t = g[r][c];
        if (t !== null && upRole(t) === CARPENTER) {
          var gunRow = false, gunCol = false;
          for (cc = 0; cc < N_COLS; cc++) {
            t2 = g[r][cc];
            if (t2 !== null && upRole(t2) === GUNNER) { gunRow = true; break; }
          }
          for (rr = 0; rr < N_ROWS; rr++) {
            t2 = g[rr][c];
            if (t2 !== null && upRole(t2) === GUNNER) { gunCol = true; break; }
          }
          if (!gunRow && !gunCol) { this._addScore(pidx, 3); this._emit({ k: 'score', p: pidx, delta: 3, why: 'carpenter' }); }
        }
      }
      // 3) 鹦鹉：每块 -1
      var parrots = 0;
      for (r = 0; r < N_ROWS; r++) for (c = 0; c < N_COLS; c++) {
        t = g[r][c];
        if (t !== null && upRole(t) === PARROT) parrots++;
      }
      if (parrots > 0) { this._addScore(pidx, -parrots); this._emit({ k: 'score', p: pidx, delta: -parrots, why: 'parrotEnd' }); }
      // 4) 水手：含至少一个水手的列数 K → +K²
      var sailorCols = 0;
      for (c = 0; c < N_COLS; c++) {
        for (r = 0; r < N_ROWS; r++) {
          t = g[r][c];
          if (t !== null && upRole(t) === SAILOR) { sailorCols++; break; }
        }
      }
      if (sailorCols > 0) { this._addScore(pidx, sailorCols * sailorCols); this._emit({ k: 'score', p: pidx, delta: sailorCols * sailorCols, why: 'sailor' }); }
      // 5) 终局计分型列奖励（地图 C）：位置与 Python `_compute_end_scores` 第 5 步一致 ——
      //    「水手」之后、「炮手计数」之前；逐列一次 _addScore（0 下限截断依赖顺序）。
      //    第 1 列已完成且角色全同 → +6；第 3 列已完成且角色互不相同 → +4。
      for (c = 0; c < N_COLS; c++) {
        var colReward = MAP_C.columns[c].reward;
        if (colReward === null) continue;
        if (colReward.type !== 'end_if_same' && colReward.type !== 'end_if_all_distinct') continue;
        if (!p.finished[c]) continue;                      // 未完成的列不结算
        var endRows = MAP_C.columns[c].rows, endRoles = [], endAllSame = true, endSeen = {};
        for (r = 0; r < endRows.length; r++) {
          var endRole = upRole(g[endRows[r]][c]);
          if (endRoles.length > 0 && endRole !== endRoles[0]) endAllSame = false;
          endRoles.push(endRole);
          endSeen[endRole] = 1;
        }
        if (colReward.type === 'end_if_same') {
          if (endAllSame) {
            this._addScore(pidx, colReward.score);
            this._emit({ k: 'score', p: pidx, delta: colReward.score, why: 'end_if_same', col: c });
          }
        } else if (Object.keys(endSeen).length === endRoles.length) {
          this._addScore(pidx, colReward.score);
          this._emit({ k: 'score', p: pidx, delta: colReward.score, why: 'end_if_all_distinct', col: c });
        }
      }
      // 6) 炮手计数
      var gc = 0;
      for (r = 0; r < N_ROWS; r++) for (c = 0; c < N_COLS; c++) {
        t = g[r][c];
        if (t !== null && upRole(t) === GUNNER) gc++;
      }
      p.gunners = gc;
    }

    var b0 = this.players[0].gunners >= BOOM_COUNT;
    var b1 = this.players[1].gunners >= BOOM_COUNT;
    if (b0) { this._addScore(0, -this.players[0].score); this._emit({ k: 'boom', p: 0 }); }
    if (b1) { this._addScore(1, -this.players[1].score); this._emit({ k: 'boom', p: 1 }); }
    if (b0 && b1) return 'draw';
    if (b0) return 1;
    if (b1) return 0;
    var s0 = this.players[0].score, s1 = this.players[1].score;
    if (s0 > s1) return 0;
    if (s1 > s0) return 1;
    if (this.treasureOwner === 0) return 0;
    if (this.treasureOwner === 1) return 1;
    return 'draw';
  };

  Game.prototype._runGame = function* () {
    var pidx = 0;
    while (true) {
      this.outerTurn++;
      yield* this._doTurn(pidx);
      // 藏宝图 +1：仅外层回合结束结算一次（嵌套回合不额外加）
      if (this.treasureOwner === pidx) {
        this._addScore(pidx, 1);
        this._emit({ k: 'score', p: pidx, delta: 1, why: 'treasure' });
      }
      var filled = 0;
      for (var c = 0; c < N_COLS; c++) if (this.players[pidx].finished[c]) filled++;
      if (filled >= 4) {
        if (pidx === 1) break;
        this.outerTurn++;
        yield* this._doTurn(1);      // 玩家1 完成 4 列 → 玩家2 补一个完整回合
        if (this.treasureOwner === 1) {
          this._addScore(1, 1);
          this._emit({ k: 'score', p: 1, delta: 1, why: 'treasure' });
        }
        break;
      }
      pidx = 1 - pidx;
    }
    this.winner = this._computeEndScores();
    this._emit({ k: 'end', winner: this.winner });
  };

  // -------- 对外协议 --------
  Game.prototype.reset = function () {
    this._initState();
    this._gen = this._runGame();
    this.decision = this._gen.next().value;
    this.phase = this.decision[0];
    return [this.publicView(), this.legalMask()];
  };

  Game.prototype.step = function (action) {
    if (this.done) throw new Error('game already done');
    var legal = this.decision[1];
    if (legal.indexOf(action) < 0) {
      throw new Error('illegal action ' + action + ' at phase ' + this.phase + ' legal=' + legal);
    }
    this.decisionCount++;
    if (this.decisionCount > this.maxDecisions) {
      this.truncated = true;
      this.winner = this._computeEndScores();
      this.done = true;
      this.phase = PHASE_DONE;
      return [this.publicView(), [], true];
    }
    var r = this._gen.next(action);
    if (r.done) {
      this.done = true;
      this.phase = PHASE_DONE;
      this.decision = [PHASE_DONE, []];
    } else {
      this.decision = r.value;
      this.phase = this.decision[0];
    }
    return [this.publicView(), this.legalMask(), this.done];
  };

  Game.prototype.legalMask = function () {
    if (this.done) return [];
    return this.decision[1].slice();
  };

  Game.prototype.publicView = function () {
    var boards = [];
    for (var pi = 0; pi < 2; pi++) {
      var p = this.players[pi], rows = [];
      for (var r = 0; r < N_ROWS; r++) {
        var row = [];
        for (var c = 0; c < N_COLS; c++) {
          var t = p.grid[r][c];
          row.push(t === null ? -1 : upRole(t));
        }
        rows.push(row);
      }
      boards.push(rows);
    }
    var tileRole = -1;
    if (this.curTile !== null && !this.done) tileRole = upRole(this.curTile);
    var inFlip = (this.phase === PHASE_FLIP) && !this.done;
    var placeable;
    if (this.done) placeable = [];
    else placeable = this._placeableColumns(this.players[this.acting]);
    return {
      phase: this.phase,
      acting: this.acting,
      boards: boards,
      scores: [this.players[0].score, this.players[1].score],
      finishedCols: [this.players[0].finished.slice(), this.players[1].finished.slice()],
      treasureOwner: this.treasureOwner,
      colFirstCompleted: this.colFirstCompleted.slice(),
      tileRole: (inFlip || this.phase === PHASE_COL || this.phase === PHASE_MONKEY) ? tileRole : -1,
      tileFlipped: !!this.curFlipped,
      placeable: placeable.slice(),
      monkeyNeighbors: (this.phase === PHASE_MONKEY) ? this.monkeyNeighbors.map(function (n) { return [n[0], n[1]]; }) : [],
      outerTurn: this.outerTurn,
      turnsTotal: this.turnsTotal,
      revealSerial: this.revealSerial,
      reveal: this.lastReveal ? [this.lastReveal[0], this.lastReveal[1]] : null,
      done: this.done
    };
  };

  // 与 jsref/replay.mjs 完全相同的 JSON 结构（跨语言对拍用）
  Game.prototype.digest = function () {
    var boardOf = function (p) {
      return p.grid.map(function (row) {
        return row.map(function (t) { return t === null ? null : ROLE_KEYS[upRole(t)]; });
      });
    };
    var winnerOut = null;
    if (this.winner !== null) winnerOut = (this.winner === 0 || this.winner === 1) ? ('p' + this.winner) : 'draw';
    return {
      ok: true,
      map: 'C',
      finished: !!this.done,
      decisionsConsumed: this.decisionCount,
      turnsOuter: this.outerTurn,
      discards: this.discards,
      gunners: [this.players[0].gunners, this.players[1].gunners],
      finalScores: [this.players[0].score, this.players[1].score],
      treasureOwner: this.treasureOwner,
      finishedCols: [this.players[0].finished.slice(), this.players[1].finished.slice()],
      colFirstCompleted: this.colFirstCompleted.slice(),
      prisoners: [[], []],
      boards: [boardOf(this.players[0]), boardOf(this.players[1])],
      winner: winnerOut
    };
  };

  // ============================== 脚本驱动（与 jsref/engine.mjs 同构） ==============================
  /**
   * script = { map:'C', boomRule:'lose'|'win', drawOrder:[{faces:[a,b],upIndex}], actions:[{t,v}|{t,r,c}] }
   * 返回 digest（+ 已消费决策数）。动作类型不符/列非法时抛错，与 jsref 的错误分支语义一致。
   * 本部署的引擎常量已固定为地图 C（MAP_C），因此 `map` 只接受 'C'：传别的地图会显式抛错，
   * 而不是拿地图 C 的列定义去跑一局标签为别的地图的脚本（硬规则 10）。
   */
  function runScript(script) {
    var map = script.map === undefined ? 'C' : script.map;
    if (map !== 'C') throw new Error('unsupported map ' + map);
    var drawOrder = script.drawOrder.map(function (e) {
      var f0 = ROLE_INDEX[e.faces[0]], f1 = ROLE_INDEX[e.faces[1]];
      if (f0 === undefined || f1 === undefined || f0 === f1) throw new Error('invalid drawOrder entry');
      if (e.upIndex !== 0 && e.upIndex !== 1) throw new Error('invalid drawOrder entry');
      return [f0, f1, e.upIndex];
    });
    var g = new Game({ drawOrder: drawOrder, boomRule: script.boomRule || BOOM_RULE_LOSE });
    var idx = 0;
    while (!g.done) {
      var a = script.actions[idx++];
      if (a === undefined) break;                    // 动作耗尽：正常退出（finished:false）
      var phase = g.phase, legal = g.decision[1], action;
      if (phase === PHASE_FLIP) {
        if (a.t !== 'flip') throw new Error('unexpected action expected flip got ' + a.t);
        if (a.v !== 0 && a.v !== 1) throw new Error('illegal flip value ' + a.v);
        action = a.v;
      } else if (phase === PHASE_COL) {
        if (a.t !== 'col') throw new Error('unexpected action expected col got ' + a.t);
        if (legal.indexOf(a.v) < 0) throw new Error('illegal column ' + a.v);
        action = a.v;
      } else if (phase === PHASE_MONKEY) {
        if (a.t !== 'monkey') throw new Error('unexpected action expected monkey got ' + a.t);
        var found = -1;
        for (var i = 0; i < legal.length; i++) {
          if (g.monkeyNeighbors[legal[i]][0] === a.r && g.monkeyNeighbors[legal[i]][1] === a.c) found = legal[i];
        }
        if (found < 0) throw new Error('illegal monkey target ' + a.r + ',' + a.c);
        action = found;
      } else {
        throw new Error('unexpected phase ' + phase);
      }
      g.step(action);
    }
    return g.digest();
  }

  // ============================== 信念追踪（cfs/belief.py MeanFieldBelief） ==============================
  var PAIRS = [], PAIR_ID = [];
  (function () {
    for (var i = 0; i < N_ROLES; i++) {
      PAIR_ID.push(new Array(N_ROLES).fill(-1));
    }
    var n = 0;
    for (var a = 0; a < N_ROLES; a++) {
      for (var b = a + 1; b < N_ROLES; b++) {
        PAIRS.push([a, b]);
        PAIR_ID[a][b] = n; PAIR_ID[b][a] = n;
        n++;
      }
    }
  })();
  var N_PAIRS = PAIRS.length;   // 36
  var DECK_SIZE = 2 * N_PAIRS;  // 72

  function MeanFieldBelief() {
    this.E = new Array(N_PAIRS).fill(2.0);
    this._total = DECK_SIZE;
    this.soft = [];        // 每次抽牌的软移除摊分记录
    this.known = [];       // 该次抽牌的完整对是否已知
    this.cellDraw = {};    // "p,r,c" -> 抽牌序号
    this.cellKnown = {};   // "p,r,c" -> 完整对是否已知
    this.refills = 0;
  }

  MeanFieldBelief.prototype.onDraw = function (visibleRole) {
    var w = {}, s = 0.0, r, pid, v;
    for (r = 0; r < N_ROLES; r++) {
      if (r === visibleRole) continue;
      pid = PAIR_ID[visibleRole][r];       // 无序对的编号（0..35），只作键使用
      v = this.E[pid];
      w[pid] = v;
      s += v;
    }
    var idx = this.soft.length;
    var keys = Object.keys(w);
    if (s <= 1e-12) {
      for (var i = 0; i < keys.length; i++) w[keys[i]] = 1.0 / Math.max(1, keys.length);
    } else {
      for (var j = 0; j < keys.length; j++) w[keys[j]] /= s;
    }
    for (var m = 0; m < keys.length; m++) this.E[keys[m] | 0] -= w[keys[m]];
    this._total -= 1.0;
    this.soft.push(w);
    this.known.push(false);
    if (this._total <= 1e-9) this._resetDeck();   // 牌堆抽空 → 引擎会重建整副
    return idx;
  };

  MeanFieldBelief.prototype.onCurrentRevealed = function (drawIdx, otherRole, visibleRole) {
    this._resolve(drawIdx, PAIR_ID[visibleRole][otherRole]);
  };

  MeanFieldBelief.prototype.bindCell = function (player, row, col, drawIdx) {
    var key = player + ',' + row + ',' + col;
    this.cellDraw[key] = drawIdx;
    this.cellKnown[key] = this.known[drawIdx];
  };

  MeanFieldBelief.prototype.onCellFlipped = function (player, row, col, oldRole, newRole) {
    var key = player + ',' + row + ',' + col;
    if (this.cellKnown[key] === undefined || this.cellKnown[key] === true) return;
    var idx = this.cellDraw[key];
    if (idx === undefined) return;
    this._resolve(idx, PAIR_ID[oldRole][newRole]);
    this.cellKnown[key] = true;
  };

  MeanFieldBelief.prototype._resolve = function (drawIdx, pairId) {
    if (this.known[drawIdx]) return;
    var rec = this.soft[drawIdx];
    if (rec) {
      for (var k in rec) if (Object.prototype.hasOwnProperty.call(rec, k)) this.E[k | 0] += rec[k];
    }
    this.E[pairId] -= 1.0;
    if (this.E[pairId] < 0.0) this.E[pairId] = 0.0;
    this.known[drawIdx] = true;
  };

  MeanFieldBelief.prototype._resetDeck = function () {
    this.E = new Array(N_PAIRS).fill(2.0);
    this._total = DECK_SIZE;
    this.refills++;
  };

  Object.defineProperty(MeanFieldBelief.prototype, 'total', { get: function () { return this._total; } });

  MeanFieldBelief.prototype.backsideDist = function (visibleRole) {
    var out = new Array(N_ROLES).fill(0.0), r, s = 0.0;
    for (r = 0; r < N_ROLES; r++) {
      if (r === visibleRole) continue;
      s += this.E[PAIR_ID[visibleRole][r]];
    }
    if (s <= 1e-12) {
      for (r = 0; r < N_ROLES; r++) if (r !== visibleRole) out[r] = 1.0 / (N_ROLES - 1);
      return out;
    }
    for (r = 0; r < N_ROLES; r++) {
      if (r === visibleRole) continue;
      out[r] = this.E[PAIR_ID[visibleRole][r]] / s;
    }
    return out;
  };

  MeanFieldBelief.prototype.remainingUpfaceExpectation = function () {
    var out = new Array(N_ROLES).fill(0.0);
    for (var i = 0; i < N_PAIRS; i++) {
      var half = this.E[i] * 0.5;
      out[PAIRS[i][0]] += half;
      out[PAIRS[i][1]] += half;
    }
    return out;
  };

  // ============================== 信念事件驱动（cfs/driver.py BeliefDriver） ==============================
  function bottomEmptyFromBoard(board, col) {
    var rows = MAP_C.columns[col].rows;
    for (var i = 0; i < rows.length; i++) if (board[rows[i]][col] < 0) return rows[i];
    return null;
  }

  function BeliefDriver(belief) {
    this.belief = belief;
    this.pendingDraw = null;
  }

  BeliefDriver.prototype.onTransition = function (phase, view, action, nxt) {
    var b = this.belief;
    if (phase === PHASE_FLIP) {
      this.pendingDraw = b.onDraw(view.tileRole);
      if (action === 1 && this.pendingDraw !== null) {
        if (nxt.revealSerial !== view.revealSerial && nxt.reveal !== null) {
          b.onCurrentRevealed(this.pendingDraw, nxt.reveal[1], nxt.reveal[0]);
        }
      }
    } else if (phase === PHASE_COL) {
      var p = view.acting;
      var row = bottomEmptyFromBoard(view.boards[p], action);
      if (row !== null && this.pendingDraw !== null) b.bindCell(p, row, action, this.pendingDraw);
    } else if (phase === PHASE_MONKEY) {
      var p2 = view.acting;
      var nbrs = view.monkeyNeighbors;
      var rr = nbrs[action][0], cc = nbrs[action][1];
      var ev = (nxt.revealSerial !== view.revealSerial && nxt.reveal !== null) ? nxt.reveal : null;
      var oldRole, newRole;
      if (ev === null) { oldRole = view.boards[p2][rr][cc]; newRole = nxt.boards[p2][rr][cc]; }
      else { oldRole = ev[0]; newRole = ev[1]; }
      if (oldRole !== newRole) b.onCellFlipped(p2, rr, cc, oldRole, newRole);
    }
  };

  // ============================== 特征编码（cfs/encode.py） ==============================
  var OFF_BOARD_SELF = 0, OFF_BOARD_OPP = 250, OFF_SCORES = 500, OFF_FIN_SELF = 502,
      OFF_FIN_OPP = 507, OFF_TREASURE = 512, OFF_COLFIRST = 515, OFF_PHASE = 530,
      OFF_TILE = 534, OFF_FLIPPED = 544, OFF_PLACEABLE = 545, OFF_MONKEYDIR = 550,
      OFF_NEIGHBOR_PLANE = 554, OFF_TURN = 579, OFF_BELIEF = 580;

  function FeatureConfig(o) {
    o = o || {};
    this.useBelief = o.use_belief !== undefined ? !!o.use_belief : true;
    this.usePairCounts = o.use_pair_counts !== undefined ? !!o.use_pair_counts : false;
    this.scoreScale = o.score_scale !== undefined ? o.score_scale : 30.0;
    this.turnScale = o.turn_scale !== undefined ? o.turn_scale : 80.0;
    this.leakDim = o.leak_dim !== undefined ? (o.leak_dim | 0) : 0;
  }
  FeatureConfig.prototype.beliefDim = function () {
    if (!this.useBelief) return 0;
    return (N_ROLES + N_ROLES + 1) + (this.usePairCounts ? 36 : 0);
  };
  FeatureConfig.prototype.dim = function () { return OFF_BELIEF + this.beliefDim() + this.leakDim; };

  function fillBoard(v, off, board) {
    for (var r = 0; r < N_ROWS; r++) {
      var row = board[r];
      var base = off + r * (N_COLS * 10);
      for (var c = 0; c < N_COLS; c++) {
        var role = row[c];
        v[base + c * 10 + (role >= 0 ? role : 9)] = 1.0;
      }
    }
  }

  function encode(view, belief, cfg) {
    if (!cfg) cfg = new FeatureConfig();
    var v = new Float32Array(cfg.dim());
    var p = view.acting | 0;
    fillBoard(v, OFF_BOARD_SELF, view.boards[p]);
    fillBoard(v, OFF_BOARD_OPP, view.boards[1 - p]);

    v[OFF_SCORES] = view.scores[p] / cfg.scoreScale;
    v[OFF_SCORES + 1] = view.scores[1 - p] / cfg.scoreScale;

    for (var c = 0; c < N_COLS; c++) {
      v[OFF_FIN_SELF + c] = view.finishedCols[p][c] ? 1.0 : 0.0;
      v[OFF_FIN_OPP + c] = view.finishedCols[1 - p][c] ? 1.0 : 0.0;
    }

    var t = view.treasureOwner;
    v[OFF_TREASURE + (t === null || t === undefined ? 0 : (t === p ? 1 : 2))] = 1.0;

    for (var c2 = 0; c2 < N_COLS; c2++) {
      var who = view.colFirstCompleted[c2];
      v[OFF_COLFIRST + c2 * 3 + (who === null || who === undefined ? 0 : (who === p ? 1 : 2))] = 1.0;
    }

    var phase = view.phase | 0;
    if (phase >= 0 && phase < 4) v[OFF_PHASE + phase] = 1.0;

    var role = view.tileRole;
    if (role >= 0) v[OFF_TILE + role] = 1.0;
    else v[OFF_TILE + N_ROLES] = 1.0;
    v[OFF_FLIPPED] = view.tileFlipped ? 1.0 : 0.0;

    for (var i = 0; i < view.placeable.length; i++) v[OFF_PLACEABLE + view.placeable[i]] = 1.0;

    for (var j = 0; j < view.monkeyNeighbors.length; j++) {
      v[OFF_NEIGHBOR_PLANE + view.monkeyNeighbors[j][0] * N_COLS + view.monkeyNeighbors[j][1]] = 1.0;
    }

    v[OFF_TURN] = view.outerTurn / cfg.turnScale;

    if (cfg.useBelief && belief) {
      var o = OFF_BELIEF, r;
      if (phase === PHASE_FLIP && role >= 0) {
        var dist = belief.backsideDist(role);
        for (r = 0; r < N_ROLES; r++) v[o + r] = dist[r];
      }
      o += N_ROLES;
      var rem = belief.remainingUpfaceExpectation();
      for (r = 0; r < N_ROLES; r++) v[o + r] = rem[r] * 0.5;
      o += N_ROLES;
      v[o] = belief.total / 72.0;
      o += 1;
      if (cfg.usePairCounts) {
        // 训练配置未启用 pair counts；保留分支仅为与 Python 对齐
        throw new Error('use_pair_counts 未在浏览器端实现（本模型 cfg 为 false）');
      }
    }
    return v;
  }

  global.CFS = {
    ROLE_KEYS: ROLE_KEYS, ROLE_INDEX: ROLE_INDEX, N_ROLES: N_ROLES, ROLES: ROLES,
    CHEF: CHEF, PARROT: PARROT, CARTOGRAPHER: CARTOGRAPHER, NAVIGATOR: NAVIGATOR,
    GUNNER: GUNNER, MONKEY: MONKEY, LOOKOUT: LOOKOUT, CARPENTER: CARPENTER, SAILOR: SAILOR,
    MAP_C: MAP_C, N_COLS: N_COLS, N_ROWS: N_ROWS,
    PHASE_FLIP: PHASE_FLIP, PHASE_COL: PHASE_COL, PHASE_MONKEY: PHASE_MONKEY,
    PHASE_FLIP_TILE: PHASE_FLIP_TILE, PHASE_DONE: PHASE_DONE, PHASE_NAMES: PHASE_NAMES,
    BOOM_RULE_LOSE: BOOM_RULE_LOSE, BOOM_COUNT: BOOM_COUNT, NEIGHBOR_DIRS: NEIGHBOR_DIRS,
    Game: Game, Tile: Tile, upRole: upRole, Player: Player,
    makeDeck: makeDeck, drawOrderFromRng: drawOrderFromRng, mulberry32: mulberry32,
    runScript: runScript,
    MeanFieldBelief: MeanFieldBelief, BeliefDriver: BeliefDriver,
    bottomEmptyFromBoard: bottomEmptyFromBoard,
    PAIRS: PAIRS, PAIR_ID: PAIR_ID, N_PAIRS: N_PAIRS, DECK_SIZE: DECK_SIZE,
    FeatureConfig: FeatureConfig, encode: encode,
    OFFSETS: {
      BOARD_SELF: OFF_BOARD_SELF, BOARD_OPP: OFF_BOARD_OPP, SCORES: OFF_SCORES,
      FIN_SELF: OFF_FIN_SELF, FIN_OPP: OFF_FIN_OPP, TREASURE: OFF_TREASURE,
      COLFIRST: OFF_COLFIRST, PHASE: OFF_PHASE, TILE: OFF_TILE, FLIPPED: OFF_FLIPPED,
      PLACEABLE: OFF_PLACEABLE, MONKEYDIR: OFF_MONKEYDIR, NEIGHBOR_PLANE: OFF_NEIGHBOR_PLANE,
      TURN: OFF_TURN, BELIEF: OFF_BELIEF
    }
  };

  if (typeof module !== 'undefined' && module.exports) module.exports = global.CFS;
})(typeof window !== 'undefined' ? window : globalThis);
