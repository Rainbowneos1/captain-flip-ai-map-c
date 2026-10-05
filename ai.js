/* =====================================================================================
 * 量化策略网络的浏览器推理（无任何依赖，加载时反量化一次）。
 *
 * 权重来源：`weights.js`（由 `export_weights.py` 从**地图 C 的检查点** `runs/c-r1/final.pt`
 * 导出，见 c-web/README.md §3；实际用到的检查点会写进 payload.source）。
 * 导出时 2D 权重矩阵按「每行沿输入维每 G 个数一组」做对称 8bit 量化，偏置保持 fp32。
 * 本文件在初始化时把 int8 + scale **反量化成 Float32Array**，之后全程按 fp32 前向，
 * 所以推理路径与训练侧 torch 的差别只来自量化本身。
 *
 *   CFS_AI.load()            读取 window.CFS_MODEL，返回 Policy 实例
 *   policy.act(view, legal, phase, belief)   确定性（argmax）选动作
 *   policy.lastInfo          最近一次前向的诊断信息（各动作 logit、价值、耗时）
 * ===================================================================================== */
(function (global) {
  'use strict';

  function b64ToU8(b64) {
    var bin = global.atob(b64);
    var n = bin.length;
    var u = new Uint8Array(n);
    for (var i = 0; i < n; i++) u[i] = bin.charCodeAt(i);
    return u;
  }

  function b64ToF32(b64) {
    var u = b64ToU8(b64);
    return new Float32Array(u.buffer, u.byteOffset, u.byteLength >> 2);
  }

  /** per-group 对称 int8 → fp32 */
  function dequantize(t) {
    var out = t.shape[0], inDim = t.shape[1], g = t.g;
    var nGroups = Math.ceil(inDim / g);
    var scales = b64ToF32(t.sc);
    var u8 = b64ToU8(t.d);
    var q = new Int8Array(u8.buffer, u8.byteOffset, u8.length);
    var W = new Float32Array(out * inDim);
    for (var r = 0; r < out; r++) {
      var rowBase = r * inDim, sBase = r * nGroups;
      for (var gi = 0; gi < nGroups; gi++) {
        var s = scales[sBase + gi];
        if (s === 0) continue;
        var lo = gi * g, hi = Math.min(inDim, lo + g);
        for (var k = lo; k < hi; k++) W[rowBase + k] = q[rowBase + k] * s;
      }
    }
    return W;
  }

  function reluInPlace(buf, n) {
    for (var i = 0; i < n; i++) if (buf[i] < 0) buf[i] = 0;
    return buf;
  }

  function Policy(payload) {
    this.payload = payload;
    this.cfgPayload = payload.cfg;
    this.arch = payload.arch;
    this.W = {};
    this.B = {};
    var i, t, name;
    for (i = 0; i < payload.tensors.length; i++) {
      t = payload.tensors[i];
      this.W[t.n] = dequantize(t);
    }
    for (name in payload.floats) {
      if (Object.prototype.hasOwnProperty.call(payload.floats, name)) {
        this.B[name] = b64ToF32(payload.floats[name].d);
      }
    }
    this.cfg = new global.CFS.FeatureConfig(payload.cfg);
    this.inDim = this.arch.in_dim;
    this.hidden = this.arch.hidden;
    this.layers = this.arch.layers;
    this.nHeads = this.arch.heads.length;
    this.lastInfo = null;
    this.stats = { forwards: 0, totalMs: 0, maxMs: 0 };
  }

  /** 主干 + 指定决策头的前向；返回值 { logits, value, hidden }（hidden 为 Float32Array 副本） */
  Policy.prototype.forward = function (feat, headIdx) {
    var h = feat, i, o, j, sum, base;
    for (var L = 0; L < this.layers; L++) {
      var w = this.W['trunk.' + (2 * L) + '.weight'];
      var b = this.B['trunk.' + (2 * L) + '.bias'];
      var dIn = (L === 0) ? this.inDim : this.hidden;
      var out = new Float32Array(this.hidden);
      for (o = 0; o < this.hidden; o++) {
        sum = b[o];
        base = o * dIn;
        for (j = 0; j < dIn; j++) sum += w[base + j] * h[j];
        out[o] = sum > 0 ? sum : 0;              // ReLU
      }
      h = out;
    }
    var hw = this.W['heads.' + headIdx + '.weight'];
    var hb = this.B['heads.' + headIdx + '.bias'];
    var hs = this.arch.heads[headIdx];
    var logits = new Float32Array(hs);
    for (o = 0; o < hs; o++) {
      sum = hb[o];
      base = o * this.hidden;
      for (j = 0; j < this.hidden; j++) sum += hw[base + j] * h[j];
      logits[o] = sum;
    }
    var vw = this.W['value.weight'], vb = this.B['value.bias'];
    sum = vb[0];
    for (j = 0; j < this.hidden; j++) sum += vw[j] * h[j];
    return { logits: logits, value: sum, hidden: h };
  };

  /**
   * 确定性（argmax）决策。`legal` 为当前决策点的合法动作数组。
   * 返回动作值；诊断信息（含被掩码的 logits 与被选动作的 softmax 概率）写入 lastInfo。
   */
  Policy.prototype.act = function (view, legal, phase, belief) {
    var t0 = (global.performance && global.performance.now) ? global.performance.now() : Date.now();
    var headIdx = phase;                       // HEAD_ORDER = (flip, col, monkey, flip_tile) 与 phase 同序
    var feat = global.CFS.encode(view, belief, this.cfg);
    var res = this.forward(feat, headIdx);
    var logits = res.logits;
    var best = -1, bestVal = -Infinity, i, a;
    for (i = 0; i < legal.length; i++) {
      a = legal[i];
      if (logits[a] > bestVal) { bestVal = logits[a]; best = a; }
    }
    // 被选中动作的 softmax 概率（只在合法动作上归一化）
    var mx = -Infinity;
    for (i = 0; i < legal.length; i++) if (logits[legal[i]] > mx) mx = logits[legal[i]];
    var den = 0, num = 0;
    for (i = 0; i < legal.length; i++) {
      var e = Math.exp(logits[legal[i]] - mx);
      den += e;
      if (legal[i] === best) num = e;
    }
    var t1 = (global.performance && global.performance.now) ? global.performance.now() : Date.now();
    var ms = t1 - t0;
    this.stats.forwards++;
    this.stats.totalMs += ms;
    if (ms > this.stats.maxMs) this.stats.maxMs = ms;
    this.lastInfo = {
      phase: phase, headIdx: headIdx, action: best, ms: ms, value: res.value,
      prob: den > 0 ? num / den : 1,
      logits: logits, legal: legal.slice(), features: feat,
      featureNorm: (function () { var s = 0; for (var k = 0; k < feat.length; k++) s += feat[k] * feat[k]; return Math.sqrt(s); })()
    };
    return best;
  };

  global.CFS_AI = {
    Policy: Policy,
    load: function (payload) {
      payload = payload || global.CFS_MODEL;
      if (!payload) throw new Error('weights.js 未加载（window.CFS_MODEL 缺失）');
      if (!global.CFS) throw new Error('game.js 未加载（window.CFS 缺失）');
      return new Policy(payload);
    }
  };

  if (typeof module !== 'undefined' && module.exports) module.exports = global.CFS_AI;
})(typeof window !== 'undefined' ? window : globalThis);
