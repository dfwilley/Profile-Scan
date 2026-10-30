/* Profile Scan — image-to-DXF engine.
 * Finds a reference sheet of paper in a photo, removes perspective, separates the
 * part from the paper, traces its outline and holes, and fits lines, arcs and
 * circles in inches. Pure JavaScript; no libraries.
 */
(function (root) {
  'use strict';

  /* ---------------- basic image helpers ---------------- */
  // gray image: {w, h, d: Float32Array}
  function grayFromRGBA(rgba, w, h) {
    var d = new Float32Array(w * h);
    for (var i = 0, j = 0; i < d.length; i++, j += 4) d[i] = 0.299 * rgba[j] + 0.587 * rgba[j + 1] + 0.114 * rgba[j + 2];
    return { w: w, h: h, d: d };
  }
  function boxDown(g, f) {
    var W = Math.floor(g.w / f), H = Math.floor(g.h / f), d = new Float32Array(W * H), n = f * f;
    for (var y = 0; y < H; y++) for (var x = 0; x < W; x++) {
      var s = 0;
      for (var yy = 0; yy < f; yy++) { var row = (y * f + yy) * g.w + x * f; for (var xx = 0; xx < f; xx++) s += g.d[row + xx]; }
      d[y * W + x] = s / n;
    }
    return { w: W, h: H, d: d };
  }
  function sample(g, x, y) {
    if (x < 0) x = 0; if (y < 0) y = 0; if (x > g.w - 1.001) x = g.w - 1.001; if (y > g.h - 1.001) y = g.h - 1.001;
    var x0 = x | 0, y0 = y | 0, fx = x - x0, fy = y - y0, i = y0 * g.w + x0;
    return (g.d[i] * (1 - fx) + g.d[i + 1] * fx) * (1 - fy) + (g.d[i + g.w] * (1 - fx) + g.d[i + g.w + 1] * fx) * fy;
  }
  function otsu(values) {
    var hist = new Float64Array(256), n = 0;
    for (var i = 0; i < values.length; i++) { var v = values[i] | 0; if (v < 0) v = 0; if (v > 255) v = 255; hist[v]++; n++; }
    var sum = 0; for (i = 0; i < 256; i++) sum += i * hist[i];
    var sumB = 0, wB = 0, best = 0, t = 127;
    for (i = 0; i < 256; i++) {
      wB += hist[i]; if (!wB) continue; var wF = n - wB; if (!wF) break;
      sumB += i * hist[i]; var mB = sumB / wB, mF = (sum - sumB) / wF, between = wB * wF * (mB - mF) * (mB - mF);
      if (between > best) { best = between; t = i; }
    }
    return t + 0.5;
  }

  /* ---------------- paper detection ---------------- */
  function largestComponent(mask, w, h) {
    var lab = new Int32Array(w * h), best = 0, bestId = 0, id = 0, q = new Int32Array(w * h);
    for (var s = 0; s < w * h; s++) {
      if (!mask[s] || lab[s]) continue;
      id++; var head = 0, tail = 0, cnt = 0; q[tail++] = s; lab[s] = id;
      while (head < tail) {
        var p = q[head++], x = p % w, y = (p - x) / w; cnt++;
        if (x > 0 && mask[p - 1] && !lab[p - 1]) { lab[p - 1] = id; q[tail++] = p - 1; }
        if (x < w - 1 && mask[p + 1] && !lab[p + 1]) { lab[p + 1] = id; q[tail++] = p + 1; }
        if (y > 0 && mask[p - w] && !lab[p - w]) { lab[p - w] = id; q[tail++] = p - w; }
        if (y < h - 1 && mask[p + w] && !lab[p + w]) { lab[p + w] = id; q[tail++] = p + w; }
      }
      if (cnt > best) { best = cnt; bestId = id; }
    }
    return { lab: lab, id: bestId, count: best };
  }
  function convexHull(pts) {
    pts = pts.slice().sort(function (a, b) { return a[0] - b[0] || a[1] - b[1]; });
    function cr(o, a, b) { return (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0]); }
    var lo = [], up = [], i;
    for (i = 0; i < pts.length; i++) { while (lo.length >= 2 && cr(lo[lo.length - 2], lo[lo.length - 1], pts[i]) <= 0) lo.pop(); lo.push(pts[i]); }
    for (i = pts.length - 1; i >= 0; i--) { while (up.length >= 2 && cr(up[up.length - 2], up[up.length - 1], pts[i]) <= 0) up.pop(); up.push(pts[i]); }
    up.pop(); lo.pop(); return lo.concat(up);
  }
  function polyArea(p) { var a = 0; for (var i = 0; i < p.length; i++) { var q = p[(i + 1) % p.length]; a += p[i][0] * q[1] - q[0] * p[i][1]; } return a / 2; }
  // Largest-area quadrilateral using hull vertices (diagonal i-k, best apex on each side).
  function hullToQuad(hull) {
    var p = hull, n = p.length;
    if (n > 160) { var st = n / 160, q = []; for (var s = 0; s < 160; s++) q.push(p[Math.floor(s * st)]); p = q; n = p.length; }
    function tri(a, b, c) { return Math.abs((b[0] - a[0]) * (c[1] - a[1]) - (b[1] - a[1]) * (c[0] - a[0])); }
    var best = -1, bq = null;
    for (var i = 0; i < n; i++) for (var k = i + 2; k < n; k++) {
      var bj = -1, ba = -1, bl = -1, bb = -1;
      for (var j = i + 1; j < k; j++) { var a = tri(p[i], p[j], p[k]); if (a > ba) { ba = a; bj = j; } }
      for (var l = k + 1; l < n + i; l++) { var b = tri(p[k], p[l % n], p[i]); if (b > bb) { bb = b; bl = l % n; } }
      if (bj >= 0 && bl >= 0 && ba + bb > best) { best = ba + bb; bq = [p[i], p[bj], p[k], p[bl]]; }
    }
    return bq || p.slice(0, 4);
  }
  // order corners: TL, TR, BR, BL (image coordinates, y down)
  function orderCorners(q) {
    var cx = 0, cy = 0; q.forEach(function (p) { cx += p[0]; cy += p[1]; }); cx /= 4; cy /= 4;
    q = q.slice().sort(function (a, b) { return Math.atan2(a[1] - cy, a[0] - cx) - Math.atan2(b[1] - cy, b[0] - cx); });
    var k = 0, m = Infinity; q.forEach(function (p, i) { if (p[0] + p[1] < m) { m = p[0] + p[1]; k = i; } });
    return q.slice(k).concat(q.slice(0, k));
  }

  function detectPaper(g) {
    var f = Math.max(1, Math.round(Math.max(g.w, g.h) / 480)), s = boxDown(g, f);
    var t = otsu(s.d), mask = new Uint8Array(s.w * s.h);
    for (var i = 0; i < mask.length; i++) mask[i] = s.d[i] > t ? 1 : 0;
    var cc = largestComponent(mask, s.w, s.h);
    if (cc.count < s.w * s.h * 0.05) return null;
    var pts = [];
    for (var y = 0; y < s.h; y++) for (var x = 0; x < s.w; x++) {
      var p = y * s.w + x; if (cc.lab[p] !== cc.id) continue;
      if (x === 0 || y === 0 || x === s.w - 1 || y === s.h - 1 || cc.lab[p - 1] !== cc.id || cc.lab[p + 1] !== cc.id || cc.lab[p - s.w] !== cc.id || cc.lab[p + s.w] !== cc.id)
        pts.push([(x + 0.5) * f, (y + 0.5) * f]);
    }
    var hull = convexHull(pts);
    if (hull.length < 4) return null;
    var quad = orderCorners(hullToQuad(hull));
    var touches = quad.some(function (p) { return p[0] < 2 * f || p[1] < 2 * f || p[0] > g.w - 2 * f || p[1] > g.h - 2 * f; });
    return { corners: refineCorners(g, quad), rough: quad, touchesEdge: touches };
  }

  // Sharpen each paper edge with sub-pixel gradient search and a robust line fit.
  function refineCorners(g, q) {
    var cx = 0, cy = 0; q.forEach(function (p) { cx += p[0]; cy += p[1]; }); cx /= 4; cy /= 4;
    var lines = [];
    for (var k = 0; k < 4; k++) {
      var A = q[k], B = q[(k + 1) % 4], dx = B[0] - A[0], dy = B[1] - A[1], L = Math.hypot(dx, dy);
      if (L < 10) return q;
      var tx = dx / L, ty = dy / L, nx = -ty, ny = tx;
      var mx = (A[0] + B[0]) / 2, my = (A[1] + B[1]) / 2;
      if ((mx - cx) * nx + (my - cy) * ny < 0) { nx = -nx; ny = -ny; }   // outward
      var R = Math.max(6, Math.round(L * 0.025)), pts = [];
      for (var sIdx = 0; sIdx < 60; sIdx++) {
        var t = 0.1 + 0.8 * sIdx / 59, px = A[0] + dx * t, py = A[1] + dy * t;
        var best = 0, bestS = null, prev = [];
        for (var s = -R; s <= R; s++) {
          var d = sample(g, px + nx * (s + 1), py + ny * (s + 1)) - sample(g, px + nx * (s - 1), py + ny * (s - 1));
          prev.push(d);
          if (d < best) { best = d; bestS = s; }
        }
        if (bestS === null || best > -20) continue;
        var i0 = bestS + R, sub = 0;
        if (i0 > 0 && i0 < prev.length - 1) { var a = prev[i0 - 1], b = prev[i0], c = prev[i0 + 1], den = a - 2 * b + c; if (den) sub = 0.5 * (a - c) / den; }
        var e = bestS + sub; pts.push([px + nx * e, py + ny * e]);
      }
      if (pts.length < 10) return q;
      var ln = fitLine(pts);
      for (var it = 0; it < 2; it++) {
        var keep = pts.filter(function (p) { return Math.abs((p[0] - ln.x) * ln.nx + (p[1] - ln.y) * ln.ny) < 1.5; });
        if (keep.length >= 8) ln = fitLine(keep);
      }
      lines.push(ln);
    }
    var out = [];
    for (k = 0; k < 4; k++) {
      var l1 = lines[(k + 3) % 4], l2 = lines[k], P = intersect(l1, l2);
      if (!P || Math.hypot(P[0] - q[k][0], P[1] - q[k][1]) > Math.max(g.w, g.h) * 0.03) return q;
      out.push(P);
    }
    return out;
  }
  function fitLine(pts) {
    var n = pts.length, mx = 0, my = 0; pts.forEach(function (p) { mx += p[0]; my += p[1]; }); mx /= n; my /= n;
    var sxx = 0, sxy = 0, syy = 0; pts.forEach(function (p) { var a = p[0] - mx, b = p[1] - my; sxx += a * a; sxy += a * b; syy += b * b; });
    var th = 0.5 * Math.atan2(2 * sxy, sxx - syy), dx = Math.cos(th), dy = Math.sin(th);
    return { x: mx, y: my, dx: dx, dy: dy, nx: -dy, ny: dx };
  }
  function intersect(a, b) {
    var den = a.dx * b.dy - a.dy * b.dx; if (Math.abs(den) < 1e-9) return null;
    var t = ((b.x - a.x) * b.dy - (b.y - a.y) * b.dx) / den;
    return [a.x + a.dx * t, a.y + a.dy * t];
  }

  /* ---------------- perspective ---------------- */
  // Homography mapping src[i] -> dst[i]
  function homography(src, dst) {
    var A = [], b = [];
    for (var i = 0; i < 4; i++) {
      var x = src[i][0], y = src[i][1], u = dst[i][0], v = dst[i][1];
      A.push([x, y, 1, 0, 0, 0, -u * x, -u * y]); b.push(u);
      A.push([0, 0, 0, x, y, 1, -v * x, -v * y]); b.push(v);
    }
    var h = solve(A, b); if (!h) return null; h.push(1); return h;
  }
  function solve(A, b) {
    var n = b.length, M = A.map(function (r, i) { return r.concat([b[i]]); });
    for (var c = 0; c < n; c++) {
      var piv = c; for (var r = c + 1; r < n; r++) if (Math.abs(M[r][c]) > Math.abs(M[piv][c])) piv = r;
      if (Math.abs(M[piv][c]) < 1e-12) return null;
      var tmp = M[c]; M[c] = M[piv]; M[piv] = tmp;
      for (r = 0; r < n; r++) { if (r === c) continue; var f = M[r][c] / M[c][c]; for (var k = c; k <= n; k++) M[r][k] -= f * M[c][k]; }
    }
    return M.map(function (r, i) { return r[n] / r[i]; });
  }
  function applyH(H, x, y) { var w = H[6] * x + H[7] * y + H[8]; return [(H[0] * x + H[1] * y + H[2]) / w, (H[3] * x + H[4] * y + H[5]) / w]; }

  // Warp RGBA photo into a flat, to-scale image of the paper.
  function rectify(rgba, sw, sh, corners, wIn, hIn, ppi) {
    var W = Math.round(wIn * ppi), H = Math.round(hIn * ppi);
    var Hm = homography([[0, 0], [W, 0], [W, H], [0, H]], corners);
    var out = new Uint8ClampedArray(W * H * 4), gray = new Float32Array(W * H);
    for (var v = 0; v < H; v++) for (var u = 0; u < W; u++) {
      var p = applyH(Hm, u + 0.5, v + 0.5), x = p[0] - 0.5, y = p[1] - 0.5;
      if (x < 0) x = 0; if (y < 0) y = 0; if (x > sw - 1.001) x = sw - 1.001; if (y > sh - 1.001) y = sh - 1.001;
      var x0 = x | 0, y0 = y | 0, fx = x - x0, fy = y - y0, i = (y0 * sw + x0) * 4, o = (v * W + u) * 4;
      var w00 = (1 - fx) * (1 - fy), w10 = fx * (1 - fy), w01 = (1 - fx) * fy, w11 = fx * fy, j = sw * 4;
      for (var c = 0; c < 3; c++) out[o + c] = rgba[i + c] * w00 + rgba[i + 4 + c] * w10 + rgba[i + j + c] * w01 + rgba[i + j + 4 + c] * w11;
      out[o + 3] = 255;
      gray[v * W + u] = 0.299 * out[o] + 0.587 * out[o + 1] + 0.114 * out[o + 2];
    }
    return { w: W, h: H, rgba: out, gray: { w: W, h: H, d: gray }, toRect: homography(corners, [[0, 0], [W, 0], [W, H], [0, H]]) };
  }

  /* ---------------- part segmentation ---------------- */
  function percentile(arr, p) { var a = Array.prototype.slice.call(arr).sort(function (x, y) { return x - y; }); return a[Math.min(a.length - 1, Math.floor(p * a.length))]; }

  // Flatten uneven lighting by dividing by an estimate of the bare-paper brightness.
  function normalize(g, ppi) {
    var B = Math.max(8, Math.round(ppi * 0.5)), bw = Math.ceil(g.w / B), bh = Math.ceil(g.h / B), bg = new Float32Array(bw * bh);
    for (var by = 0; by < bh; by++) for (var bx = 0; bx < bw; bx++) {
      var vals = [];
      for (var y = by * B; y < Math.min(g.h, by * B + B); y += 2) for (var x = bx * B; x < Math.min(g.w, bx * B + B); x += 2) vals.push(g.d[y * g.w + x]);
      bg[by * bw + bx] = percentile(vals, 0.9);
    }
    var med = percentile(bg, 0.5), good = new Uint8Array(bw * bh);
    for (var i = 0; i < bg.length; i++) good[i] = bg[i] > med * 0.8 ? 1 : 0;
    for (var pass = 0; pass < bw + bh; pass++) {           // fill blocks covered by the part
      var changed = false, nb = new Float32Array(bg), ng = new Uint8Array(good);
      for (by = 0; by < bh; by++) for (bx = 0; bx < bw; bx++) {
        var k = by * bw + bx; if (good[k]) continue; var s = 0, n = 0;
        [[-1, 0], [1, 0], [0, -1], [0, 1]].forEach(function (o) { var xx = bx + o[0], yy = by + o[1]; if (xx >= 0 && yy >= 0 && xx < bw && yy < bh && good[yy * bw + xx]) { s += bg[yy * bw + xx]; n++; } });
        if (n) { nb[k] = s / n; ng[k] = 1; changed = true; }
      }
      bg = nb; good = ng; if (!changed) break;
    }
    var out = new Float32Array(g.w * g.h);
    for (y = 0; y < g.h; y++) for (x = 0; x < g.w; x++) {
      var fx = Math.min(bw - 1.001, Math.max(0, x / B - 0.5)), fy = Math.min(bh - 1.001, Math.max(0, y / B - 0.5));
      var x0 = fx | 0, y0 = fy | 0, ax = fx - x0, ay = fy - y0, x1 = Math.min(bw - 1, x0 + 1), y1 = Math.min(bh - 1, y0 + 1);
      var b = (bg[y0 * bw + x0] * (1 - ax) + bg[y0 * bw + x1] * ax) * (1 - ay) + (bg[y1 * bw + x0] * (1 - ax) + bg[y1 * bw + x1] * ax) * ay;
      out[y * g.w + x] = Math.min(255, 200 * g.d[y * g.w + x] / Math.max(1, b));
    }
    return { w: g.w, h: g.h, d: out };
  }

  function morph(mask, w, h, r, dilate) {
    var cur = mask;
    for (var k = 0; k < r; k++) {
      var nxt = new Uint8Array(w * h), eight = k % 2 === 1;
      for (var y = 0; y < h; y++) for (var x = 0; x < w; x++) {
        var p = y * w + x, v = cur[p];
        if (dilate ? !v : v) {
          var hit = false;
          for (var dy = -1; dy <= 1 && !hit; dy++) for (var dx = -1; dx <= 1; dx++) {
            if (!dx && !dy) continue; if (!eight && dx && dy) continue;
            var xx = x + dx, yy = y + dy; if (xx < 0 || yy < 0 || xx >= w || yy >= h) { if (!dilate) { hit = true; break; } continue; }
            if (dilate ? cur[yy * w + xx] : !cur[yy * w + xx]) { hit = true; break; }
          }
          nxt[p] = dilate ? (hit ? 1 : 0) : (hit ? 0 : 1);
        } else nxt[p] = v;
      }
      cur = nxt;
    }
    return cur;
  }

  // opts: {ppi, marginIn, sensitivity (-30..30), smoothPx, minHoleIn}
  function segment(gray, opts) {
    var ppi = opts.ppi, w = gray.w, h = gray.h, n = normalize(gray, ppi), m = Math.round((opts.marginIn || 0.15) * ppi);
    var inner = []; for (var y = m; y < h - m; y += 2) for (var x = m; x < w - m; x += 2) inner.push(n.d[y * w + x]);
    var t = otsu(inner);
    t = Math.min(185, Math.max(40, t)) + (opts.sensitivity || 0);
    var mask = new Uint8Array(w * h);
    for (y = m; y < h - m; y++) for (x = m; x < w - m; x++) mask[y * w + x] = n.d[y * w + x] < t ? 1 : 0;
    var r = opts.smoothPx == null ? 2 : opts.smoothPx;
    if (r > 0) { mask = morph(morph(mask, w, h, r, true), w, h, r, false); mask = morph(morph(mask, w, h, r, false), w, h, r, true); }
    var cc = largestComponent(mask, w, h);
    if (cc.count < ppi * ppi * 0.02) return { mask: null, threshold: t, norm: n };
    var part = new Uint8Array(w * h); for (var i = 0; i < part.length; i++) part[i] = cc.lab[i] === cc.id ? 1 : 0;
    // Background regions not connected to the border are holes; fill tiny ones (noise).
    var bgc = new Uint8Array(w * h); for (i = 0; i < part.length; i++) bgc[i] = part[i] ? 0 : 1;
    var lab = new Int32Array(w * h), id = 0, q = new Int32Array(w * h), minA = Math.PI * Math.pow((opts.minHoleIn || 0.04) * ppi / 2, 2);
    for (var s = 0; s < w * h; s++) {
      if (!bgc[s] || lab[s]) continue; id++; var head = 0, tail = 0, border = false, members = []; q[tail++] = s; lab[s] = id;
      while (head < tail) {
        var p = q[head++], px = p % w, py = (p - px) / w; members.push(p);
        if (px === 0 || py === 0 || px === w - 1 || py === h - 1) border = true;
        if (px > 0 && bgc[p - 1] && !lab[p - 1]) { lab[p - 1] = id; q[tail++] = p - 1; }
        if (px < w - 1 && bgc[p + 1] && !lab[p + 1]) { lab[p + 1] = id; q[tail++] = p + 1; }
        if (py > 0 && bgc[p - w] && !lab[p - w]) { lab[p - w] = id; q[tail++] = p - w; }
        if (py < h - 1 && bgc[p + w] && !lab[p + w]) { lab[p + w] = id; q[tail++] = p + w; }
      }
      if (!border && members.length < minA) members.forEach(function (k) { part[k] = 1; });
    }
    var touches = false;
    for (x = 0; x < w && !touches; x++) if (part[m * w + x] || part[(h - m - 1) * w + x]) touches = true;
    for (y = 0; y < h && !touches; y++) if (part[y * w + m] || part[y * w + w - m - 1]) touches = true;
    return { mask: part, threshold: t, norm: n, touchesMargin: touches, areaPx: cc.count };
  }

  /* ---------------- contour tracing (marching squares) ---------------- */
  function traceContours(mask, w, h) {
    // padded, lightly blurred field for smooth sub-pixel boundaries
    var W = w + 2, H = h + 2, f = new Float32Array(W * H), g = new Float32Array(W * H), x, y;
    for (y = 0; y < h; y++) for (x = 0; x < w; x++) f[(y + 1) * W + x + 1] = mask[y * w + x];
    for (var pass = 0; pass < 2; pass++) {
      for (y = 1; y < H - 1; y++) for (x = 1; x < W - 1; x++) g[y * W + x] = (f[y * W + x - 1] + f[y * W + x] * 2 + f[y * W + x + 1]) / 4;
      for (y = 1; y < H - 1; y++) for (x = 1; x < W - 1; x++) f[y * W + x] = (g[(y - 1) * W + x] + g[y * W + x] * 2 + g[(y + 1) * W + x]) / 4;
    }
    var iso = 0.5, segs = [], pos = {};
    function ep(id, x0, y0, x1, y1, v0, v1) { if (!pos[id]) { var t = (iso - v0) / (v1 - v0); pos[id] = [x0 + (x1 - x0) * t - 1, y0 + (y1 - y0) * t - 1]; } return id; }
    for (y = 0; y < H - 1; y++) for (x = 0; x < W - 1; x++) {
      var a = f[y * W + x], b = f[y * W + x + 1], c = f[(y + 1) * W + x + 1], d = f[(y + 1) * W + x];
      var code = (a > iso ? 8 : 0) | (b > iso ? 4 : 0) | (c > iso ? 2 : 0) | (d > iso ? 1 : 0);
      if (code === 0 || code === 15) continue;
      var T = 'h' + (y * W + x), R = 'v' + (y * W + x + 1), B = 'h' + ((y + 1) * W + x), L = 'v' + (y * W + x);
      var eT = function () { return ep(T, x, y, x + 1, y, a, b); }, eR = function () { return ep(R, x + 1, y, x + 1, y + 1, b, c); };
      var eB = function () { return ep(B, x, y + 1, x + 1, y + 1, d, c); }, eL = function () { return ep(L, x, y, x, y + 1, a, d); };
      var center = (a + b + c + d) / 4;
      switch (code) {
        case 1: case 14: segs.push([eL(), eB()]); break;
        case 2: case 13: segs.push([eB(), eR()]); break;
        case 3: case 12: segs.push([eL(), eR()]); break;
        case 4: case 11: segs.push([eT(), eR()]); break;
        case 6: case 9: segs.push([eT(), eB()]); break;
        case 7: case 8: segs.push([eL(), eT()]); break;
        case 5: if (center > iso) { segs.push([eL(), eT()]); segs.push([eB(), eR()]); } else { segs.push([eL(), eB()]); segs.push([eT(), eR()]); } break;
        case 10: if (center > iso) { segs.push([eT(), eR()]); segs.push([eL(), eB()]); } else { segs.push([eL(), eT()]); segs.push([eB(), eR()]); } break;
      }
    }
    var adj = {};
    segs.forEach(function (s, i) { (adj[s[0]] = adj[s[0]] || []).push(i); (adj[s[1]] = adj[s[1]] || []).push(i); });
    var used = new Uint8Array(segs.length), loops = [];
    for (var i = 0; i < segs.length; i++) {
      if (used[i]) continue; used[i] = 1;
      var start = segs[i][0], cur = segs[i][1], loop = [pos[start]], guard = 0;
      while (cur !== start && guard++ < 2000000) {
        loop.push(pos[cur]);
        var nextSeg = -1, list = adj[cur] || [];
        for (var k = 0; k < list.length; k++) if (!used[list[k]]) { nextSeg = list[k]; break; }
        if (nextSeg < 0) break;
        used[nextSeg] = 1; cur = segs[nextSeg][0] === cur ? segs[nextSeg][1] : segs[nextSeg][0];
      }
      if (loop.length >= 8) loops.push(loop);
    }
    return loops;
  }

  /* ---------------- geometry fitting ---------------- */
  function resample(loop, ds) {
    var out = [loop[0]], acc = 0, n = loop.length;
    for (var i = 0; i < n; i++) {
      var a = loop[i], b = loop[(i + 1) % n], L = Math.hypot(b[0] - a[0], b[1] - a[1]), pos = 0;
      while (acc + (L - pos) >= ds) { pos += ds - acc; acc = 0; var t = pos / L; out.push([a[0] + (b[0] - a[0]) * t, a[1] + (b[1] - a[1]) * t]); }
      acc += L - pos;
    }
    if (out.length > 2 && Math.hypot(out[out.length - 1][0] - out[0][0], out[out.length - 1][1] - out[0][1]) < ds * 0.5) out.pop();
    return out;
  }
  function fitCircle(pts) {           // Kasa algebraic fit, then max/rms deviation
    var n = pts.length, mx = 0, my = 0; pts.forEach(function (p) { mx += p[0]; my += p[1]; }); mx /= n; my /= n;
    var suu = 0, svv = 0, suv = 0, suuu = 0, svvv = 0, suvv = 0, svuu = 0;
    pts.forEach(function (p) { var u = p[0] - mx, v = p[1] - my; suu += u * u; svv += v * v; suv += u * v; suuu += u * u * u; svvv += v * v * v; suvv += u * v * v; svuu += v * u * u; });
    var det = suu * svv - suv * suv; if (Math.abs(det) < 1e-12) return null;
    var r1 = 0.5 * (suuu + suvv), r2 = 0.5 * (svvv + svuu);
    var uc = (r1 * svv - r2 * suv) / det, vc = (suu * r2 - suv * r1) / det;
    var cx = uc + mx, cy = vc + my, r = Math.sqrt(uc * uc + vc * vc + (suu + svv) / n);
    var mx2 = 0, ss = 0; pts.forEach(function (p) { var e = Math.abs(Math.hypot(p[0] - cx, p[1] - cy) - r); ss += e * e; if (e > mx2) mx2 = e; });
    return { cx: cx, cy: cy, r: r, rms: Math.sqrt(ss / n), max: mx2 };
  }
  function circle3(a, b, c) {
    var d = 2 * (a[0] * (b[1] - c[1]) + b[0] * (c[1] - a[1]) + c[0] * (a[1] - b[1])); if (Math.abs(d) < 1e-12) return null;
    var a2 = a[0] * a[0] + a[1] * a[1], b2 = b[0] * b[0] + b[1] * b[1], c2 = c[0] * c[0] + c[1] * c[1];
    var ux = (a2 * (b[1] - c[1]) + b2 * (c[1] - a[1]) + c2 * (a[1] - b[1])) / d, uy = (a2 * (c[0] - b[0]) + b2 * (a[0] - c[0]) + c2 * (b[0] - a[0])) / d;
    return { cx: ux, cy: uy, r: Math.hypot(a[0] - ux, a[1] - uy) };
  }
  function rdp(pts, i0, i1, eps, keep) {
    var a = pts[i0], b = pts[i1], dx = b[0] - a[0], dy = b[1] - a[1], L = Math.hypot(dx, dy) || 1e-12, best = -1, bi = -1;
    for (var i = i0 + 1; i < i1; i++) { var d = Math.abs((pts[i][0] - a[0]) * dy - (pts[i][1] - a[1]) * dx) / L; if (d > best) { best = d; bi = i; } }
    if (best > eps) { rdp(pts, i0, bi, eps, keep); keep.push(bi); rdp(pts, bi, i1, eps, keep); }
  }
  function sweepOK(pts, c) {         // points progress monotonically around the center, one direction, < 350 degrees
    var tot = 0, sgn = 0;
    for (var i = 1; i < pts.length; i++) {
      var a0 = Math.atan2(pts[i - 1][1] - c.cy, pts[i - 1][0] - c.cx), a1 = Math.atan2(pts[i][1] - c.cy, pts[i][0] - c.cx), d = a1 - a0;
      if (d > Math.PI) d -= 2 * Math.PI; if (d < -Math.PI) d += 2 * Math.PI;
      if (Math.abs(d) < 1e-9) continue; var s = d > 0 ? 1 : -1; if (sgn && s !== sgn) return 0; sgn = s; tot += d;
    }
    return Math.abs(tot) < Math.PI * 350 / 180 ? Math.abs(tot) : 0;
  }

  // loop: points in inches. Returns entities.
  function fitLoop(loop, o) {
    var P = resample(loop, o.ds), n = P.length, ents = [];
    if (n < 8) return ents;
    var whole = fitCircle(P);
    if (whole && whole.max < Math.max(o.arcTol * 1.5, whole.r * 0.02) && whole.r > 0.01) {
      ents.push({ type: 'circle', cx: whole.cx, cy: whole.cy, r: whole.r }); return ents;
    }
    // start at the sharpest corner
    var k = 3, bestI = 0, bestT = -1;
    for (var i = 0; i < n; i++) {
      var a = P[(i - k + n) % n], b = P[i], c = P[(i + k) % n];
      var t = Math.abs(Math.atan2((b[0] - a[0]) * (c[1] - b[1]) - (b[1] - a[1]) * (c[0] - b[0]), (b[0] - a[0]) * (c[0] - b[0]) + (b[1] - a[1]) * (c[1] - b[1])));
      if (t > bestT) { bestT = t; bestI = i; }
    }
    P = P.slice(bestI).concat(P.slice(0, bestI)); P.push(P[0]);
    var far = 1, fd = -1;
    for (i = 1; i < P.length - 1; i++) { var dd = Math.hypot(P[i][0] - P[0][0], P[i][1] - P[0][1]); if (dd > fd) { fd = dd; far = i; } }
    var keep = [0, far]; rdp(P, 0, far, o.lineTol, keep); rdp(P, far, P.length - 1, o.lineTol, keep); keep.push(P.length - 1); keep.sort(function (x, y) { return x - y; });
    var items = segmentDense(P, keep, o);
    // If the loop's start fell in the middle of a feature (first and last pieces are the same
    // line or arc), restart the loop at the beginning of the last piece and segment again.
    if (items.length > 2 && !o._rotated) {
      var A = items[items.length - 1], B = items[0], same = false;
      if (A.type === B.type) {
        var both = P.slice(A.i0, P.length - 1).concat(P.slice(0, B.i1 + 1));
        if (A.type === 'arc') { var cf2 = fitCircle(both); same = cf2 && cf2.max < o.arcTol && sweepOK(both, cf2); }
        else { var lf = fitLine(both), dev = 0; both.forEach(function (q) { dev = Math.max(dev, Math.abs((q[0] - lf.x) * lf.nx + (q[1] - lf.y) * lf.ny)); }); same = dev < o.lineTol; }
      }
      if (same) {
        var o2 = Object.assign({}, o, { _rotated: true }), Q = P.slice(A.i0, P.length - 1).concat(P.slice(0, A.i0));
        return fitLoopDense(Q, o2);
      }
    }
    return regularize(P, items, o);
  }
  function fitLoopDense(Q, o) {      // Q: open dense loop (no repeated end), start already chosen
    var P = Q.concat([Q[0]]), far = 1, fd = -1;
    for (var i = 1; i < P.length - 1; i++) { var dd = Math.hypot(P[i][0] - P[0][0], P[i][1] - P[0][1]); if (dd > fd) { fd = dd; far = i; } }
    var keep = [0, far]; rdp(P, 0, far, o.lineTol, keep); rdp(P, far, P.length - 1, o.lineTol, keep); keep.push(P.length - 1); keep.sort(function (x, y) { return x - y; });
    return regularize(P, segmentDense(P, keep, o), o);
  }
  function segmentDense(P, keep, o) {
    var V = keep, items = [], vi = 0;
    while (vi < V.length - 1) {
      var bestJ = -1, bestC = null;
      for (var j = vi + 2; j < V.length; j++) {
        var seg = P.slice(V[vi], V[j] + 1), cf = fitCircle(seg);
        if (!cf || cf.r > o.maxArcR || cf.max > o.arcTol) break;
        var sw = sweepOK(seg, cf); if (!sw) break;
        if (sw >= 25 * Math.PI / 180) { bestJ = j; bestC = cf; }
      }
      if (bestJ > 0) { items.push({ type: 'arc', i0: V[vi], i1: V[bestJ], fit: bestC }); vi = bestJ; continue; }
      items.push({ type: 'line', i0: V[vi], i1: V[vi + 1] }); vi++;
    }
    return items;
  }

  /* Clean up a traced loop: merge collinear lines, drop tiny fragments, make sharp
     corners exact intersections, and turn line-arc-line runs into true tangent fillets. */
  function lineFit(P, i0, i1) {
    var n = i1 - i0, a = i0 + Math.floor(n * 0.12), b = i1 - Math.floor(n * 0.12);
    if (b - a < 2) { a = i0; b = i1; }
    var f = fitLine(P.slice(a, b + 1));
    return { x: f.x, y: f.y, dx: f.dx, dy: f.dy, nx: f.nx, ny: f.ny };
  }
  function regularize(P, items, o) {
    var N = P.length - 1;                       // P[N] == P[0]
    function len(it) { return Math.hypot(P[it.i1][0] - P[it.i0][0], P[it.i1][1] - P[it.i0][1]); }
    // 1) merge consecutive near-collinear lines (cyclic)
    var merged = true;
    while (merged && items.length > 2) {
      merged = false;
      for (var k = 0; k < items.length - 1; k++) {   // loop starts at its sharpest corner, so no wrap-around merge needed
        var A = items[k], B = items[k + 1];
        if (A.type !== 'line' || B.type !== 'line') continue;
        var comb = P.slice(A.i0, B.i1 + 1), f = lineFit(P, A.i0, B.i1), dev = 0, cnt = 0;
        comb.forEach(function (q, qi) { var e = Math.abs((q[0] - f.x) * f.nx + (q[1] - f.y) * f.ny); if (qi > comb.length * 0.1 && qi < comb.length * 0.9 && e > dev) dev = e; });
        if (dev < o.lineTol * 0.8) { A.i1 = B.i1; items.splice(k + 1, 1); merged = true; break; }
      }
    }
    // 2) classify; drop junk (tiny lines, tiny arcs)
    var minLine = 0.06, minR = 0.05;
    items.forEach(function (it) {
      if (it.type === 'line') { it.L = len(it); it.junk = it.L < minLine; if (!it.junk) it.g = lineFit(P, it.i0, it.i1); }
      else { var f = fitCircle(P.slice(it.i0, it.i1 + 1)); it.c = f; it.junk = !f || f.r < minR; }
    });
    var kept = items.filter(function (it) { return !it.junk; });
    if (kept.length < 2) { // fall back to plain polyline
      return items.map(function (it) { return { type: 'line', a: P[it.i0], b: P[it.i1] }; });
    }
    var n = kept.length;
    // junction point between kept[k] and kept[k+1]
    function junction(A, B) {
      var ia = A.i1, ib = B.i0; if (ib < ia) ib += N;   // junk spans between
      return P[Math.round((ia + ib) / 2) % N];
    }
    var startPt = new Array(n), endPt = new Array(n), fillet = new Array(n);
    // 3) fillets for line-arc-line
    for (k = 0; k < n; k++) {
      var it = kept[k], prev = kept[(k - 1 + n) % n], next = kept[(k + 1) % n];
      if (it.type !== 'arc' || prev.type !== 'line' || next.type !== 'line' || n < 3) continue;
      var fl = tangentFillet(prev.g, next.g, it.c.r, it.c);
      if (fl) { fillet[k] = fl; startPt[k] = fl.t1; endPt[k] = fl.t2; endPt[(k - 1 + n) % n] = fl.t1; startPt[(k + 1) % n] = fl.t2; }
    }
    // 4) remaining joins
    for (k = 0; k < n; k++) {
      var A2 = kept[k], B2 = kept[(k + 1) % n];
      if (endPt[k] && startPt[(k + 1) % n]) continue;
      var J = junction(A2, B2);
      if (A2.type === 'line' && B2.type === 'line') {
        var X = intersect(A2.g, B2.g), ang = Math.abs(A2.g.dx * B2.g.dy - A2.g.dy * B2.g.dx);
        if (X && ang > Math.sin(8 * Math.PI / 180) && Math.hypot(X[0] - J[0], X[1] - J[1]) < 0.2) J = X;
      }
      endPt[k] = J; startPt[(k + 1) % n] = J;
    }
    // 5) emit
    var ents = [];
    for (k = 0; k < n; k++) {
      var e = kept[k], a = startPt[k], b = endPt[k];
      if (e.type === 'line') { if (Math.hypot(b[0] - a[0], b[1] - a[1]) > 1e-4) ents.push({ type: 'line', a: a, b: b }); continue; }
      var c0 = fillet[k] ? { cx: fillet[k].cx, cy: fillet[k].cy, r: fillet[k].r } : e.c;
      var pm = P[Math.round((e.i0 + e.i1) / 2)], um = Math.hypot(pm[0] - c0.cx, pm[1] - c0.cy) || 1;
      var mid = [c0.cx + (pm[0] - c0.cx) / um * c0.r, c0.cy + (pm[1] - c0.cy) / um * c0.r];
      var cc = circle3(a, mid, b);
      if (!cc || cc.r > o.maxArcR) { ents.push({ type: 'line', a: a, b: b }); continue; }
      var ccw = ((mid[0] - a[0]) * (b[1] - mid[1]) - (mid[1] - a[1]) * (b[0] - mid[0])) > 0;
      ents.push({ type: 'arc', cx: cc.cx, cy: cc.cy, r: cc.r, p0: a, p1: mid, p2: b, ccw: ccw });
    }
    return ents;
  }
  // Fillet of radius r tangent to infinite lines g1 (incoming) and g2 (outgoing), on the side of the fitted arc center.
  function tangentFillet(g1, g2, r, arcFit) {
    var best = null, parallel = Math.abs(g1.dx * g2.dy - g1.dy * g2.dx) < 0.02;
    if (!parallel) [-1, 1].forEach(function (s1) { [-1, 1].forEach(function (s2) {
      var o1 = { x: g1.x + g1.nx * r * s1, y: g1.y + g1.ny * r * s1, dx: g1.dx, dy: g1.dy };
      var o2 = { x: g2.x + g2.nx * r * s2, y: g2.y + g2.ny * r * s2, dx: g2.dx, dy: g2.dy };
      var c = intersect(o1, o2); if (!c) return;
      var d = Math.hypot(c[0] - arcFit.cx, c[1] - arcFit.cy);
      if (!best || d < best.d) best = { d: d, c: c };
    }); });
    function foot(g, c) { var t = (c[0] - g.x) * g.dx + (c[1] - g.y) * g.dy; return [g.x + g.dx * t, g.y + g.dy * t]; }
    if (!best) {   // parallel lines: half-round end (like a tab or slot)
      if (!parallel) return null;
      var sep = Math.abs((g2.x - g1.x) * g1.nx + (g2.y - g1.y) * g1.ny), rr = sep / 2;
      if (Math.abs(rr - r) > r * 0.15 + 0.02) return null;
      var mid = { x: (g1.x + g2.x) / 2, y: (g1.y + g2.y) / 2, dx: g1.dx, dy: g1.dy };
      var c0 = foot(mid, [arcFit.cx, arcFit.cy]);
      return { cx: c0[0], cy: c0[1], r: rr, t1: foot(g1, c0), t2: foot(g2, c0) };
    }
    if (best.d > r * 0.5 + 0.02) return null;
    return { cx: best.c[0], cy: best.c[1], r: r, t1: foot(g1, best.c), t2: foot(g2, best.c) };
  }

  var FR = [2, 4, 8, 16, 32, 64];
  function snapDia(d, mode) {
    if (mode === 'thou') return Math.round(d * 1000) / 1000;
    if (mode === '64') return Math.round(d * 64) / 64;
    if (mode === '32') return Math.round(d * 32) / 32;
    if (mode === 'mm') return Math.round(d * 25.4 * 10) / 254;
    return d;
  }

  /* opts: {ppi, rectH (px), scale (1), thicknessIn, cameraHeightIn, nadir:[u,v] px, snap, lineTol, arcTol} */
  function buildProfile(loops, opts) {
    var ppi = opts.ppi, Hpx = opts.rectH, k = opts.scale || 1;
    var t = opts.thicknessIn || 0, hc = opts.cameraHeightIn || 14, shrink = t > 0 && hc > t ? (hc - t) / hc : 1;
    var nx = opts.nadir ? opts.nadir[0] / ppi : 0, ny = opts.nadir ? (Hpx - opts.nadir[1]) / ppi : 0;
    var L = loops.map(function (lp) {
      return lp.map(function (p) {
        var X = p[0] / ppi, Y = (Hpx - p[1]) / ppi;
        X = nx + (X - nx) * shrink; Y = ny + (Y - ny) * shrink;
        return [X * k, Y * k];
      });
    });
    var areas = L.map(function (lp) { return Math.abs(polyArea(lp)); }), outer = areas.indexOf(Math.max.apply(null, areas));
    var minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity;
    L[outer].forEach(function (p) { minX = Math.min(minX, p[0]); minY = Math.min(minY, p[1]); maxX = Math.max(maxX, p[0]); maxY = Math.max(maxY, p[1]); });
    L = L.map(function (lp) { return lp.map(function (p) { return [p[0] - minX, p[1] - minY]; }); });
    var o = { ds: 0.01, lineTol: opts.lineTol || 0.008, arcTol: opts.arcTol || 0.01, maxArcR: 30 };
    var outline = fitLoop(L[outer], o), holes = [];
    L.forEach(function (lp, i) {
      if (i === outer || areas[i] < 0.0004) return;
      var e = fitLoop(lp, o);
      e.forEach(function (x) { if (x.type === 'circle' && opts.snap) x.r = snapDia(2 * x.r, opts.snap) / 2; });
      holes.push(e);
    });
    var all = outline.concat.apply(outline, holes);
    // inches (profile coords) -> rectified-image pixels, for drawing over the photo
    var toPx = function (X, Y) { var x = nx + ((X + minX) / k - nx) / shrink, y = ny + ((Y + minY) / k - ny) / shrink; return [x * ppi, Hpx - y * ppi]; };
    return { entities: all, outline: outline, holes: holes, width: maxX - minX, height: maxY - minY, toPx: toPx,
      counts: { lines: all.filter(function (e) { return e.type === 'line'; }).length, arcs: all.filter(function (e) { return e.type === 'arc'; }).length, circles: all.filter(function (e) { return e.type === 'circle'; }).length } };
  }

  /* ---------------- export ---------------- */
  function f5(x) { return (Math.abs(x) < 5e-6 ? 0 : x).toFixed(5); }
  function toDXF(ents) {
    var o = ['0', 'SECTION', '2', 'HEADER', '9', '$ACADVER', '1', 'AC1009', '9', '$INSUNITS', '70', '1', '9', '$MEASUREMENT', '70', '0', '0', 'ENDSEC',
      '0', 'SECTION', '2', 'TABLES', '0', 'TABLE', '2', 'LAYER', '70', '1', '0', 'LAYER', '2', 'PROFILE', '70', '0', '62', '7', '6', 'CONTINUOUS', '0', 'ENDTAB', '0', 'ENDSEC',
      '0', 'SECTION', '2', 'ENTITIES'];
    ents.forEach(function (e) {
      if (e.type === 'line') o.push('0', 'LINE', '8', 'PROFILE', '10', f5(e.a[0]), '20', f5(e.a[1]), '30', '0', '11', f5(e.b[0]), '21', f5(e.b[1]), '31', '0');
      else if (e.type === 'circle') o.push('0', 'CIRCLE', '8', 'PROFILE', '10', f5(e.cx), '20', f5(e.cy), '30', '0', '40', f5(e.r));
      else if (e.type === 'arc') {
        var s = Math.atan2(e.p0[1] - e.cy, e.p0[0] - e.cx) * 180 / Math.PI, t = Math.atan2(e.p2[1] - e.cy, e.p2[0] - e.cx) * 180 / Math.PI;
        if (!e.ccw) { var tmp = s; s = t; t = tmp; }
        s = (s + 360) % 360; t = (t + 360) % 360;
        o.push('0', 'ARC', '8', 'PROFILE', '10', f5(e.cx), '20', f5(e.cy), '30', '0', '40', f5(e.r), '50', s.toFixed(4), '51', t.toFixed(4));
      }
    });
    o.push('0', 'ENDSEC', '0', 'EOF');
    return o.join('\r\n') + '\r\n';
  }
  function entPath(e, X, Y) {
    if (e.type === 'line') return 'M' + X(e.a[0]) + ' ' + Y(e.a[1]) + 'L' + X(e.b[0]) + ' ' + Y(e.b[1]);
    if (e.type === 'circle') return 'M' + X(e.cx - e.r) + ' ' + Y(e.cy) + 'a' + e.r * X.s + ' ' + e.r * X.s + ' 0 1 0 ' + 2 * e.r * X.s + ' 0a' + e.r * X.s + ' ' + e.r * X.s + ' 0 1 0 ' + (-2 * e.r * X.s) + ' 0';
    var a0 = Math.atan2(e.p0[1] - e.cy, e.p0[0] - e.cx), a2 = Math.atan2(e.p2[1] - e.cy, e.p2[0] - e.cx), sw = a2 - a0;
    if (e.ccw && sw < 0) sw += 2 * Math.PI; if (!e.ccw && sw > 0) sw -= 2 * Math.PI;
    var large = Math.abs(sw) > Math.PI ? 1 : 0, sweepFlag = e.ccw ? 0 : 1;   // SVG y is flipped
    return 'M' + X(e.p0[0]) + ' ' + Y(e.p0[1]) + 'A' + e.r * X.s + ' ' + e.r * X.s + ' 0 ' + large + ' ' + sweepFlag + ' ' + X(e.p2[0]) + ' ' + Y(e.p2[1]);
  }
  function toSVG(prof) {
    var m = 0.1, W = prof.width + 2 * m, H = prof.height + 2 * m;
    var X = function (x) { return (x + m).toFixed(4); }; X.s = 1; var Y = function (y) { return (H - y - m).toFixed(4); };
    var d = prof.entities.map(function (e) { return entPath(e, X, Y); }).join('');
    return '<?xml version="1.0" encoding="UTF-8"?>\n<svg xmlns="http://www.w3.org/2000/svg" width="' + W.toFixed(4) + 'in" height="' + H.toFixed(4) + 'in" viewBox="0 0 ' + W.toFixed(4) + ' ' + H.toFixed(4) + '">' +
      '<path d="' + d + '" fill="none" stroke="#000" stroke-width="0.01"/></svg>\n';
  }

  var api = { grayFromRGBA: grayFromRGBA, detectPaper: detectPaper, refineCorners: refineCorners, homography: homography, applyH: applyH,
    rectify: rectify, segment: segment, traceContours: traceContours, buildProfile: buildProfile, toDXF: toDXF, toSVG: toSVG, entPath: entPath,
    fitCircle: fitCircle, snapDia: snapDia, orderCorners: orderCorners };
  root.ScanCore = api;
  if (typeof module !== 'undefined' && module.exports) module.exports = api;
})(typeof self !== 'undefined' ? self : this);
