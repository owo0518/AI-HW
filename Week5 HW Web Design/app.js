'use strict';
/* ================= gates：閘定義、尺寸、接腳 ================= */
const GATES = ['AND', 'OR', 'NOT', 'NAND', 'NOR', 'XOR', 'XNOR'];
const IO = ['INPUT', 'OUTPUT', 'CLOCK'];
const ni = c => c.type === 'CHIP' ? c.pi.length : ({ INPUT: 0, CLOCK: 0, OUTPUT: 1, NOT: 1 }[c.type] ?? 2);
const no = c => c.type === 'CHIP' ? c.po.length : c.type === 'OUTPUT' ? 0 : 1;
const isGate = c => GATES.includes(c.type);
const size = c => c.type === 'CHIP' ? { w: 100, h: 40 * Math.max(c.pi.length, c.po.length, 1) } : isGate(c) ? { w: 80, h: 60 } : { w: 60, h: 40 };
const snapG = n => Math.round(n / 10) * 10;
function ev(t, [x, y]) {
  x ??= null; y ??= null;
  const inv = r => r == null ? null : 1 - r;
  switch (t) {
    case 'BUF': return x;
    case 'NOT': return inv(x);
    case 'AND': return x === 0 || y === 0 ? 0 : x == null || y == null ? null : 1;
    case 'NAND': return inv(ev('AND', [x, y]));
    case 'OR': return x === 1 || y === 1 ? 1 : x == null || y == null ? null : 0;
    case 'NOR': return inv(ev('OR', [x, y]));
    case 'XOR': return x == null || y == null ? null : x ^ y;
    case 'XNOR': return inv(ev('XOR', [x, y]));
  }
}
/* ================= circuit：資料模型與接腳座標 ================= */
const fresh = () => ({ comps: [], wires: [], nid: 1, cnt: {}, defs: {}, dn: 1, st: {} });
let S = fresh();
const byId = id => S.comps.find(c => c.id === id);
function pinPos(c, out, i) {
  if (c.type === 'CHIP') return { x: c.x + (out ? 100 : 0), y: c.y + 20 + 40 * i };
  if (isGate(c)) return out ? { x: c.x + 80, y: c.y + 30 } : { x: c.x, y: c.y + (ni(c) === 1 ? 30 : 20 + 20 * i) };
  return { x: c.x + (out ? 60 : 0), y: c.y + 20 };
}
/* ================= simulator：展開、時序模擬、振盪偵測 ================= */
let sim = { v: {}, osc: new Set(), loop: false, unconn: 0, err: '' };
function flat(comps, wires, pre, d, ext, ins, N) {
  if (d > 8) throw Error('封裝展開超過 8 層');
  const by = {}; comps.forEach(c => by[c.id] = c);
  const okey = (c, p) => c.type === 'CHIP' ? pre + c.id + '/' + S.defs[c.d].outs[p] : pre + c.id;
  const src = (c, p) => { const w = wires.find(w => w.to.c === c.id && w.to.p === p); return w && by[w.from.c] ? okey(by[w.from.c], w.from.p) : null; };
  for (const c of comps) {
    if (c.type === 'CHIP') {
      const df = S.defs[c.d]; if (!df) throw Error('找不到元件定義');
      const e = df.pi.map((_, i) => src(c, i));
      flat(df.comps, df.wires, pre + c.id + '/', d + 1, e, df.ins, N); continue;
    }
    let t = c.type, inp = [];
    if (t === 'INPUT' && ext) { t = 'BUF'; inp = [ext[ins.indexOf(c.id)] ?? null]; }
    else if (t === 'OUTPUT') { t = 'BUF'; inp = [src(c, 0)]; }
    else if (t === 'INPUT' || t === 'CLOCK') t = 'SRC';
    else for (let i = 0; i < ni(c); i++) inp.push(src(c, i));
    N.push({ k: pre + c.id, t, inp, c });
  }
}
const okeyTop = (c, p) => c.type === 'CHIP' ? c.id + '/' + S.defs[c.d].outs[p] : '' + c.id;
function simulate() {
  const N = [];
  try { flat(S.comps, S.wires, '', 0, null, null, N); } catch (e) { sim = { v: {}, osc: new Set(), loop: false, unconn: 0, err: e.message }; return; }
  const v = {}, idx = {}, fz = new Set();
  N.forEach(n => { idx[n.k] = n; v[n.k] = n.t === 'SRC' ? n.c.val : (S.st[n.k] ?? null); });
  const get = k => k == null ? null : (v[k] ?? null);
  const lim = N.length * 3 + 20;
  const pass = ch => {
    let any = false;
    for (const n of N) {
      if (n.t === 'SRC' || fz.has(n.k)) continue;
      const r = ev(n.t, n.inp.map(get));
      if (r !== v[n.k]) { v[n.k] = r; any = true; ch && ch.add(n.k); }
    }
    return any;
  };
  const settle = () => { for (let i = 0; i < lim; i++) if (!pass()) return true; return false; };
  const freezeChanged = () => { const ch = new Set(); for (let i = 0; i < 4; i++) pass(ch); ch.forEach(k => { fz.add(k); v[k] = null; }); };
  for (let t = 0; t < 6 && !settle(); t++) freezeChanged();
  // 迴路偵測：從節點沿輸入往上游能回到自己
  const cyc = new Set();
  for (const n of N) {
    const seen = new Set(), st = [n.k]; let hit = false;
    while (st.length && !hit) for (const s of idx[st.pop()].inp) {
      if (s == null || !idx[s]) continue;
      if (s === n.k) { hit = true; break; }
      if (!seen.has(s)) { seen.add(s); st.push(s); }
    }
    if (hit) cyc.add(n.k);
  }
  // 迴路內仍未定義者：以 0 試探是否會振盪（只用於偵測，不改記憶）
  const nul = [...cyc].filter(k => v[k] == null && !fz.has(k));
  if (nul.length) {
    const save = { ...v }; nul.forEach(k => v[k] = 0);
    if (!settle()) freezeChanged();
    Object.assign(v, save); fz.forEach(k => v[k] = null); settle();
  }
  const st = {}; let un = 0;
  N.forEach(n => { if (n.t !== 'SRC') st[n.k] = v[n.k] ?? null; un += n.inp.filter(s => s == null).length; });
  S.st = st;
  sim = { v, osc: new Set([...fz].map(k => +k.split('/')[0])), loop: cyc.size > 0, unconn: un, err: '' };
}
const outVal = (c, p) => sim.v[okeyTop(c, p)] ?? null;
function inVal(c, i) {
  const w = S.wires.find(w => w.to.c === c.id && w.to.p === i), f = w && byId(w.from.c);
  return f ? outVal(f, w.from.p) : null;
}
/* ================= undo / redo ================= */
let U = [], R = [];
const snap = () => { U.push(JSON.stringify(S)); if (U.length > 100) U.shift(); R = []; };
function undo() { if (!U.length) return; R.push(JSON.stringify(S)); S = JSON.parse(U.pop()); sel.clear(); selW = null; update(); }
function redo() { if (!R.length) return; U.push(JSON.stringify(S)); S = JSON.parse(R.pop()); sel.clear(); selW = null; update(); }
/* ================= renderer ================= */
const $ = s => document.querySelector(s), svg = $('#cv'), layer = $('#layer'), world = $('#world');
let view = { x: 40, y: 40, k: 1 }, sel = new Set(), selW = null, mode = 'sel', running = false, pending = null, ghost = null, band = null, hot = null;
const vc = v => v == null ? 'x' : v;
const vt = v => v == null ? '?' : v;
function wirePts(w) {
  const a = byId(w.from.c), b = byId(w.to.c); if (!a || !b) return [];
  const p = pinPos(a, true, w.from.p), q = pinPos(b, false, w.to.p);
  if (q.x >= p.x + 20) { const m = snapG((p.x + q.x) / 2); return [p, { x: m, y: p.y }, { x: m, y: q.y }, q]; }
  const my = snapG((p.y + q.y) / 2) + (Math.abs(p.y - q.y) < 10 ? 50 : 0);
  return [p, { x: p.x + 20, y: p.y }, { x: p.x + 20, y: my }, { x: q.x - 20, y: my }, { x: q.x - 20, y: q.y }, q];
}
const pstr = ps => ps.map(p => p.x + ',' + p.y).join(' ');
let raf = 0;
const redraw = () => { if (!raf) raf = requestAnimationFrame(() => { raf = 0; draw(); }); };
function draw() {
  world.setAttribute('transform', `translate(${view.x} ${view.y}) scale(${view.k})`);
  $('#zlbl').textContent = Math.round(view.k * 100) + '%';
  let h = '';
  for (const w of S.wires) {
    const a = byId(w.from.c); if (!a) continue;
    h += `<polyline class="w v${vc(outVal(a, w.from.p))}${selW === w.id ? ' sel' : ''}" points="${pstr(wirePts(w))}"/>`;
  }
  for (const c of S.comps) {
    const s = size(c), cls = 'body' + (sel.has(c.id) ? ' sel' : '') + (sim.osc.has(c.id) ? ' osc' : '');
    h += `<g><rect class="${cls}" x="${c.x}" y="${c.y}" width="${s.w}" height="${s.h}" rx="${isGate(c) ? 6 : 4}"/>`;
    const cx = c.x + s.w / 2, cy = c.y + s.h / 2;
    if (c.type === 'INPUT' || c.type === 'CLOCK') {
      h += `<text class="big t${vc(c.val)}" x="${cx}" y="${cy + 2}">${c.val}</text><text x="${cx}" y="${c.y - 8}">${esc(c.name)}${c.type === 'CLOCK' ? ' ' + c.hz + 'Hz' : ''}</text>`;
    } else if (c.type === 'OUTPUT') {
      const v = inVal(c, 0); h += `<text class="big t${vc(v)}" x="${cx}" y="${cy + 2}">${vt(v)}</text><text x="${cx}" y="${c.y - 8}">${esc(c.name)}</text>`;
    } else if (c.type === 'CHIP') {
      h += `<text x="${cx}" y="${c.y - 8}">${esc(c.name)}</text>`;
      c.pi.forEach((n, i) => h += `<text x="${c.x + 8}" y="${c.y + 20 + 40 * i - 14}" style="text-anchor:start;font-size:10px">${esc(n)}</text>`);
      c.po.forEach((n, i) => h += `<text x="${c.x + 92}" y="${c.y + 20 + 40 * i - 14}" style="text-anchor:end;font-size:10px">${esc(n)}</text>`);
    } else {
      h += `<text x="${cx - 4}" y="${cy}">${c.type}</text>`;
      if (['NOT', 'NAND', 'NOR', 'XNOR'].includes(c.type)) h += `<circle class="pin" style="stroke:var(--ink)" cx="${c.x + 84}" cy="${c.y + 30}" r="4"/>`;
    }
    for (let i = 0; i < ni(c); i++) h += pinSvg(c, false, i, inVal(c, i));
    for (let i = 0; i < no(c); i++) h += pinSvg(c, true, i, outVal(c, i));
    h += '</g>';
  }
  if (ghost) h += `<polyline class="w v0" style="stroke-dasharray:4 4" points="${ghost.a.x},${ghost.a.y} ${ghost.b.x},${ghost.b.y}"/>`;
  if (band) h += `<rect class="box" x="${Math.min(band.a.x, band.b.x)}" y="${Math.min(band.a.y, band.b.y)}" width="${Math.abs(band.a.x - band.b.x)}" height="${Math.abs(band.a.y - band.b.y)}"/>`;
  layer.innerHTML = h;
}
const esc = s => String(s ?? '').replace(/[&<>"]/g, m => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' }[m]));
function pinSvg(c, out, i, val) {
  const p = pinPos(c, out, i), isHot = hot && hot.c === c.id && hot.p === i && hot.out === out;
  const o = out ? -12 : 12, dy = isGate(c) || c.type === 'CHIP' ? -9 : 14;
  const stroke = `var(--v${vc(val)})`.replace('vx', 'vx');
  return `<circle class="pin${isHot ? ' hot' : ''}" cx="${p.x}" cy="${p.y}" r="${isHot ? 8 : 4}" style="stroke:${stroke}"/><text class="pv t${vc(val)}" x="${p.x + (c.type === 'INPUT' || c.type === 'CLOCK' ? 0 : o)}" y="${p.y + dy}">${vt(val)}</text>`;
}
/* ================= 狀態面板、屬性列、提示 ================= */
function panel() {
  const ins = S.comps.filter(c => c.type === 'INPUT' || c.type === 'CLOCK'), outs = S.comps.filter(c => c.type === 'OUTPUT');
  let msg = sim.err ? ['err', sim.err] : sim.osc.size ? ['err', '電路振盪，無法穩定；相關輸出視為未定義'] : sim.loop ? ['', '以時序電路模擬'] : ['', '組合電路'];
  if (sim.unconn && !sim.err) msg[1] += `（${sim.unconn} 個輸入接腳未連接）`;
  $('#stat').innerHTML = `<div class="msg ${msg[0]}">${esc(msg[1])}</div><h4>輸入</h4>` +
    (ins.map(c => `<div class="row"><span class="val v${vc(c.val)}">${c.val}</span><button data-tg="${c.id}">${esc(c.name)}</button></div>`).join('') || '<small>尚無輸入</small>') +
    `<h4>輸出</h4>` + (outs.map(c => { const v = inVal(c, 0); return `<div class="row"><span class="val v${vc(v)}">${vt(v)}</span>${esc(c.name)}</div>`; }).join('') || '<small>尚無輸出</small>') +
    `<h4>導線顏色</h4><div class="row"><span class="val v1">1</span>邏輯 1（綠、實線）</div><div class="row"><span class="val v0">0</span>邏輯 0（藍）</div><div class="row"><span class="val vx">?</span>未定義／錯誤（紅、虛線）</div>`;
}
function props() {
  const p = $('#props'), c = sel.size === 1 ? byId([...sel][0]) : null;
  if (!c || !(IO.includes(c.type) || c.type === 'CHIP')) { p.hidden = true; return; }
  p.hidden = false;
  if (c.type === 'CHIP') { p.innerHTML = `${esc(c.name)} <button id="unp">展開封裝</button>`; $('#unp').onclick = () => unpack(c.id); return; }
  p.innerHTML = `名稱 <input id="pn" maxlength="8" value="${esc(c.name)}">` + (c.type === 'CLOCK' ? ` 頻率 <input id="ph" type="number" min="0.1" max="20" step="0.1" value="${c.hz}"> Hz <small id="pi">${Math.round(500 / c.hz)} ms</small>` : '');
  $('#pn').onchange = e => { snap(); c.name = e.target.value.slice(0, 8) || c.name; update(); };
  if (c.type === 'CLOCK') $('#ph').onchange = e => { snap(); c.hz = Math.min(20, Math.max(.1, +e.target.value || 1)); update(); };
}
let tt = 0;
function toast(m) { const t = $('#toast'); t.textContent = m; t.classList.add('show'); clearTimeout(tt); tt = setTimeout(() => t.classList.remove('show'), 2600); }
function palette() {
  const ds = Object.entries(S.defs); $('#custom').hidden = !ds.length;
  $('#customBtns').innerHTML = ds.map(([id, d]) => `<button data-chip="${id}">${esc(d.name)}</button>`).join('');
}
let lastDefs = '';
function update() {
  simulate(); draw(); panel(); props();
  const k = JSON.stringify(Object.entries(S.defs).map(([i, d]) => [i, d.name])); if (k !== lastDefs) { lastDefs = k; palette(); }
}
/* ================= editor：新增、命中測試、指標事件 ================= */
function addComp(type, d) {
  snap();
  const r = svg.getBoundingClientRect(), c = { id: S.nid++, type, rot: 0 };
  const sz = d ? { w: 100, h: 40 * Math.max(S.defs[d].pi.length, S.defs[d].po.length, 1) } : size({ type });
  c.x = snapG((r.width / 2 - view.x) / view.k - sz.w / 2 + (S.comps.length % 5) * 20); c.y = snapG((r.height / 2 - view.y) / view.k - sz.h / 2 + (S.comps.length % 5) * 20);
  if (type === 'CHIP') { const df = S.defs[d]; Object.assign(c, { d, name: df.name, pi: df.pi.slice(), po: df.po.slice() }); }
  if (IO.includes(type)) { const n = S.cnt[type] = (S.cnt[type] || 0) + 1; c.name = ({ INPUT: 'IN', OUTPUT: 'OUT', CLOCK: 'CLK' })[type] + n; }
  if (type === 'INPUT' || type === 'CLOCK') c.val = 0;
  if (type === 'CLOCK') c.hz = 1;
  S.comps.push(c); sel = new Set([c.id]); selW = null; update();
}
const world2 = e => { const r = svg.getBoundingClientRect(); return { x: (e.clientX - r.left - view.x) / view.k, y: (e.clientY - r.top - view.y) / view.k }; };
function hitPin(p, rad, want) {
  let best = null, bd = rad;
  for (const c of S.comps) for (const out of [false, true]) {
    if (want !== undefined && out !== want) continue;
    for (let i = 0; i < (out ? no(c) : ni(c)); i++) {
      const q = pinPos(c, out, i), d = Math.hypot(q.x - p.x, q.y - p.y);
      if (d < bd) { bd = d; best = { c: c.id, p: i, out }; }
    }
  }
  return best;
}
function hit(p) {
  const pin = hitPin(p, (mode === 'wire' ? 18 : 10) / view.k); if (pin) return { pin };
  for (let i = S.comps.length - 1; i >= 0; i--) { const c = S.comps[i], s = size(c); if (p.x >= c.x && p.x <= c.x + s.w && p.y >= c.y && p.y <= c.y + s.h) return { c: c.id }; }
  for (const w of S.wires) { const ps = wirePts(w); for (let i = 0; i < ps.length - 1; i++) if (dSeg(p, ps[i], ps[i + 1]) < 6 / view.k) return { w: w.id }; }
  return {};
}
function dSeg(p, a, b) {
  const dx = b.x - a.x, dy = b.y - a.y, l = dx * dx + dy * dy || 1, t = Math.max(0, Math.min(1, ((p.x - a.x) * dx + (p.y - a.y) * dy) / l));
  return Math.hypot(p.x - a.x - t * dx, p.y - a.y - t * dy);
}
function connect(a, b) {
  if (a.out === b.out) return toast(a.out ? '不能連接兩個輸出接腳' : '不能連接兩個輸入接腳');
  if (a.c === b.c) return toast('不能連到自己的接腳');
  const f = a.out ? a : b, t = a.out ? b : a;
  if (S.wires.some(w => w.to.c === t.c && w.to.p === t.p)) return toast('這個輸入接腳已經有來源');
  snap(); S.wires.push({ id: S.nid++, from: { c: f.c, p: f.p }, to: { c: t.c, p: t.p } }); update();
}
const pointers = new Map(); let drag = null, wiring = null, pinch = null;
svg.addEventListener('pointerdown', e => {
  svg.setPointerCapture(e.pointerId); pointers.set(e.pointerId, { x: e.clientX, y: e.clientY });
  if (pointers.size === 2) { const [a, b] = [...pointers.values()]; pinch = { d: Math.hypot(a.x - b.x, a.y - b.y), k: view.k }; drag = wiring = null; return; }
  const p = world2(e), h = hit(p);
  if (pending) {
    if (h.pin) { const a = pending; pending = null; hot = null; connect(a, h.pin); return; }
    pending = null; hot = null;
  }
  if (h.pin) { wiring = { a: h.pin, moved: false }; return; }
  if (h.c) {
    const c = byId(h.c);
    if (mode === 'wire') { drag = { t: 'pan', sx: e.clientX, sy: e.clientY, vx: view.x, vy: view.y, moved: false, click: c }; return; }
    if (!sel.has(c.id)) sel = new Set([c.id]); selW = null;
    drag = { t: 'move', s: p, o: new Map([...sel].map(i => [i, { x: byId(i).x, y: byId(i).y }])), moved: false, click: c }; update(); return;
  }
  if (h.w) { selW = h.w; sel.clear(); update(); return; }
  if (mode === 'box' || e.shiftKey) { drag = { t: 'box' }; band = { a: p, b: p }; return; }
  drag = { t: 'pan', sx: e.clientX, sy: e.clientY, vx: view.x, vy: view.y, moved: false };
});
svg.addEventListener('pointermove', e => {
  if (pointers.has(e.pointerId)) pointers.set(e.pointerId, { x: e.clientX, y: e.clientY });
  if (pinch && pointers.size === 2) { const [a, b] = [...pointers.values()]; zoomAt((a.x + b.x) / 2, (a.y + b.y) / 2, pinch.k * Math.hypot(a.x - b.x, a.y - b.y) / pinch.d); return; }
  const p = world2(e);
  if (wiring) {
    wiring.moved = true; const a = byId(wiring.a.c);
    ghost = { a: pinPos(a, wiring.a.out, wiring.a.p), b: p };
    hot = hitPin(p, 30 / view.k, !wiring.a.out); if (hot && hot.c === wiring.a.c) hot = null;
    return redraw();
  }
  if (!drag) return;
  if (drag.t === 'move') {
    const dx = snapG(p.x - drag.s.x), dy = snapG(p.y - drag.s.y);
    if (!drag.moved && (dx || dy)) { drag.moved = true; snap(); }
    if (drag.moved) drag.o.forEach((o, id) => { const c = byId(id); c.x = o.x + dx; c.y = o.y + dy; });
  } else if (drag.t === 'pan') {
    const dx = e.clientX - drag.sx, dy = e.clientY - drag.sy;
    if (Math.abs(dx) + Math.abs(dy) > 3) drag.moved = true;
    view.x = drag.vx + dx; view.y = drag.vy + dy;
  } else if (drag.t === 'box') band.b = p;
  redraw();
});
function endPointer(e) {
  pointers.delete(e.pointerId); if (pointers.size < 2) pinch = null;
  if (wiring) {
    const w = wiring; wiring = null; ghost = null; const p = world2(e);
    if (w.moved) { const t = hitPin(p, 30 / view.k, !w.a.out); hot = null; if (t && t.c !== w.a.c) connect(w.a, t); else { const any = hitPin(p, 12 / view.k); if (any) connect(w.a, any); } }
    else { pending = w.a; hot = w.a; toast('再點選另一個接腳完成連線（Esc 取消）'); }
    return redraw();
  }
  if (!drag) return;
  const d = drag; drag = null;
  if (d.t === 'move' && !d.moved) {
    if (d.click.type === 'INPUT' || d.click.type === 'CLOCK') { snap(); d.click.val ^= 1; update(); }
  } else if (d.t === 'pan' && !d.moved) {
    if (d.click && (d.click.type === 'INPUT' || d.click.type === 'CLOCK')) { snap(); d.click.val ^= 1; }
    else { sel.clear(); selW = null; }
  } else if (d.t === 'box') {
    const r = { x1: Math.min(band.a.x, band.b.x), x2: Math.max(band.a.x, band.b.x), y1: Math.min(band.a.y, band.b.y), y2: Math.max(band.a.y, band.b.y) };
    sel = new Set(S.comps.filter(c => { const s = size(c); return c.x <= r.x2 && c.x + s.w >= r.x1 && c.y <= r.y2 && c.y + s.h >= r.y1; }).map(c => c.id)); band = null;
  }
  update();
}
svg.addEventListener('pointerup', endPointer); svg.addEventListener('pointercancel', endPointer);
svg.addEventListener('wheel', e => { e.preventDefault(); zoomAt(e.clientX, e.clientY, view.k * (e.deltaY < 0 ? 1.1 : 1 / 1.1)); }, { passive: false });
function zoomAt(cx, cy, k) {
  k = Math.min(3, Math.max(.2, k)); const r = svg.getBoundingClientRect(), x = cx - r.left, y = cy - r.top;
  view.x = x - (x - view.x) * k / view.k; view.y = y - (y - view.y) * k / view.k; view.k = k; redraw();
}
function fit() {
  if (!S.comps.length) { view = { x: 40, y: 40, k: 1 }; return redraw(); }
  const r = svg.getBoundingClientRect(); let x1 = 1e9, y1 = 1e9, x2 = -1e9, y2 = -1e9;
  S.comps.forEach(c => { const s = size(c); x1 = Math.min(x1, c.x); y1 = Math.min(y1, c.y - 20); x2 = Math.max(x2, c.x + s.w); y2 = Math.max(y2, c.y + s.h); });
  const k = Math.min(1.5, Math.max(.2, Math.min((r.width - 80) / (x2 - x1), (r.height - 80) / (y2 - y1))));
  view = { k, x: (r.width - (x2 - x1) * k) / 2 - x1 * k, y: (r.height - (y2 - y1) * k) / 2 - y1 * k }; redraw();
}
function delSel() {
  if (selW != null) { snap(); S.wires = S.wires.filter(w => w.id !== selW); selW = null; return update(); }
  if (!sel.size) return; snap();
  S.comps = S.comps.filter(c => !sel.has(c.id)); S.wires = S.wires.filter(w => !sel.has(w.from.c) && !sel.has(w.to.c)); sel.clear(); update();
}
/* ================= clock：時脈 ================= */
const lastT = {};
setInterval(() => {
  if (!running) return; const now = performance.now(); let ch = false;
  for (const c of S.comps) if (c.type === 'CLOCK') { lastT[c.id] ??= now; if (now - lastT[c.id] >= 500 / c.hz) { c.val ^= 1; lastT[c.id] = now; ch = true; } }
  if (ch) update();
}, 20);
function step() {
  if (!S.comps.some(c => c.type === 'CLOCK')) return toast('畫布上沒有 CLOCK');
  snap(); S.comps.forEach(c => c.type === 'CLOCK' && (c.val ^= 1)); update();
}
/* ================= pack：封裝與展開 ================= */
const sortPos = (a, b) => a.y - b.y || a.x - b.x;
function pack() {
  const cs = S.comps.filter(c => sel.has(c.id));
  if (!cs.length) return toast('請先用「框選」選取要封裝的電路');
  if (cs.some(c => c.type === 'CLOCK')) return toast('封裝內不能含 CLOCK，請改由外部接進 INPUT');
  const ins = cs.filter(c => c.type === 'INPUT').sort(sortPos), outs = cs.filter(c => c.type === 'OUTPUT').sort(sortPos);
  if (!ins.length || !outs.length) return toast('選取範圍必須至少含一個 INPUT 與一個 OUTPUT');
  const name = (prompt('元件名稱（最多 8 個字）', '') || '').trim().slice(0, 8); if (!name) return;
  snap();
  const did = 'd' + S.dn++, ids = new Set(cs.map(c => c.id)), cid = S.nid++;
  const mx = Math.min(...cs.map(c => c.x)), my = Math.min(...cs.map(c => c.y));
  S.defs[did] = { name, comps: JSON.parse(JSON.stringify(cs)), wires: S.wires.filter(w => ids.has(w.from.c) && ids.has(w.to.c)).map(w => JSON.parse(JSON.stringify(w))), ins: ins.map(c => c.id), outs: outs.map(c => c.id), pi: ins.map(c => c.name), po: outs.map(c => c.name) };
  for (const c of cs) for (const k of Object.keys(S.st)) if (k === '' + c.id || k.startsWith(c.id + '/')) { S.st[cid + '/' + k] = S.st[k]; delete S.st[k]; }
  S.comps = S.comps.filter(c => !ids.has(c.id)); S.wires = S.wires.filter(w => !ids.has(w.from.c) && !ids.has(w.to.c));
  const df = S.defs[did];
  S.comps.push({ id: cid, type: 'CHIP', x: mx, y: my, rot: 0, d: did, name, pi: df.pi.slice(), po: df.po.slice() });
  sel = new Set([cid]); update(); toast('已封裝為「' + name + '」');
}
function unpack(id) {
  const c = byId(id), df = c && S.defs[c.d]; if (!df) return; snap();
  const mx = Math.min(...df.comps.map(k => k.x)), my = Math.min(...df.comps.map(k => k.y)), map = {};
  const nc = JSON.parse(JSON.stringify(df.comps)).map(k => { map[k.id] = S.nid++; return { ...k, id: map[k.id], x: k.x - mx + c.x, y: k.y - my + c.y }; });
  const nw = JSON.parse(JSON.stringify(df.wires)).map(w => ({ id: S.nid++, from: { c: map[w.from.c], p: w.from.p }, to: { c: map[w.to.c], p: w.to.p } }));
  for (const k of Object.keys(S.st)) if (k.startsWith(id + '/')) { S.st[k.slice(('' + id).length + 1).replace(/^(\d+)/, m => map[m] ?? m)] = S.st[k]; delete S.st[k]; }
  const ext = S.wires.filter(w => w.to.c === id), extO = S.wires.filter(w => w.from.c === id), drop = new Set(), add = [];
  df.ins.forEach((iid, i) => { const e = ext.find(w => w.to.p === i); if (!e) return; drop.add(map[iid]);
    nw.filter(w => w.from.c === map[iid]).forEach(w => add.push({ id: S.nid++, from: { ...e.from }, to: { ...w.to } })); });
  df.outs.forEach((oid, j) => { const es = extO.filter(w => w.from.p === j); if (!es.length) return; const inner = nw.find(w => w.to.c === map[oid]); if (!inner) return; drop.add(map[oid]);
    es.forEach(w => add.push({ id: S.nid++, from: { ...inner.from }, to: { ...w.to } })); });
  S.comps = S.comps.filter(k => k.id !== id).concat(nc.filter(k => !drop.has(k.id)));
  S.wires = S.wires.filter(w => w.from.c !== id && w.to.c !== id).concat(nw.filter(w => !drop.has(w.from.c) && !drop.has(w.to.c)), add);
  sel = new Set(nc.filter(k => !drop.has(k.id)).map(k => k.id)); update();
}
/* ================= library：元件庫管理 ================= */
const usedDef = d => S.comps.some(c => c.d === d) || Object.values(S.defs).some(x => x.comps.some(c => c.d === d));
const dlg = $('#dlg');
function libDlg() {
  const es = Object.entries(S.defs);
  dlg.innerHTML = `<h3>元件庫</h3>` + (es.map(([id, d]) => `<div class="row"><b style="flex:1">${esc(d.name)}</b><button data-r="${id}">重新命名</button><button data-x="${id}">匯出</button><button data-d="${id}" ${usedDef(id) ? 'disabled title="使用中"' : ''}>刪除</button></div>`).join('') || '<p>尚無自訂元件。框選電路後按「封裝」建立。</p>') +
    `<div class="acts"><button data-x="*">匯出全部</button><button data-close>關閉</button></div>`;
  dlg.showModal();
}
dlg.addEventListener('click', e => {
  const t = e.target; if (!(t instanceof HTMLElement)) return;
  if (t.dataset.close !== undefined) dlg.close();
  if (t.dataset.r) { const n = (prompt('新名稱（最多 8 個字）', S.defs[t.dataset.r].name) || '').trim().slice(0, 8); if (n) { snap(); S.defs[t.dataset.r].name = n; S.comps.forEach(c => c.d === t.dataset.r && (c.name = n)); Object.values(S.defs).forEach(d => d.comps.forEach(c => c.d === t.dataset.r && (c.name = n))); update(); libDlg(); } }
  if (t.dataset.d && !usedDef(t.dataset.d)) { snap(); delete S.defs[t.dataset.d]; update(); libDlg(); }
  if (t.dataset.x) { const ids = t.dataset.x === '*' ? Object.keys(S.defs) : [t.dataset.x]; if (ids.length) download(t.dataset.x === '*' ? 'components-all.json' : 'component-' + S.defs[ids[0]].name + '.json', JSON.stringify(compFile(ids))); }
  if (t.dataset.dl) download('logic-project.json', $('#ta').value);
  if (t.dataset.imp) importText($('#ta').value);
  if (t.dataset.pick) $('#file').click();
});
/* ================= io：匯出匯入與驗證 ================= */
const projFile = () => ({ format: 'logic-sim', version: 1, kind: 'project', circuit: { comps: S.comps, wires: S.wires, nid: S.nid, cnt: S.cnt, defs: S.defs, dn: S.dn } });
function compFile(ids) {
  const need = new Set(), walk = i => { if (need.has(i)) return; need.add(i); S.defs[i].comps.forEach(c => c.d && walk(c.d)); }; ids.forEach(walk);
  const defs = {}; need.forEach(i => defs[i] = S.defs[i]); return { format: 'logic-sim', version: 1, kind: 'components', defs };
}
function download(name, text) {
  const a = document.createElement('a'); a.href = URL.createObjectURL(new Blob([text], { type: 'application/json' })); a.download = name; document.body.appendChild(a); a.click(); a.remove();
}
function projectDlg() {
  dlg.innerHTML = `<h3>專案匯出／匯入</h3><p>下載檔案，或複製下方文字；也可貼上 JSON 後匯入。</p><textarea id="ta" aria-label="專案 JSON">${esc(JSON.stringify(projFile()))}</textarea><input id="file" type="file" accept=".json,application/json" multiple hidden><div class="acts"><button data-dl="1">下載 logic-project.json</button><button data-pick="1">選擇檔案匯入</button><button data-imp="1">匯入文字框內容</button><button data-close>關閉</button></div>`;
  dlg.showModal(); $('#file').onchange = async e => { for (const f of e.target.files) { if (f.size > 5 * 1048576) { toast('檔案超過 5 MB：' + f.name); continue; } await importText(await f.text()); } };
}
function cleanSet(comps, wires, defs) {
  const ids = new Set(), by = {};
  if (!Array.isArray(comps) || !Array.isArray(wires)) throw Error('缺少元件或導線陣列');
  const out = comps.map(c => {
    if (!c || ![...GATES, ...IO, 'CHIP'].includes(c.type)) throw Error('未知的元件類型：' + c?.type);
    if (!Number.isInteger(c.id) || ids.has(c.id) || !Number.isFinite(c.x) || !Number.isFinite(c.y)) throw Error('元件識別碼重複或座標不合法');
    ids.add(c.id); const n = { id: c.id, type: c.type, x: snapG(c.x), y: snapG(c.y), rot: 0 };
    if (c.type === 'INPUT' || c.type === 'CLOCK') n.val = c.val ? 1 : 0;
    if (IO.includes(c.type)) n.name = String(c.name ?? '').slice(0, 8);
    if (c.type === 'CLOCK') n.hz = Math.min(20, Math.max(.1, +c.hz || 1));
    if (c.type === 'CHIP') { const df = defs[c.d]; if (!df) throw Error('找不到自訂元件定義：' + c.d); Object.assign(n, { d: c.d, name: String(c.name ?? df.name).slice(0, 8), pi: df.pi.slice(), po: df.po.slice() }); }
    return by[n.id] = n;
  }), used = new Set(), ws = [];
  for (const w of wires) {
    const a = by[w?.from?.c], b = by[w?.to?.c]; if (!a || !b) throw Error('導線端點不存在');
    if (!(w.from.p >= 0 && w.from.p < no(a)) || !(w.to.p >= 0 && w.to.p < ni(b))) throw Error('接腳編號超出範圍');
    const k = b.id + ':' + w.to.p; if (used.has(k)) continue; used.add(k);
    ws.push({ id: Number.isInteger(w.id) ? w.id : 1e6 + ws.length, from: { c: a.id, p: w.from.p }, to: { c: b.id, p: w.to.p } });
  }
  return { comps: out, wires: ws };
}
function mapDefs(raw, dn) {
  const map = {}, nd = {}; Object.keys(raw).forEach(k => map[k] = 'd' + dn++);
  for (const [k, d] of Object.entries(raw)) {
    if (!d || !Array.isArray(d.pi) || !Array.isArray(d.po) || !Array.isArray(d.ins) || !Array.isArray(d.outs)) throw Error('元件定義格式錯誤');
    nd[map[k]] = { ...d, name: String(d.name || '元件').slice(0, 8), pi: d.pi.map(x => String(x).slice(0, 8)), po: d.po.map(x => String(x).slice(0, 8)), comps: (d.comps || []).map(c => c.type === 'CHIP' ? { ...c, d: map[c.d] } : c) };
  }
  for (const d of Object.values(nd)) {
    const cl = cleanSet(d.comps, d.wires || [], nd); d.comps = cl.comps; d.wires = cl.wires;
    const t = (ids, ty) => ids.every(i => d.comps.find(c => c.id === i)?.type === ty);
    if (d.ins.length !== d.pi.length || d.outs.length !== d.po.length || !t(d.ins, 'INPUT') || !t(d.outs, 'OUTPUT')) throw Error('元件「' + d.name + '」的接腳數與內部 INPUT／OUTPUT 不一致');
  }
  return { map, nd, dn };
}
async function importText(txt) {
  try {
    const j = JSON.parse(txt); if (j?.format !== 'logic-sim') throw Error('不是本程式的檔案格式');
    if (j.kind === 'project') {
      const c = j.circuit || {}, r = mapDefs(c.defs || {}, 1);
      const cl = cleanSet((c.comps || []).map(k => k.type === 'CHIP' ? { ...k, d: r.map[k.d] } : k), c.wires || [], r.nd);
      snap(); const mx = Math.max(0, ...cl.comps.map(k => k.id), ...cl.wires.map(w => w.id));
      S = { ...fresh(), ...cl, nid: mx + 1, cnt: c.cnt && typeof c.cnt === 'object' ? c.cnt : {}, defs: r.nd, dn: r.dn };
    } else if (j.kind === 'components') {
      const r = mapDefs(j.defs || {}, S.dn); snap(); Object.assign(S.defs, r.nd); S.dn = r.dn;
    } else throw Error('未知的 kind');
    sel.clear(); update(); fit(); toast('匯入完成');
  } catch (e) { toast('匯入失敗：' + e.message); }
}
/* ================= 範例與工具列 ================= */
function demo() {
  snap(); S = { ...fresh(), defs: S.defs, dn: S.dn };
  const add = (type, x, y, o = {}) => { const c = { id: S.nid++, type, x, y, rot: 0, ...o }; S.comps.push(c); return c.id; };
  const s = add('INPUT', 40, 60, { name: 'S', val: 0 }), r = add('INPUT', 40, 200, { name: 'R', val: 0 });
  const n1 = add('NOR', 240, 40), n2 = add('NOR', 240, 180), q = add('OUTPUT', 420, 60, { name: 'Q' }), qb = add('OUTPUT', 420, 200, { name: 'QB' });
  const w = (a, ap, b, bp) => S.wires.push({ id: S.nid++, from: { c: a, p: ap }, to: { c: b, p: bp } });
  w(r, 0, n1, 0); w(n2, 0, n1, 1); w(s, 0, n2, 1); w(n1, 0, n2, 0); w(n1, 0, q, 0); w(n2, 0, qb, 0);
  S.cnt = { INPUT: 2, OUTPUT: 2 }; sel.clear(); update(); fit(); toast('SR 栓鎖：先把 S 切成 1，再切回 0，Q 會保持 1');
}
const acts = {
  sel: () => setMode('sel'), wire: () => setMode('wire'), box: () => setMode('box'), pack, project: projectDlg, lib: libDlg, del: delSel, undo, redo,
  zout: () => zoomAt(innerWidth / 2, innerHeight / 2, view.k / 1.2), zin: () => zoomAt(innerWidth / 2, innerHeight / 2, view.k * 1.2), zlbl: fit, step,
  run: () => { if (!running && !S.comps.some(c => c.type === 'CLOCK')) return toast('畫布上沒有 CLOCK'); running = !running; $('#runBtn').textContent = running ? '暫停' : '執行'; },
  reset: () => { snap(); S.st = {}; update(); },
  demo, clear: () => { if (!S.comps.length || confirm('清空整個畫布？（可復原）')) { snap(); S = { ...fresh(), defs: S.defs, dn: S.dn }; sel.clear(); update(); } },
  status: () => $('#stat').classList.toggle('open'),
};
function setMode(m) { mode = m; pending = null; hot = null; ['sel', 'wire', 'box'].forEach(k => $(`[data-act=${k}]`).classList.toggle('on', k === m)); redraw(); }
document.addEventListener('click', e => {
  const t = e.target.closest('button'); if (!t) return;
  if (t.dataset.act) acts[t.dataset.act]();
  if (t.dataset.add) addComp(t.dataset.add);
  if (t.dataset.chip) addComp('CHIP', t.dataset.chip);
  if (t.dataset.tg) { const c = byId(+t.dataset.tg); snap(); c.val ^= 1; update(); }
});
document.addEventListener('keydown', e => {
  if (e.target.matches('input,textarea')) return;
  const m = e.ctrlKey || e.metaKey;
  if (e.key === 'Delete' || e.key === 'Backspace') { e.preventDefault(); delSel(); }
  else if (m && e.key.toLowerCase() === 'z') { e.preventDefault(); e.shiftKey ? redo() : undo(); }
  else if (m && e.key.toLowerCase() === 'y') { e.preventDefault(); redo(); }
  else if (e.key === 'Escape') { pending = null; hot = null; wiring = null; ghost = null; sel.clear(); selW = null; update(); }
  else if (e.key === '+' || e.key === '=') acts.zin(); else if (e.key === '-') acts.zout();
});
addEventListener('resize', redraw);
update();
