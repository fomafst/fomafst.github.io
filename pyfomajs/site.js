import { FST } from './pyfoma.js';

// ---------------------------
// UI helpers
// ---------------------------

const $ = (sel) => document.querySelector(sel);

// Be liberal about element IDs so we work with both our simple UI
// and the reference WebGraphviz UI.
const editor = $('#editor') || $('#code') || $('#graphviz_data');
const codeHlEl = $('#codeHL');
const consoleEl = $('#console') || $('#output') || $('#graphviz_errors');
const graphEl = $('#graph') || $('#graphviz_svg_div');
const runBtn = $('#runBtn') || $('#generate_btn');
const clearBtn = $('#clearBtn');
const fitBtn = $('#fitBtn');
const saveBtn = $('#saveBtn');
const demoSelect = $('#demoSelect');
const wrapToggle = $('#wrapToggle');

// Metadata about the most recently produced text output (for saving).
let lastOutputMeta = null; // { filename: string, kind: 'text'|'foma' }

// Enable pan/zoom on the graph panel.
installGraphPanZoom();

// Lightweight syntax coloring in the left editor: comments in green.
// We keep the textarea for caret/selection and draw highlighted text in an overlay <pre>.
let refreshEditorHighlight = () => {};
if (codeHlEl && editor && editor.tagName === 'TEXTAREA') {
  refreshEditorHighlight = installEditorOverlayHighlight(editor, codeHlEl);
}

// Optional: wrap long editor lines.
// Default is OFF (horizontal scrolling), which keeps the overlay perfectly aligned.
if (wrapToggle && editor && editor.tagName === 'TEXTAREA' && codeHlEl) {
  const applyWrapSetting = () => {
    const on = !!wrapToggle.checked;
    if (on) {
      editor.setAttribute('wrap', 'soft');
      editor.style.whiteSpace = 'pre-wrap';
      editor.style.overflowX = 'hidden';
      editor.style.overflowWrap = 'anywhere';
      editor.style.wordBreak = 'break-word';
      codeHlEl.style.whiteSpace = 'pre-wrap';
      codeHlEl.style.overflowWrap = 'anywhere';
      codeHlEl.style.wordBreak = 'break-word';
    } else {
      editor.setAttribute('wrap', 'off');
      editor.style.whiteSpace = 'pre';
      editor.style.overflowX = 'auto';
      editor.style.overflowWrap = 'normal';
      editor.style.wordBreak = 'normal';
      codeHlEl.style.whiteSpace = 'pre';
      codeHlEl.style.overflowWrap = 'normal';
      codeHlEl.style.wordBreak = 'normal';
    }
    // Re-render + resync scroll after style change.
    refreshEditorHighlight();
  };
  wrapToggle.addEventListener('change', applyWrapSetting);
  applyWrapSetting();
}

function appendConsole(text, kind = 'out') {
  if (!consoleEl) {
    // Fallback if the host page doesn't provide a console area.
    // eslint-disable-next-line no-console
    console[kind === 'err' ? 'error' : 'log'](text);
    return;
  }
  const pre = document.createElement('pre');
  pre.className = kind;
  pre.textContent = text;
  consoleEl.appendChild(pre);
  consoleEl.scrollTop = consoleEl.scrollHeight;
}

function clearOutput() {
  if (!consoleEl) return;
  consoleEl.innerHTML = '';
  lastOutputMeta = null;
}

function getConsoleText() {
  if (!consoleEl) return '';
  // Join <pre> blocks with a blank line between them.
  const pres = Array.from(consoleEl.querySelectorAll('pre'));
  if (pres.length === 0) return '';
  return pres.map((p) => p.textContent ?? '').join('\n\n');
}

function saveTextAsFile(text, filename) {
  const safe = (filename && String(filename).trim()) ? String(filename).trim() : 'output.txt';
  const blob = new Blob([text], { type: 'text/plain;charset=utf-8' });
  const url = URL.createObjectURL(blob);
  const a = document.createElement('a');
  a.href = url;
  a.download = safe;
  document.body.appendChild(a);
  a.click();
  a.remove();
  // Revoke asynchronously to avoid breaking download in some browsers.
  setTimeout(() => URL.revokeObjectURL(url), 1000);
}

function setGraphPlaceholder(msg) {
  graphEl.innerHTML = `<div class="placeholder">${msg}</div>`;
}

// ---------------------------
// Editor overlay highlighting (comments only)
// ---------------------------

function escapeHtml(s) {
  return String(s)
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;')
    .replace(/"/g, '&quot;')
    .replace(/'/g, '&#39;');
}

function highlightProgram(text) {
  // Color full-line comments (// ...) in green. Everything else is default.
  const lines = String(text ?? '').replace(/\r\n?/g, '\n').split('\n');
  const out = [];
  for (const line of lines) {
    const trimmed = line.trimStart();
    if (trimmed.startsWith('//')) {
      out.push(`<span class="comment">${escapeHtml(line)}</span>`);
    } else {
      out.push(escapeHtml(line));
    }
  }
  return out.join('\n');
}

function installEditorOverlayHighlight(textarea, pre) {
  const syncScroll = () => {
    // Keep overlay aligned with textarea scroll position.
    // Using scrollTop/scrollLeft (instead of large CSS transforms) avoids
    // occasional rendering glitches where content can appear to disappear
    // after scrolling large documents.
    pre.scrollTop = textarea.scrollTop;
    pre.scrollLeft = textarea.scrollLeft;
  };

  const refresh = () => {
    pre.innerHTML = highlightProgram(textarea.value);
    syncScroll();
  };

  textarea.addEventListener('input', refresh);
  textarea.addEventListener('scroll', syncScroll);
  // Keep the overlay up to date on resize too.
  window.addEventListener('resize', syncScroll);

  // Initial render.
  refresh();
  return refresh;
}

// Viz.js glue.
// There are two common APIs:
//   (A) Old WebGraphviz demo:  Viz(dot, 'svg')  (sync)
//   (B) Viz.js 2.x:            new Viz().renderSVGElement(dot) (async)
let viz = null;
let vizCallMode = null; // 'string' or 'object' for legacy function API

// ---------------------------
// Graph pan/zoom
// ---------------------------

// We pan/zoom by manipulating the SVG's viewBox.
// This keeps the rendering crisp (vector) even at high zoom.
let vbState = {
  svg: null,
  content: null, // original content viewBox from Graphviz
  orig: null,   // {x,y,w,h}
  cur: null,    // {x,y,w,h}
  dragging: false,
  startX: 0,
  startY: 0,
  startVB: null,
};

function clamp(x, lo, hi) { return Math.max(lo, Math.min(hi, x)); }

function getGraphSvg() {
  return graphEl ? graphEl.querySelector('svg') : null;
}

function parseViewBox(vb) {
  const parts = String(vb ?? '').trim().split(/\s+/).map(Number);
  if (parts.length === 4 && parts.every((n) => Number.isFinite(n))) {
    return { x: parts[0], y: parts[1], w: parts[2], h: parts[3] };
  }
  return null;
}

function ensureSvgViewBox(svg) {
  // Most Graphviz SVGs include a viewBox already. If not, derive it.
  let vb = parseViewBox(svg.getAttribute('viewBox'));
  if (vb) return vb;

  const wAttr = svg.getAttribute('width') || '';
  const hAttr = svg.getAttribute('height') || '';
  const w = parseFloat(wAttr) || svg.clientWidth || 100;
  const h = parseFloat(hAttr) || svg.clientHeight || 100;
  vb = { x: 0, y: 0, w, h };
  svg.setAttribute('viewBox', `${vb.x} ${vb.y} ${vb.w} ${vb.h}`);
  return vb;
}

function setSvgViewBox(svg, vb) {
  svg.setAttribute('viewBox', `${vb.x} ${vb.y} ${vb.w} ${vb.h}`);
}

function initSvgPanZoom() {
  const svg = getGraphSvg();
  if (!svg) return;
  vbState.svg = svg;
  // The SVG may have had its viewBox adjusted for display; preserve the original
  // content viewBox so we can "Fit graph" later.
  vbState.content = svg.__contentVB || ensureSvgViewBox(svg);
  vbState.orig = parseViewBox(svg.getAttribute('viewBox')) || { ...vbState.content };
  vbState.cur = { ...vbState.orig };
  vbState.dragging = false;
}

function resetSvgPanZoom() {
  const svg = getGraphSvg();
  if (!svg) return;
  if (!vbState.orig) initSvgPanZoom();
  vbState.cur = { ...vbState.orig };
  setSvgViewBox(svg, vbState.cur);
}

function installGraphPanZoom() {
  if (!graphEl) return;
  // Avoid installing twice.
  if (graphEl.__pzInstalled) return;
  graphEl.__pzInstalled = true;

  // Initialize once (and again after each render).
  initSvgPanZoom();

  // Wheel/trackpad: two-finger scroll zooms.
  graphEl.addEventListener('wheel', (e) => {
    const svg = getGraphSvg();
    if (!svg) return;
    if (!vbState.cur) initSvgPanZoom();
    e.preventDefault();

    const rect = svg.getBoundingClientRect();
    const px = (e.clientX - rect.left) / rect.width;
    const py = (e.clientY - rect.top) / rect.height;
    const nx = clamp(px, 0, 1);
    const ny = clamp(py, 0, 1);

    // Smooth zoom: deltaY>0 zoom out, deltaY<0 zoom in.
    const zoom = Math.exp(e.deltaY * 0.001);
    const vb = vbState.cur;
    const newW = clamp(vb.w * zoom, 10, vbState.orig.w * 200);
    const newH = clamp(vb.h * zoom, 10, vbState.orig.h * 200);
    const cx = vb.x + nx * vb.w;
    const cy = vb.y + ny * vb.h;
    vbState.cur = {
      x: cx - nx * newW,
      y: cy - ny * newH,
      w: newW,
      h: newH,
    };
    setSvgViewBox(svg, vbState.cur);
  }, { passive: false });

  // Drag to pan.
  graphEl.addEventListener('pointerdown', (e) => {
    const svg = getGraphSvg();
    if (!svg) return;
    if (!vbState.cur) initSvgPanZoom();
    vbState.dragging = true;
    vbState.startX = e.clientX;
    vbState.startY = e.clientY;
    vbState.startVB = { ...vbState.cur };
    graphEl.setPointerCapture(e.pointerId);
  });
  graphEl.addEventListener('pointermove', (e) => {
    if (!vbState.dragging) return;
    const svg = getGraphSvg();
    if (!svg) return;
    const rect = svg.getBoundingClientRect();
    const dx = (e.clientX - vbState.startX) / rect.width * vbState.startVB.w;
    const dy = (e.clientY - vbState.startY) / rect.height * vbState.startVB.h;
    vbState.cur = {
      x: vbState.startVB.x - dx,
      y: vbState.startVB.y - dy,
      w: vbState.startVB.w,
      h: vbState.startVB.h,
    };
    setSvgViewBox(svg, vbState.cur);
  });
  const endPan = (e) => {
    if (!vbState.dragging) return;
    vbState.dragging = false;
    try { graphEl.releasePointerCapture(e.pointerId); } catch (_) { /* ignore */ }
  };
  graphEl.addEventListener('pointerup', endPan);
  graphEl.addEventListener('pointercancel', endPan);

  // Double-click to reset zoom.
  graphEl.addEventListener('dblclick', () => {
    resetSvgPanZoom();
  });
}

function ensureVizPresent() {
  if (typeof window.Viz !== 'function') {
    throw new Error('Viz.js not found. Make sure viz.js and full.render.js are loaded.');
  }
}

// Some Viz.js (full.render.js) builds ship with a small initial WASM heap.
// For larger DFAs, Graphviz can exceed that and abort. We start with a larger
// heap and grow on demand by recreating Viz.
let vizMemBytes = 64 * 1024 * 1024;
const VIZ_MEM_MAX = 512 * 1024 * 1024;

function makeViz(memBytes) {
  // Viz.js 2.x expects Module/render from full.render.js.
  if (window.Module && window.render) {
    const baseModule = window.Module;
    const baseRender = window.render;

    // Emscripten "MODULARIZE" module factory typically accepts an overrides object.
    // We wrap it so we can request a larger initial heap.
    let ModuleFactory = baseModule;
    if (typeof baseModule === 'function') {
      ModuleFactory = () => {
        const overrides = {
          // Older emscripten: TOTAL_MEMORY; newer: INITIAL_MEMORY.
          TOTAL_MEMORY: memBytes,
          INITIAL_MEMORY: memBytes,
          // If the module was compiled with growth enabled, this helps; otherwise ignored.
          ALLOW_MEMORY_GROWTH: 1,
        };
        try { return baseModule(overrides); } catch (_e1) {
          try { return baseModule({ TOTAL_MEMORY: memBytes }); } catch (_e2) {
            return baseModule();
          }
        }
      };
    }
    return new window.Viz({ Module: ModuleFactory, render: baseRender });
  }
  return new window.Viz();
}

function isMemoryAbort(err) {
  const s = String(err?.message ?? err);
  return s.includes('Cannot enlarge memory arrays') || s.includes('abort("Cannot enlarge memory arrays') || s.includes('Cannot enlarge memory');
}

async function renderDot(dot) {
  ensureVizPresent();

  // Viz.js 2.x API (class with promise-based rendering)
  if (window.Viz.prototype && typeof window.Viz.prototype.renderSVGElement === 'function') {
    if (!viz) viz = makeViz(vizMemBytes);
    const renderOnce = async () => {
      // Viz.js defaults to the 'dot' engine for digraphs; passing an engine option
      // can trigger quirks in some builds, so keep it simple.
      const svgEl = await viz.renderSVGElement(dot);
      graphEl.innerHTML = '';
      graphEl.appendChild(svgEl);
      resetGraphSize();
      initSvgPanZoom();
    };
    try {
      await renderOnce();
      return;
    } catch (e) {
      // Viz instances become unusable after a failed render.
      // If we hit the WASM heap limit, bump heap and retry.
      if (isMemoryAbort(e) && vizMemBytes < VIZ_MEM_MAX) {
        vizMemBytes = Math.min(VIZ_MEM_MAX, vizMemBytes * 2);
      }
      viz = makeViz(vizMemBytes);
      try { await renderOnce(); return; } catch (e2) { throw (e2 && (e2.message || String(e2)).length) ? e2 : e; }
    }
  }

  // Old WebGraphviz API (function call). Different builds accept different signatures.
  // IMPORTANT: Some legacy builds are *silently* unhappy if you pass an options
  // object (they coerce it to a string). That can lead to strange artifacts
  // like an extra orphan node labeled "svg". So we probe once and then stick
  // to the working calling convention.
  let svg = null;

  const looksLikeSvg = (x) => String(x ?? '').includes('<svg');

  const callString = () => window.Viz(dot, 'svg');
  const callObject = () => window.Viz(dot, { format: 'svg', engine: 'dot' });

  if (vizCallMode === 'string') {
    svg = callString();
  } else if (vizCallMode === 'object') {
    svg = callObject();
  } else {
    // First render: try the WebGraphviz signature first.
    try {
      svg = callString();
      if (looksLikeSvg(svg)) vizCallMode = 'string';
      else throw new Error('Unexpected Viz output (string mode)');
    } catch (_e1) {
      svg = callObject();
      vizCallMode = 'object';
    }
  }

  // If a legacy build returned non-SVG output despite not throwing, retry.
  if (!looksLikeSvg(svg)) {
    try {
      svg = callString();
      if (looksLikeSvg(svg)) vizCallMode = 'string';
    } catch (_e2) {
      svg = callObject();
      vizCallMode = 'object';
    }
  }
  graphEl.innerHTML = sanitizeVizSvg(svg);
  resetGraphSize();
  initSvgPanZoom();
}

function sanitizeVizSvg(svgText) {
  // Some Viz builds may prepend error text before the <svg ...> root.
  const s = String(svgText ?? '');
  const i = s.indexOf('<svg');
  if (i < 0) return s;
  const j = s.lastIndexOf('</svg>');
  if (j < 0) return s.slice(i);
  return s.slice(i, j + '</svg>'.length);
}

function resetGraphSize() {
  // Default behavior:
  //  - make the SVG viewport fill the output panel (so wheel-zoom feels natural)
  //  - avoid *upscaling* small graphs by expanding the viewBox when needed
  const svg = graphEl.querySelector('svg');
  if (!svg) return;

  // Remember the original viewBox from Graphviz (content bounds).
  const contentVB = parseViewBox(svg.getAttribute('viewBox')) || ensureSvgViewBox(svg);
  svg.__contentVB = contentVB;

  // Fill the panel.
  svg.removeAttribute('width');
  svg.removeAttribute('height');
  svg.style.width = '100%';
  svg.style.height = '100%';
  svg.setAttribute('preserveAspectRatio', 'xMidYMid meet');

  // If fitting would enlarge the content, expand the viewBox so it renders at ~1x.
  const pw = Math.max(1, graphEl.clientWidth || 1);
  const ph = Math.max(1, graphEl.clientHeight || 1);
  const fitScale = Math.min(pw / contentVB.w, ph / contentVB.h);
  if (fitScale > 1.05) {
    const newW = contentVB.w * fitScale;
    const newH = contentVB.h * fitScale;
    const vb = {
      x: contentVB.x - (newW - contentVB.w) / 2,
      y: contentVB.y - (newH - contentVB.h) / 2,
      w: newW,
      h: newH,
    };
    setSvgViewBox(svg, vb);
  } else {
    setSvgViewBox(svg, contentVB);
  }
}

function fitGraph() {
  const svg = graphEl.querySelector('svg');
  if (!svg) return;
  // Fit the *content* viewBox to the panel (this may upscale small graphs; it's explicit).
  svg.style.width = '100%';
  svg.style.height = '100%';
  svg.setAttribute('preserveAspectRatio', 'xMidYMid meet');
  const contentVB = svg.__contentVB || parseViewBox(svg.getAttribute('viewBox')) || ensureSvgViewBox(svg);
  svg.__contentVB = contentVB;
  setSvgViewBox(svg, contentVB);
  initSvgPanZoom();
  resetSvgPanZoom();
}

// ---------------------------
// Mini language
// ---------------------------

// Environment of defined FSTs. Keys are WITHOUT the leading '$'.
const env = Object.create(null);

function fstHasWeights(fst) {
  // Detect non-zero weights in transitions or finals.
  for (const s of fst.states) {
    if (fst.finalstates.has(s) && s.finalweight && s.finalweight !== 0.0) return true;
    for (const [, t] of s.allTransitions()) {
      if (t.weight && t.weight !== 0.0) return true;
    }
  }
  return false;
}

function formatWeight(w) {
  const num = Number(w);
  if (!Number.isFinite(num)) return String(w);
  let s = num.toFixed(6).replace(/0+$/, '').replace(/\.$/, '');
  if (!s.includes('.')) s += '.0';
  if (s === '-0.0') s = '0.0';
  return s;
}

function isBlank(line) {
  return !line || !line.trim();
}

function stripComments(line) {
  // Simple: remove everything after // unless inside single quotes.
  let out = '';
  let inQuote = false;
  for (let i = 0; i < line.length; i++) {
    const ch = line[i];
    if (ch === "'" && line[i - 1] !== '\\') inQuote = !inQuote;
    if (!inQuote && ch === '/' && line[i + 1] === '/') break;
    out += ch;
  }
  return out;
}

function parseRhsRegex(rhs) {
  const s = rhs.trim();
  if (s.startsWith('/') && s.endsWith('/') && s.length >= 2) {
    return s.slice(1, -1);
  }
  return s;
}

function parseArgExpr(arg) {
  const s = arg.trim();
  if (!s) throw new Error('Missing argument.');
  if (s.startsWith('$')) {
    const name = s.slice(1);
    if (!(name in env)) throw new Error(`Undefined variable: $${name}`);
    return env[name];
  }
  if (s.startsWith('/') && s.endsWith('/') && s.length >= 2) {
    return FST.re(s.slice(1, -1), env);
  }
  // raw regex without slashes
  return FST.re(s, env);
}

function parseArgsList(argStr) {
  // For now, split by commas not in quotes.
  const args = [];
  let cur = '';
  let inQuote = false;
  for (let i = 0; i < argStr.length; i++) {
    const ch = argStr[i];
    if (ch === "'" && argStr[i - 1] !== '\\') inQuote = !inQuote;
    if (!inQuote && ch === ',') {
      args.push(cur.trim());
      cur = '';
    } else {
      cur += ch;
    }
  }
  if (cur.trim()) args.push(cur.trim());
  return args;
}

function parseWordArg(s) {
  // Accept either bare tokens or quoted strings.
  const t = String(s).trim();
  if ((t.startsWith('"') && t.endsWith('"')) || (t.startsWith("'") && t.endsWith("'"))) {
    return t.slice(1, -1);
  }
  return t;
}

async function execLine(line) {
  const raw = stripComments(line).trim();
  if (isBlank(raw)) return;

  // Assignment: $name = /regex/ (or = regex)
  const assign = raw.match(/^\$(\w+)\s*=\s*(.+)$/);
  if (assign) {
    const name = assign[1];
    const rhs = assign[2];
    const re = parseRhsRegex(rhs);
    env[name] = FST.re(re, env);
    return;
  }

  // Standalone regex: /.../ (compile + view)
  if (raw.startsWith('/') && raw.endsWith('/')) {
    const fst = FST.re(raw.slice(1, -1), env);
    env['x'] = fst;
    const showW = fstHasWeights(fst);
    await renderDot(fst.toDot({ showWeights: showW }));
    return;
  }

  // Function calls
  const call = raw.match(/^(\w+)\s*\((.*)\)\s*$/);
  if (call) {
    const fn = call[1];
    const argStr = call[2];
    const parts = parseArgsList(argStr);

    if (fn === 'view') {
      if (parts.length !== 1) throw new Error('view(...) takes exactly 1 argument.');
      const fst = parseArgExpr(parts[0]);
      const showW = fstHasWeights(fst);
      await renderDot(fst.toDot({ showWeights: showW }));
      return;
    }

    if (fn === 'att') {
      if (parts.length !== 1) throw new Error('att(...) takes exactly 1 argument.');
      const fst = parseArgExpr(parts[0]);
      appendConsole(fst.toATT(), 'out');
      return;
    }

    if (fn === 'tofoma') {
      if (parts.length < 1 || parts.length > 2) throw new Error('tofoma(fst[, name]) takes 1 or 2 arguments.');
      const fstArgRaw = String(parts[0] ?? '').trim();
      const fst = parseArgExpr(fstArgRaw);
      const name = (parts.length === 2) ? parseWordArg(parts[1]) : null;
      const dumped = fst.toFomastring(name);
      appendConsole(dumped, 'out');

      // Suggest a filename for "Save output...".
      // Preference: explicit name argument; else $var name; else generic.
      let base = null;
      if (name && String(name).trim()) {
        base = String(name).trim();
      } else if (fstArgRaw.startsWith('$')) {
        base = fstArgRaw.slice(1).trim();
      }
      if (!base) base = 'export';
      // Keep it filesystem-friendly.
      base = base.replace(/[^A-Za-z0-9._-]+/g, '_');
      lastOutputMeta = { filename: `${base}.foma`, kind: 'foma' };
      return;
    }

    if (fn === 'generate' | fn == 'dn') {
      if (parts.length < 2) throw new Error('generate(fst, word1, word2, ...) requires at least 2 arguments.');
      const fst = parseArgExpr(parts[0]);
      const weighted = fstHasWeights(fst);
      const words = parts.slice(1).map(parseWordArg);
      const outLines = [];
      for (const w of words) {
        const outs = Array.from(fst.generate(w, { weights: weighted }));
        if (outs.length === 0) {
          outLines.push(`${w}: (no outputs)`);
          continue;
        }
        for (const o of outs) {
          if (!weighted) {
            outLines.push(`${w}: ${o}`);
          } else {
            const [str, cost] = o;
            outLines.push(`${w}: ${str} <${formatWeight(cost)}>`);
          }
        }
      }
      appendConsole(outLines.join('\n'), 'out');
      return;
    }

    if (fn === 'analyze' | fn === 'up') {
      if (parts.length < 2) throw new Error('analyze(fst, word1, word2, ...) requires at least 2 arguments.');
      const fst = parseArgExpr(parts[0]);
      const weighted = fstHasWeights(fst);
      const words = parts.slice(1).map(parseWordArg);
      const outLines = [];
      for (const w of words) {
        const outs = Array.from(fst.analyze(w, { weights: weighted }));
        if (outs.length === 0) {
          outLines.push(`${w}: (no analyses)`);
          continue;
        }
        for (const o of outs) {
          if (!weighted) {
            outLines.push(`${w}: ${o}`);
          } else {
            const [str, cost] = o;
            outLines.push(`${w}: ${str} <${formatWeight(cost)}>`);
          }
        }
      }
      appendConsole(outLines.join('\n'), 'out');
      return;
    }

    throw new Error(`Unknown function: ${fn}`);
  }

  throw new Error(`Unrecognized statement: ${raw}`);
}

async function runAll() {
  if (!editor) {
    appendConsole('No editor textarea found in the page (expected #editor or #code).', 'err');
    return;
  }
  clearOutput();
  const lines = editor.value.split(/\r?\n/);
  for (let i = 0; i < lines.length; i++) {
    const line = lines[i];
    try {
      // eslint-disable-next-line no-await-in-loop
      await execLine(line);
    } catch (e) {
      const msg = (e && typeof e === 'object' && 'message' in e && e.message) ? e.message : String(e);
      appendConsole(`Line ${i + 1}: ${msg}`, 'err');
      break;
    }
  }
}

if (runBtn) runBtn.addEventListener('click', () => { runAll(); });
if (clearBtn) {
  clearBtn.addEventListener('click', () => {
    clearOutput();
    setGraphPlaceholder('(Cleared.)');
  });
}
if (fitBtn) fitBtn.addEventListener('click', fitGraph);

if (saveBtn) {
  saveBtn.addEventListener('click', () => {
    const text = getConsoleText();
    if (!text.trim()) {
      appendConsole('Nothing to save (output is empty).', 'err');
      return;
    }
    const filename = lastOutputMeta?.filename || 'output.txt';
    saveTextAsFile(text, filename);
  });
}

// Run on Ctrl/Cmd+Enter
if (editor) editor.addEventListener('keydown', (e) => {
  if ((e.ctrlKey || e.metaKey) && e.key === 'Enter') {
    e.preventDefault();
    runAll();
  }
});

// ---------------------------
// Demos
// ---------------------------

const DEMOS = [
  {
    name: 'Introduction',
    code: `// Introduction
    
// This demoes a pyfoma port to js (see https://github.com/mhulden/pyfoma)
// You can compile regexes into finite-state automata and transducers,
// run them, visualize them, and export to .foma files

// Everything runs in the browser

// Writing /regex/ by itself compiles a regex and immediately displays it

// You can also write regexes and store the FSTs into variables. Example:

// $consonant = [a-z] - [aeiou]

// ... and then re-use the definition in new regexes:

// $syllable = $consonant+ [aeiou] $consonant+

// view($variable) displays the FST

// generate($variable, string, string, ...) passes strings to the FST
// analyze($variable, string, string, ...) does the inverse calculation
// dn() and up() are shorter synonyms for both

// Example:

$myfst = $^rewrite(a:b / c _ d)
view($myfst)
generate($myfst, cadcab, cab)
analyze($myfst, cbd) 

// You can save an FST in .foma format for
// import into foma or pyfoma, with 
// tofoma($myfst)
// and then "Save output..."

// See pull-down menu above for more examples

`,
  },
  {
    name: 'Formalism',
    code: `// Formalism

// We follow the pyfoma regex-formalism, see pyfoma for more details.

// Basic operations:
// concatenation, union(|), intersection(&), subtraction(-), negation(~)
// Kleene star(*), Kleene plus(+), cross-product(:), composition(@)
// weight specification <#.#>
// character classes, e.g. [a-zA-Z]
// Variables use the sigil $, e.g. /$foo+ - $bar*/

// Built-in functions:

// $^determinize($foo)        # determinizes an FSM
// $^ignore($foo)             # The language x, ignoring intervening y's
// $^input($foo)              # extract input projection
// $^output($foo)             # extract output projection
// $^invert($foo)             # inverts a transducer
// $^minimize($foo)           # minimizes an FSM
// $^restrict($a / $b _ $c)   # context restriction compilation
// $^reverse($foo)            # reverses an FSM
// $^rewrite($a:$b)           # basic rewrite rule compilation
// $^rewrite($a:$b / $c _ $d, $e _ $f) # basic rewrite rule with contexts
// $^rewrite($a:?$b / $c _ $d)         # optional rewrite rule
// $^rewrite('':x $a '':y / $c _ $d) # 'markup ' rule ( wrap x, y around a)
// $^rewrite($a:$b / $c _ $d, leftmost = True)  # leftmost rewrite
// $^rewrite($a:$b / $c _ $d, longest = True)   # longest rewrite
// $^rewrite($a:$b / $c _ $d, shortest = True)  # shortest rewrite

// The compiler always returns minimized and determinized (as DFA) FSTs.
// Weighted FSMs/FSTs use the tropical semiring.

// Example regex where the minimal DFA grows exponentially with n

/[ab]* a [ab]{5}/

`,
  },
  {
    name: 'English morphological analyzer',
    code: `// English morphological analyzer (toy)

// A few base nouns
$noun = cat|dog|church|mouse|fox|fly

// We add either [N][Pl] -> +s or [N][Sg] -> '' (nothing) after the noun
$lexicon = $noun (('[N]' '[Pl]'):('+' s) | ('[N]' '[Sg]'):'')

// Define sibilants, the sounds after which we insert e when pluralizing
$sibilant = s|z|sh|ch|z|x

// Insert e between sibilants at morpheme boundary (fox+s > foxe+s)
$erule = $^rewrite('':e / $sibilant _ '+' s)

// y changes to ie at plural
$irule = $^rewrite(y:(ie) / _ '+' s)

// Remove morpheme boundaries after rules have applied
$cleanup = $^rewrite('+':'')

// Full grammar
$grammar = $lexicon @ $erule @ $irule @ $cleanup

// View FST and generate and analyze some words
view($grammar)
generate($grammar, cat[N][Pl], church[N][Pl])
analyze($grammar, dogs, flies)`,
  },
  {
    name: 'Syllabifier',
    code: `/// Toy syllabifier, showing syllabification
// with the "maximum onset" principle

// Define consonants and vowels (roughly)
$C = [a-z] - [aeiouy]
$V = [aeiouy]

// Define onsets and codas loosely
// They should be defined more precisely 
// for an accurate syllabifier

$onset = $C{,3}
$coda = $C{,5}
$syl = $onset $V $coda

// Use leftmost-shortest rewrite rule
// to insert "-" between syllables
$sbify = $^rewrite($syl '':'-' / _ $syl, leftmost = True, shortest = True)

view($sbify)

// Test
generate($sbify, abracadabra, creativity)


`,
  },
  {
    name: 'Rewrite rules with weights',
    code: `// Rewrite rules with weights

// Always delete xs at cost of 1.0
$rule1 = $^rewrite(x:y<1.0>)
generate($rule1, xxx)

// Optionally delete xs at cost of 1.0
$rule2 = $^rewrite(x:?y<1.0>)
generate($rule2, xxx)

// Optionally delete xs at cost of 1.0, but only at word edges
$rule3 = $^rewrite(x:?y<1.0> / # _ , _ #)
generate($rule3, xxx)

// Always delete xs at cost of 1.0, but only after a previous x
$rule4 = $^rewrite(x:y<1.0> / x _ )
generate($rule4, xxx)

view($rule4)
`,
  },
 {
    name: 'G2P for Brazilian Portuguese',
    code: `// G2P for Brazilian Portuguese

$V       = a|e|i|o|u|á|é|í|ó|ú|ã|õ|â|ê|ô|ü|à
$lhrule  = $^rewrite((lh):ʎ|(nh):ɲ)
$rrule1  = $^rewrite(r:ʁ / # _ )
$rrule2  = $^rewrite((rr):ʁ)
$srule3  = $^rewrite(z:s / _ #)
$srule2  = $^rewrite((ss):s | ç:s)
$srule1  = $^rewrite(s:z / $V _ $V)
$chrule  = $^rewrite((ch):ʃ)
$crule   = $^rewrite(c:s / _ (e|i))
$krule   = $^rewrite(c:k)
$erule   = $^rewrite(e:i|o:u / _ s? # , # p _ r)
$palat   = $^rewrite(t:(tʃ) | d:(dʒ) / _ i)
$grammar = $srule1 @ $lhrule @ $rrule1 @ $rrule2 @ $erule @ $srule2 @ $chrule @ $crule @ $krule @ $palat @ $srule3
view($grammar)

generate($grammar, antes, bicho, braço, braços, cada, cantar, caro, carro, casa, case, chato, diferentes, disse, filhos, gatinho, livro, luz, me, ninhos, parede, paredes, parte, partes, pedaço, peru, rápido, sabe, simpático, verdade, vermelho)

// How it works

// (Originally an exercise by Ken Beesley in the book "Finite State Morphology").

// * The following description is based on the rather conservative pronunciation of Portuguese in Porto Alegre, Rio Grande do Sul, Brazil. Because the orthography is even more conservative, the rules will roughly characterize the phonological changes that have occured in this one dialect since the orthography fossilized. 
// * The final transducer produced by our regular expression generates IPA pronunciations (using generate()) from input strings like the following, written in standard Brazilian Portuguese orthography. We will limit the input to lowercase words in this implementation.

// casa
// cimento
// me
// disse
// peruca
// simpático
// braço
// arvore


// * The surface level produced by the grammar will be written in IPA. Because we have limited our input words to lowercase letters, the six special characters needed will appear only in output strings, never at the input level.


// dʒ  palatalized d, similar to the phoneme spelled j in English "judge"
// tʃ  palatalized t, similar to the phoneme spelled ch in "church"
// ʃ   alveopalatal sibilant, like the phoneme spelled sh in English "ship"
// ʎ   phoneme spelled lh in Portuguese filho (or gli in Italian figlio)
// ɲ   phoneme spelled nh in Portuguese ninho (like the French gn in digne)
// ʁ   phoneme spelled rr inside words, single r at the beginning of words 


// * The mapping from orthography (input side) to pronunciation (output side) includes the following alternations:

//   - The orthographical (lexical-side) ç is always pronounced /s/; in other words, a ç on the upper side always corresponds to an s on the lower side. In these explanations, we follow the IPA convention of indicating phonemes, the lower-side symbols, between slashes. These slashes do not appear in the output strings.
  

// Input:  braço
// Output: brasu


//    - The orthographical ss is always pronounced /s/. In this and following illustrations, the input and output strings are lined up character pair by character pair, with the 0 (zero, also called epsilon, denoted '' in pyfoma) filling out the places where a lexical symbol maps to the empty string. These zeroes are for illustration only and do not actually appear in the surface language of our transducer.
   

// Input:  interesse
// Output: interes0i


//    - The orthographical c before e or i, or before accented versions of these vowel letters, is always pronounced /s/.
   

// Input:  cimento
// Output: simentu


//    - The orthographical digraph ch is pronounced /ʃ/.
   

// Input:  chato
// Output: ʃ0atu



//    - Elsewhere (i.e. not ch, and not ci or ce), orthographical c is always pronounced /k/.
   
 
// Input:  casa
// Output: kaza


//    - The orthographical digraph lh is realized as /ʎ/.

// Input:  filho
// Output: fiʎ0u


//    - The orthographical digraph nh is realized as /ɲ/.
   

// Input:  ninho
// Output: niɲ0u


// Remember that the zeros shown in these examples are for illustration only and do not appear in our real output strings.

//    - Elsewhere, h is silent and is simply realized as 0 (zero, the empty string).

// Input:  homem
// Output: 0omem


//    - The orthographical digraph rr is always realized as /ʁ/. Also, the single r at the beginning of a word is always realized as /ʁ/. Elsewhere, r:r, i.e. input r is realized as /r/.


// Input:  carro  rápido  caro  cantar  
// Output: kaʁ0u  ʁápidu  karu  kantar


//    - The unaccented e is pronounced /i/ at the end of a word, and when it appears in the context between p and r at the beginning of a word; e.g.
   

// Input:  peruca  case
// Output: piruka  kazi


//    - An unaccented e is also pronounced /i/ before an s at the end of a word. Elsewhere e:e.


// Input:  cases
// Output: kazis


// - An unaccented o is pronounced /u/ at the end of a word.
 

// Input:  braço  caso
// Output: brasu  kazu


// - An unaccented o is also pronounced /u/ before an s at the end of a word. Elsewhere o:o.
  

// Input:  braços
// Output: brasus


//    - A single s is pronounced /z/ when it appears between two vowels.
   

// Input:  camisa  case
// Output: kamiza  kazi


//    - Elsewhere s:s (but see above where (ss):s ).
   
//    - A word-final z is pronounced as /s/.
   

// Input:  vez
// Output: ves


//    - Elsewhere, z:z.

//    - A d is pronounced /dʒ/ when it appears before a surface phoneme /i/. (N.B. This change occurs in the environment of any surface /i/, no matter what that surface /i/ may have been at the input level.) Elsewhere d:d.
   

// Input:  d  i s s e   v e r d a d  e   p a r e d  e s
// Output: dʒ i s 0 i   v e r d a dʒ i   p a r e dʒ i s


//    - A t is pronounced /tʃ/ when it appears before a surface phoneme /i/. (N.B. This change occurs in the environment of any surface /i/, no matter what that surface /i/ may have been at the input level.) Elsewhere t:t.



// Input:  t  i o    p a r t  e s
// Output: tʃ i u    p a r tʃ i s


//    - The vowels are a, e, i, o, u, á, é, í, ó, ú, ã, õ, â, ê, ô, ü, à. All input symbols should map to themselves level by default.

`,
  },
 {
    name: 'The Soundex algorithm as an FST',
    code: `// The Soundex algorithm as an FST

// Here's a description of the algorithm in 4 steps (following Don Knuth in TAOCP vol. 3, p. 394):

// Retain the first letter of the name and drop all other occurrences of a, e, h, i, o, u, w, y.

// Replace consonants after the first letter with numbers, as follows:

//     b, f, p, v => 1
//     c, g, j, k, q, s, x, z => 2
//     d, t => 3
//     l => 4
//     m, n => 5
//     r => 6

// If two or more letters with the same number were adjacent in the original name (before step 1), or adjacent except for intervening h's and w's, omit all but the first.

// Convert to the form “letter, digit, digit, digit” by adding trailing zeros (if there are less than three digits), or by dropping rightmost digits (if there are more than three).

// Notice that Knuth's description really is such that step 3 is applied first, then step 1, step 2, and step 4. This is because step 3 references something existing "before step 1", i.e. information which applying step 1 first would destroy.

// Code

$s1 = [bfpv]
$s2 = [cgjkqsxz]
$s3 = [dt]
$s4 = l
$s5 = [mn]
$s6 = r

$step3 = $^rewrite($s1 ([hw]* $s1:'')* | $s2 ([hw]* $s2:'')* | $s3 ([hw]* $s3:'')* | $s4 ([hw]* $s4:'')* | $s5 ([hw]* $s5:'')* | $s6 ([hw]* $s6:'')*, longest = True, leftmost = True)

$step1 = . ([aehiouwy]:'' | [^aehiouwy])*
$step2 = . ($s1:1 | $s2:2 | $s3:3 | $s4:4 | $s5:5 | $s6:6)*
$step4 =  .* ((.:'')* | ('':0)*) @ .[0-9]{3}

$soundex = ([a-z]|[^a-z]:'')* @ $step3 @ $step1 @ $step2 @ $step4

view($soundex)
generate($soundex, washington) // w252
generate($soundex, pfister)    // p236
generate($soundex, ashcraft)   // a261
generate($soundex, knuth)      // k530
generate($soundex, gauss)      // g200
generate($soundex, lebowski)   // l120
`,
  },
  
];

function loadDemoByIndex(idx) {
  if (!editor) return;
  const demo = DEMOS[idx] ?? DEMOS[0];
  editor.value = demo.code;
  refreshEditorHighlight();
  clearOutput();
  setGraphPlaceholder('(Press Ctrl/Cmd+Enter or click Run.)');
}

if (demoSelect) {
  demoSelect.innerHTML = '';
  DEMOS.forEach((d, i) => {
    const opt = document.createElement('option');
    opt.value = String(i);
    opt.textContent = d.name;
    demoSelect.appendChild(opt);
  });
  demoSelect.addEventListener('change', (e) => {
    const i = Number(e.target.value);
    loadDemoByIndex(i);
  });
  loadDemoByIndex(0);
} else {
  // Fallback for other host pages without the demo dropdown.
  loadDemoByIndex(0);
}
