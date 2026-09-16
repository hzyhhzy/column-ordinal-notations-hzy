/*
 * ω-Y (weak magma) — original NER rules, with an additional CWY display.
 * Import this file with NER's custom-notation importer.
 * Registered id: omega-y-weak-cwy (does not replace the built-in notation).
 * Existing sequence / DBMS / DBMS_MN / ADBMS views, mountain drawing,
 * and FS / FS_alter / FS_short are retained unchanged.
 *
 * Original source: https://github.com/smilelee-lyx/ne-rewritten
 * Original notation credit: Yukito / Naruyoko, as recorded by NER.
 * Local adapter: output/wy-linear-20260914/ner/wy_cwy_entry.ts
 * Rebuild: node output/wy-linear-20260914/ner/build.mjs
 * Windows: powershell -File output/wy-linear-20260914/ner/build.ps1
 * This file is mechanically bundled; edit the source rather than this output.
 * No imports, network access, or external runtime dependencies are required.
 */
"use strict";
(() => {
  // .research-ne-rewritten/src/utils.ts
  function number_compare(a, b) {
    return a === b ? 0 : a < b ? -1 : 1;
  }
  function lex_compare(a, b, cmp) {
    let len = Math.min(a.length, b.length);
    for (let i = 0; i < len; i++) {
      const result = cmp(a[i], b[i]);
      if (result !== 0) return result;
    }
    return number_compare(a.length, b.length);
  }
  var DisplaySet = class {
    _map;
    _display;
    constructor(display, items) {
      this._display = display;
      this._map = /* @__PURE__ */ new Map();
      if (items) {
        for (const item of items) {
          this.add(item);
        }
      }
    }
    add(value) {
      this._map.set(this._display(value), value);
      return this;
    }
    has(value) {
      return this._map.has(this._display(value));
    }
    delete(value) {
      return this._map.delete(this._display(value));
    }
    values() {
      return Array.from(this._map.values());
    }
    get size() {
      return this._map.size;
    }
    forEach(callback) {
      this._map.forEach((value) => callback(value));
    }
    [Symbol.iterator]() {
      return this._map.values();
    }
  };
  var DisplayMap = class {
    _map;
    _display;
    constructor(display, entries) {
      this._display = display;
      this._map = /* @__PURE__ */ new Map();
      if (entries) {
        for (const [key, value] of entries) {
          this.set(key, value);
        }
      }
    }
    set(key, value) {
      this._map.set(this._display(key), [key, value]);
      return this;
    }
    get(key) {
      return this._map.get(this._display(key))?.[1];
    }
    has(key) {
      return this._map.has(this._display(key));
    }
    delete(key) {
      return this._map.delete(this._display(key));
    }
    entries() {
      return Array.from(this._map.values());
    }
    values() {
      return Array.from(this._map.values()).map(([, v]) => v);
    }
    keys() {
      return Array.from(this._map.values()).map(([k]) => k);
    }
    get size() {
      return this._map.size;
    }
    forEach(callback) {
      this._map.forEach(([k, v]) => callback(v, k));
    }
  };

  // .research-ne-rewritten/src/notations/notation_utils.ts
  function Y_FS_variants(expand_longer, is_infinity2, infinity_FS, is_limit2, display) {
    const data = {};
    const data_short = {};
    const core = {
      FS: (seq, index) => {
        if (is_infinity2(seq)) return infinity_FS(index);
        if (!seq.length) return [];
        if (!is_limit2(seq)) return seq.slice(0, seq.length - 1);
        const result = core.FS_alter(seq, index);
        return result.slice(0, result.length - 1);
      },
      FS_alter: (seq, index) => {
        if (is_infinity2(seq)) return infinity_FS(index);
        if (!seq.length) return [];
        if (!is_limit2(seq)) return seq.slice(0, seq.length - 1);
        const data_key = display(seq);
        if (data[data_key] === void 0) data[data_key] = [];
        else if (data[data_key][index] !== void 0) return data[data_key][index];
        return data[data_key][index] = expand_longer(seq, index);
      },
      FS_short: (seq, index) => {
        if (is_infinity2(seq)) return infinity_FS(index);
        if (!seq.length) return [];
        if (!is_limit2(seq)) return seq.slice(0, seq.length - 1);
        if (index === 0) return seq.slice(0, seq.length - 1);
        if (index === 1) {
          const result = core.FS_alter(seq, 1);
          return result.slice(0, seq.length);
        }
        const data_key = display(seq);
        const d = data_short[data_key];
        if (d === void 0) {
          data_short[data_key] = core.FS(seq, 1).length !== seq.length;
        }
        return core.FS(seq, index - (data_short[data_key] ? 1 : 0));
      }
    };
    return core;
  }

  // .research-ne-rewritten/src/notations/draw_mountain_util.ts
  function draw_mountain_diagram(data, opts) {
    const {
      W = 30,
      WV = 50,
      H_off = 10,
      padding = 10,
      text_size = 14,
      invert_vertical = false,
      display_html_vertical = false
    } = opts ?? {};
    const { sorted_verticals, heights, line_heights, entries, left_legs } = data;
    const cols = entries.length;
    if (cols === 0) return void 0;
    const height_last = heights[heights.length - 1] + padding;
    const total_height = height_last + padding;
    const width = WV + cols * W;
    const calc_cy = (vj) => invert_vertical ? padding + heights[vj] : height_last - heights[vj];
    const h_off_vec = invert_vertical ? -H_off : H_off;
    const elements = [];
    const lines = [];
    const extra_text = [];
    const black = { type: "text" };
    const gray = { type: "gray" };
    for (const h of line_heights) {
      const y = invert_vertical ? h + padding : height_last - h;
      lines.push({
        type: "line",
        x1: 0,
        y1: y,
        x2: width,
        y2: y,
        stroke: true,
        stroke_color: gray,
        width: 1
      });
    }
    for (let vj = 0; vj < sorted_verticals.length; vj++) {
      const label = sorted_verticals[vj];
      if (label === void 0) continue;
      extra_text.push({
        text: label,
        x: WV / 2,
        y: calc_cy(vj),
        size: text_size,
        color: black,
        align: "center",
        ...display_html_vertical ? { display_html: true } : {}
      });
    }
    for (let i = 0; i < cols; i++) {
      for (let vj = 0; vj < sorted_verticals.length; vj++) {
        const text = entries[i][vj];
        if (text === void 0) continue;
        const cx = WV + W * i + W / 2;
        const cy = calc_cy(vj);
        if (vj > 0) {
          let kv = vj - 1;
          while (kv > 0 && entries[i][kv] === void 0) kv--;
          if (entries[i][kv] !== void 0) {
            const cy_below = calc_cy(kv);
            lines.push({
              type: "line",
              x1: cx,
              y1: cy + h_off_vec,
              x2: cx,
              y2: cy_below - h_off_vec,
              stroke: true,
              stroke_color: black,
              width: 1
            });
          }
        }
        const leg = left_legs[i][vj];
        if (leg !== void 0 && vj > 0) {
          const [pi, pvj] = leg;
          const p_cx = WV + W * pi + W / 2;
          const cy_mid = calc_cy(vj - 1);
          const cy_target = calc_cy(pvj);
          lines.push({
            type: "line",
            x1: cx,
            y1: cy + h_off_vec,
            x2: p_cx,
            y2: cy_mid - h_off_vec,
            stroke: true,
            stroke_color: black,
            width: 1
          });
          lines.push({
            type: "line",
            x1: p_cx,
            y1: cy_mid - h_off_vec,
            x2: p_cx,
            y2: cy_target - h_off_vec,
            stroke: true,
            stroke_color: black,
            width: 1
          });
        }
        extra_text.push({
          text,
          x: cx,
          y: cy,
          size: text_size,
          color: black,
          align: "center"
        });
      }
    }
    elements.unshift(...lines);
    return { width, height: total_height, elements, extra_text };
  }

  // .research-ne-rewritten/src/notations/Y/Omega_Y.ts
  function INFINITY() {
    return [Infinity];
  }
  function is_infinity(expr) {
    return "" + expr === "Infinity";
  }
  function sequence_display(expr) {
    return is_infinity(expr) ? "Limit" : "" + expr;
  }
  function is_limit(seq) {
    return seq[seq.length - 1] > 1;
  }
  var sequence_from_display = (str) => {
    if (str === "Limit") return INFINITY();
    const result = str.split(",").map((s) => parseInt(s.trim(), 10));
    if (result.find(Number.isNaN) !== void 0) throw new Error("Illegal omega-Y sequence");
    return result;
  };
  function seq_compare(a, b) {
    return lex_compare(a, b, number_compare);
  }
  var from_sequence = (seq) => {
    const mountain = [];
    for (let i = 0; i < seq.length; i++) {
      const bottom = { value: seq[i], x: i, y: [1], left_up: [] };
      const phantom = { x: i, y: [], left_up: [], value: void 0 };
      bottom.right_down = phantom;
      phantom.right_up = bottom;
      if (i > 0) {
        bottom.left_down = mountain[i - 1][1];
        mountain[i - 1][1].left_up.push(bottom);
      }
      mountain[i] = [bottom, phantom];
    }
    return mountain;
  };
  function to_sequence(mountain) {
    return mountain.map((col) => col[col.length - 2].value);
  }
  function vertical_compare(a, b) {
    if (a.length > b.length) return 1;
    if (a.length < b.length) return -1;
    for (let i = a.length; i >= 0; i--) {
      if (a[i] > b[i]) return 1;
      if (a[i] < b[i]) return -1;
    }
    return 0;
  }
  function same_row(entry1, entry2) {
    return !vertical_compare(entry1.y, entry2.y);
  }
  function vertical_increase(y, d) {
    const c = y.slice();
    c[d] = (c[d] ?? 0) + 1;
    c.fill(0, 0, d);
    return c;
  }
  function dimension_difference(c1, c2) {
    let d = Math.max(c1.length, c2.length);
    while (d--) {
      if (c1[d] !== c2[d]) return d;
    }
    return d;
  }
  function create_entry(parent, entry) {
    const new_entry = {
      value: entry.value - parent.value,
      x: entry.x,
      y: vertical_increase(entry.y, dimension_difference(parent.y, entry.y) + 1),
      left_up: []
    };
    new_entry.right_down = entry;
    entry.right_up = new_entry;
    new_entry.left_down = parent;
    parent.left_up.push(new_entry);
    return new_entry;
  }
  function draw_mountain(mountain) {
    for (const column of mountain) {
      while (true) {
        const entry = column[0];
        if (entry.value === 1) break;
        let parent = entry;
        while (true) {
          let up = parent.left_down;
          while (up.right_up && vertical_compare(up.right_up.y, parent.y) <= 0) up = up.right_up;
          parent = up;
          if (parent.value < entry.value) break;
        }
        column.unshift(create_entry(parent, entry));
      }
    }
    return mountain;
  }
  function find_lower(column, y) {
    let i1 = 0, i2 = column.length - 1;
    while (i1 < i2) {
      const i = Math.floor((i1 + i2) / 2);
      if (vertical_compare(column[i].y, y) < 0) i2 = i;
      else i1 = i + 1;
    }
    return column[i2];
  }
  function find_higher_equal(column, y) {
    let i1 = 0, i2 = column.length - 1;
    while (i1 < i2) {
      const i = Math.ceil((i1 + i2) / 2);
      if (vertical_compare(column[i].y, y) >= 0) i1 = i;
      else i2 = i - 1;
    }
    return column[i1];
  }
  function y_slice(column, low_equal, high) {
    let i1 = 0, i2 = column.length - 1;
    while (i1 < i2) {
      const i = Math.floor((i1 + i2) / 2);
      if (vertical_compare(column[i].y, high) < 0) i2 = i;
      else i1 = i + 1;
    }
    const start = i2;
    i1 = start;
    i2 = column.length - 1;
    while (i1 < i2) {
      const i = Math.floor((i1 + i2) / 2);
      if (vertical_compare(column[i].y, low_equal) < 0) i2 = i;
      else i1 = i + 1;
    }
    return column.slice(start, i2);
  }
  function collect_usual(working_entry, collection = []) {
    for (const e of working_entry.left_up) {
      const child = e.right_down;
      if (collection.includes(child)) continue;
      if (same_row(working_entry, child)) {
        collection.push(child);
        collect_usual(child, collection);
      }
    }
    return collection;
  }
  function collect1D(working_entry, collection = []) {
    for (const child of working_entry.right_down.left_up) {
      if (collection.includes(child)) continue;
      if (same_row(working_entry, child)) {
        collection.push(child);
        collect1D(child, collection);
      }
    }
    return collection;
  }
  function collect(working_entry) {
    if (vertical_compare(working_entry.y, [1]) > 0 && dimension_difference(working_entry.y, working_entry.right_down.y) === 0) {
      return collect1D(working_entry);
    } else {
      return collect_usual(working_entry);
    }
  }
  function fill_magma_edge(mountain, source_entry, left_leg_entry) {
    const target_x = source_entry.x - source_entry.left_down.x + left_leg_entry.x;
    for (let d = dimension_difference(left_leg_entry.y, left_leg_entry.right_up.y); d >= 0; --d) {
      const new_entry = {
        x: target_x,
        y: vertical_increase(left_leg_entry.y, d),
        left_up: [],
        value: void 0
      };
      new_entry.left_down = left_leg_entry;
      left_leg_entry.left_up.push(new_entry);
      mountain[target_x].push(new_entry);
    }
  }
  function copy_single_edge(mountain, source_entry, x_offset, BR_x, target_y) {
    if (target_y === void 0) target_y = source_entry.y;
    const new_entry = {
      x: source_entry.x + x_offset,
      y: target_y.slice(),
      left_up: [],
      value: void 0
    };
    if (source_entry.y.length > 0) {
      let left_leg_entry;
      if (source_entry.left_down.x >= BR_x) {
        left_leg_entry = find_lower(mountain[source_entry.left_down.x + x_offset], new_entry.y);
      } else {
        left_leg_entry = source_entry.left_down;
      }
      new_entry.left_down = left_leg_entry;
      left_leg_entry.left_up.push(new_entry);
    }
    mountain[source_entry.x + x_offset].push(new_entry);
  }
  function expand_weak_magma(seq, index) {
    const mountain = draw_mountain(from_sequence(seq));
    const child = mountain[mountain.length - 1];
    let BR = child[0].left_down;
    const width = mountain.length - 1 - BR.x;
    let top = mountain[BR.x];
    top = top.slice(
      top.findIndex((entry) => entry === BR),
      top.length - 1
    );
    top.unshift(child[0]);
    const s = seq.slice();
    s[s.length - 1]--;
    const newMountain = draw_mountain(from_sequence(s));
    BR = newMountain[BR.x].find((entry) => same_row(entry, BR));
    const magma_entries = [];
    for (let BR1 = BR; true; BR1 = BR1.right_down) {
      collect_usual(BR1).forEach((entry) => {
        const dx = entry.x - BR.x;
        if (magma_entries[dx] === void 0) magma_entries[dx] = [];
        magma_entries[dx].push(entry);
      });
      if (!BR1.y.length) break;
    }
    for (let n = 1; n <= index; n++) {
      const ref = top.map((top_entry) => find_lower(newMountain[newMountain.length - 1], top_entry.y));
      for (let dx = 1; dx <= width; dx++) {
        const column = [];
        newMountain[BR.x + n * width + dx] = column;
        for (const magma_entry of magma_entries[dx]) {
          copy_single_edge(newMountain, magma_entry, n * width, BR.x);
          let source_entry = magma_entry;
          let target_y = find_higher_equal(ref, magma_entry.y).y;
          const target_y0 = target_y;
          while (!(source_entry.value <= 1 || magma_entries[dx].includes(source_entry.right_up))) {
            target_y = vertical_increase(
              target_y,
              dimension_difference(source_entry.y, source_entry.right_up.y)
            );
            source_entry = source_entry.right_up;
            copy_single_edge(newMountain, source_entry, n * width, BR.x, target_y);
          }
          const left_leg_x = magma_entry.right_up.left_down.x + n * width;
          y_slice(newMountain[left_leg_x], magma_entry.y, target_y0).forEach(
            (left_leg_entry) => fill_magma_edge(newMountain, magma_entry.right_up, left_leg_entry)
          );
        }
        column.sort((entry1, entry2) => -vertical_compare(entry1.y, entry2.y));
        for (let i = 0; i < column.length - 1; i++) {
          column[i].right_down = column[i + 1];
          column[i + 1].right_up = column[i];
        }
        column[0].value = 1;
        column.slice(1, column.length - 1).forEach((entry) => {
          entry.value = entry.right_up.value + entry.right_up.left_down.value;
        });
      }
    }
    return to_sequence(newMountain);
  }
  function expand_actual_magma(seq, index) {
    const mountain = draw_mountain(from_sequence(seq));
    const child = mountain[mountain.length - 1];
    const BR = child[0].left_down;
    const width = mountain.length - 1 - BR.x;
    let top = mountain[BR.x];
    top = top.slice(
      top.findIndex((entry) => entry === BR),
      top.length - 1
    );
    top.unshift(child[0]);
    const s = seq.slice();
    s[s.length - 1]--;
    const sMountain = draw_mountain(from_sequence(s));
    const newBR = sMountain[BR.x].find((entry) => same_row(entry, BR));
    const magma_entries = [];
    for (let BR1 = newBR; true; BR1 = BR1.right_down) {
      collect(BR1).forEach((entry) => {
        const dx = entry.x - BR1.x;
        if (magma_entries[dx] === void 0) magma_entries[dx] = [];
        magma_entries[dx].push(entry);
      });
      if (!BR1.y.length) break;
    }
    for (let n = 1; n <= index; n++) {
      const ref = top.map((top_entry) => find_lower(sMountain[sMountain.length - 1], top_entry.y));
      for (let dx = 1; dx <= width; dx++) {
        const column = [];
        sMountain[BR.x + n * width + dx] = column;
        for (const magma_entry of magma_entries[dx]) {
          copy_single_edge(sMountain, magma_entry, n * width, BR.x);
          let source_entry = magma_entry;
          let target_y = find_higher_equal(ref, magma_entry.y).y;
          const target_y0 = target_y;
          while (!(source_entry.value <= 1 || magma_entries[dx].includes(source_entry.right_up))) {
            target_y = vertical_increase(
              target_y,
              dimension_difference(source_entry.y, source_entry.right_up.y)
            );
            source_entry = source_entry.right_up;
            copy_single_edge(sMountain, source_entry, n * width, BR.x, target_y);
          }
          if (!magma_entry.y.length) continue;
          const left_leg_x = magma_entry.left_down.x + n * width;
          y_slice(sMountain[left_leg_x], magma_entry.y, target_y0).forEach(
            (left_leg_entry) => fill_magma_edge(sMountain, magma_entry, left_leg_entry)
          );
        }
        column.sort((entry1, entry2) => -vertical_compare(entry1.y, entry2.y));
        for (let i = 0; i < column.length - 1; i++) {
          column[i].right_down = column[i + 1];
          column[i + 1].right_up = column[i];
        }
        column[0].value = 1;
        column.slice(1, column.length - 1).forEach((entry) => {
          entry.value = entry.right_up.value + entry.right_up.left_down.value;
        });
      }
    }
    return to_sequence(sMountain);
  }
  function expand_medium_magma(seq, index) {
    const mountain = draw_mountain(from_sequence(seq));
    const child = mountain[mountain.length - 1];
    let BR = child[0].left_down;
    const width = mountain.length - 1 - BR.x;
    let top = mountain[BR.x];
    top = top.slice(
      top.findIndex((entry) => entry === BR),
      top.length - 1
    );
    top.unshift(child[0]);
    const s = seq.slice();
    s[s.length - 1]--;
    const newMountain = draw_mountain(from_sequence(s));
    BR = newMountain[BR.x].find((entry) => same_row(entry, BR));
    const magma_entries = [];
    for (let BR1 = BR; true; BR1 = BR1.right_down) {
      collect_usual(BR1).forEach((entry) => {
        const dx = entry.x - BR.x;
        if (magma_entries[dx] === void 0) magma_entries[dx] = [];
        magma_entries[dx].push(entry);
      });
      if (!BR1.y.length) break;
    }
    for (let n = 1; n <= index; n++) {
      const ref = top.map((top_entry) => find_lower(newMountain[newMountain.length - 1], top_entry.y));
      for (let dx = 1; dx <= width; dx++) {
        const column = [];
        newMountain[BR.x + n * width + dx] = column;
        for (const magma_entry of magma_entries[dx]) {
          copy_single_edge(newMountain, magma_entry, n * width, BR.x);
          let source_entry = magma_entry;
          let target_y = find_higher_equal(ref, magma_entry.y).y;
          const target_y0 = target_y;
          while (!(source_entry.value <= 1 || magma_entries[dx].includes(source_entry.right_up))) {
            target_y = vertical_increase(
              target_y,
              dimension_difference(source_entry.y, source_entry.right_up.y)
            );
            source_entry = source_entry.right_up;
            copy_single_edge(newMountain, source_entry, n * width, BR.x, target_y);
          }
          if (!magma_entry.y.length) continue;
          const left_leg_x = magma_entry.left_down.x + n * width;
          y_slice(newMountain[left_leg_x], magma_entry.y, target_y0).forEach(
            (left_leg_entry) => fill_magma_edge(newMountain, magma_entry, left_leg_entry)
          );
        }
        column.sort((entry1, entry2) => -vertical_compare(entry1.y, entry2.y));
        for (let i = 0; i < column.length - 1; i++) {
          column[i].right_down = column[i + 1];
          column[i + 1].right_up = column[i];
        }
        column[0].value = 1;
        column.slice(1, column.length - 1).forEach((entry) => {
          entry.value = entry.right_up.value + entry.right_up.left_down.value;
        });
      }
    }
    return to_sequence(newMountain);
  }
  function expand_strong_magma(seq, index) {
    const mountain = draw_mountain(from_sequence(seq));
    const child = mountain[mountain.length - 1];
    let BR = child[0].left_down;
    const width = mountain.length - 1 - BR.x;
    let top = mountain[BR.x];
    top = top.slice(
      top.findIndex((entry) => entry === BR),
      top.length - 1
    );
    top.unshift(child[0]);
    const s = seq.slice();
    s[s.length - 1]--;
    const newMountain = draw_mountain(from_sequence(s));
    BR = newMountain[BR.x].find((entry) => same_row(entry, BR));
    const magma_entries = [];
    for (let BR1 = BR; true; BR1 = BR1.right_down) {
      if (BR1.y.length) {
        collect1D(BR1).forEach((entry) => {
          const dx = entry.x - BR.x;
          if (magma_entries[dx] === void 0) magma_entries[dx] = [];
          magma_entries[dx].push(entry);
        });
      } else {
        newMountain.slice(BR.x + 1).forEach((column, dx1) => magma_entries[dx1 + 1].push(column[column.length - 1]));
        break;
      }
    }
    for (let n = 1; n <= index; n++) {
      const ref = top.map((top_entry) => find_lower(newMountain[newMountain.length - 1], top_entry.y));
      for (let dx = 1; dx <= width; dx++) {
        const column = [];
        newMountain[BR.x + n * width + dx] = column;
        for (const magma_entry of magma_entries[dx]) {
          copy_single_edge(newMountain, magma_entry, n * width, BR.x);
          let source_entry = magma_entry;
          let target_y = find_higher_equal(ref, magma_entry.y).y;
          const target_y0 = target_y;
          while (!(source_entry.value <= 1 || magma_entries[dx].includes(source_entry.right_up))) {
            target_y = vertical_increase(
              target_y,
              dimension_difference(source_entry.y, source_entry.right_up.y)
            );
            source_entry = source_entry.right_up;
            copy_single_edge(newMountain, source_entry, n * width, BR.x, target_y);
          }
          if (!magma_entry.y.length) continue;
          const left_leg_x = magma_entry.left_down.x + n * width;
          y_slice(newMountain[left_leg_x], magma_entry.y, target_y0).forEach(
            (left_leg_entry) => fill_magma_edge(newMountain, magma_entry, left_leg_entry)
          );
        }
        column.sort((entry1, entry2) => -vertical_compare(entry1.y, entry2.y));
        for (let i = 0; i < column.length - 1; i++) {
          column[i].right_down = column[i + 1];
          column[i + 1].right_up = column[i];
        }
        column[0].value = 1;
        column.slice(1, column.length - 1).forEach((entry) => {
          entry.value = entry.right_up.value + entry.right_up.left_down.value;
        });
      }
    }
    return to_sequence(newMountain);
  }
  function draw_dbms_mountain(m, Asheep) {
    let mountain = m;
    for (let col of mountain) {
      for (let j = col.length - 3; j >= 0; j--) {
        let entry = col[j];
        if (entry.y.length === 0) continue;
        entry.sep = dimension_difference(entry.y, entry.left_down.y);
        let left_entry = entry.left_down.right_up;
        if (Asheep && left_entry !== void 0 && vertical_compare(left_entry.y, entry.y) !== 0)
          left_entry = void 0;
        entry.depth = 1 + (left_entry?.depth ?? 0);
      }
    }
    return mountain;
  }
  function to_dbms_display(seq, type) {
    if ("" + seq === "Infinity") return "Limit";
    let mountain = draw_dbms_mountain(draw_mountain(from_sequence(seq)), type === "ADBMS");
    let result = "";
    for (let col of mountain) {
      result += "(";
      for (let j = col.length - 3; j >= 0; j--) {
        let entry = col[j];
        switch (type) {
          case "DBMS":
            result += entry.depth + ",".repeat(entry.sep + 1);
            break;
          case "DBMS'":
          case "ADBMS":
            result += ",".repeat(entry.sep + 1) + entry.depth;
            break;
        }
      }
      if (type === "DBMS") result += "0";
      result += ")";
    }
    return result;
  }
  var cwy_display_cache = /* @__PURE__ */ new Map();
  var cwy_cache_characters = 0;
  function to_cwy_display(seq) {
    const limits = {
      milliseconds: 500,
      steps: 5e5,
      cells: 25e3,
      columns: 2e4,
      word: 512,
      payload: 5e5,
      text: 1e6
    };
    try {
      if (seq.length === 1 && seq[0] === Infinity) return "[][S]";
      if (!seq.length) return "0";
      if (seq.length > limits.columns) throw new Error("列数超过显示预算");
      if (seq.some((value) => !Number.isSafeInteger(value) || value < 1))
        throw new Error("原数列含非正整数或超出 JS 安全整数范围，无法精确转换");
      if (seq[0] !== 1) throw new Error("原数列必须以 1 开头");
      if (seq.length === 1) return "[]";
      const root = seq[1];
      if (seq.length + root - 1 > limits.columns)
        throw new Error("根部拉长后的列数超过显示预算");
      const key = seq.join(",");
      const cached = cwy_display_cache.get(key);
      if (cached !== void 0) return cached;
      const started = Date.now();
      let steps = 0, cells = 2 * seq.length, payload = 0;
      const tick = () => {
        if (++steps > limits.steps || cells > limits.cells || payload > limits.payload || Date.now() - started >= limits.milliseconds)
          throw new Error("转换达到时间或结构预算；未输出截断表示");
      };
      let text = "[][]" + "[S]".repeat(root - 1);
      if (seq.length > 2) {
        const mountain = from_sequence(seq);
        for (const column of mountain) {
          while (column[0].value !== 1) {
            tick();
            const entry = column[0];
            let parent = entry;
            do {
              let up = parent.left_down;
              while (up.right_up && vertical_compare(up.right_up.y, parent.y) <= 0) {
                tick();
                up = up.right_up;
              }
              parent = up;
              tick();
            } while (parent.value >= entry.value);
            const dimension = dimension_difference(parent.y, entry.y) + 1;
            if (Math.max(entry.y.length, dimension + 1) > limits.word)
              throw new Error("源图层数超过显示预算");
            ++cells;
            tick();
            column.unshift(create_entry(parent, entry));
          }
        }
        const words = /* @__PURE__ */ new Map();
        const compare_words = (a, b) => a[0] - b[0] || a.length - b.length || lex_compare(a, b, number_compare);
        const move = (i) => i === 0 ? 0 : i + root - 1;
        for (let child = 0; child < mountain.length; child++) {
          const maxima = /* @__PURE__ */ new Map();
          for (const entry of mountain[child].slice(0, -2)) {
            tick();
            const parent = entry.left_down;
            const cap = parent.right_up;
            const inherited = cap ? words.get(cap) : [parent.x];
            if (!inherited) throw new Error("父盖轮廓缺失");
            const dimension = dimension_difference(parent.y, entry.right_down.y) + 1;
            const length = Math.max(inherited.length, dimension + 1);
            if (length > limits.word) throw new Error("祖先词长度超过显示预算");
            payload += length;
            tick();
            let word = [...Array(length - inherited.length).fill(inherited[0]), ...inherited];
            if (dimension) word.fill(child, word.length - dimension);
            let first = 0;
            while (first + 1 < word.length && word[first] === word[first + 1]) first++;
            word = word.slice(first);
            words.set(entry, word);
            const previous = maxima.get(parent.x);
            if (!previous || compare_words(previous, word) < 0) maxima.set(parent.x, word);
          }
          if (child < 2) continue;
          const rows = [...maxima].sort((a, b) => b[0] - a[0]);
          text += "[" + rows.map(([parent, word]) => move(parent) + ":(" + word.map(move).join(",") + ")").join(";") + "]";
          if (text.length > limits.text) throw new Error("完整字符串超过显示预算");
        }
      }
      tick();
      if (key.length + text.length <= 25e4) {
        while (cwy_display_cache.size && (cwy_display_cache.size >= 64 || cwy_cache_characters + key.length + text.length > 5e5)) {
          const oldest = cwy_display_cache.keys().next().value;
          cwy_cache_characters -= oldest.length + cwy_display_cache.get(oldest).length;
          cwy_display_cache.delete(oldest);
        }
        cwy_display_cache.set(key, text);
        cwy_cache_characters += key.length + text.length;
      }
      return text;
    } catch (error) {
      return "CWY 暂不可显示：" + (error instanceof Error ? error.message : String(error));
    }
  }
  function vertical_display(v) {
    return v.toReversed().join(",");
  }
  function vertical_display_html(v) {
    if (v.length === 0) return "0";
    const parts = [];
    for (let i = v.length - 1; i >= 0; i--) {
      const c = v[i];
      if (c === 0) continue;
      if (i === 0) {
        parts.push("" + c);
      } else if (i === 1) {
        parts.push(c === 1 ? "ω" : "ω" + c);
      } else {
        parts.push(c === 1 ? `ω<sup>${i}</sup>` : `ω<sup>${i}</sup>${c}`);
      }
    }
    return parts.join("+");
  }
  function compute_y_mountain_diagram(seq, current_equiv) {
    if (is_infinity(seq) || seq.length === 0) return void 0;
    const mountain = draw_dbms_mountain(draw_mountain(from_sequence(seq)), current_equiv === "ADBMS");
    const vertical_set = new DisplaySet(vertical_display);
    for (const col of mountain) for (const entry of col) vertical_set.add(entry.y);
    const sorted = vertical_set.values().sort(vertical_compare);
    const vertical_index = new DisplayMap(vertical_display);
    for (let i = 0; i < sorted.length; i++) vertical_index.set(sorted[i], i);
    const entries = Array.from(
      { length: mountain.length },
      () => Array.from({ length: sorted.length }, () => void 0)
    );
    const left_legs = Array.from(
      { length: mountain.length },
      () => Array.from({ length: sorted.length }, () => void 0)
    );
    for (let i = 0; i < mountain.length; i++) {
      for (let j = 0; j < mountain[i].length - 1; j++) {
        const entry = mountain[i][j];
        const vj = vertical_index.get(entry.y);
        if (current_equiv === "DBMS") {
          entries[i][vj - 1] = entry.right_up !== void 0 ? "" + entry.right_up.depth + ",".repeat(entry.right_up.sep + 1) : "0";
        } else if (current_equiv === "ADBMS" || current_equiv === "DBMS'") {
          entries[i][vj - 1] = entry.sep !== void 0 ? ",".repeat(entry.sep + 1) + entry.depth : "*";
        } else {
          entries[i][vj - 1] = "" + entry.value;
        }
        if (entry.left_down) {
          const pvj = vertical_index.get(entry.left_down.y);
          if (pvj !== 0) left_legs[i][vj - 1] = [entry.left_down.x, pvj - 1];
        }
      }
    }
    const H = 40, HS = 5;
    const heights = [0];
    const line_heights = [];
    for (let i = 2; i < sorted.length; i++) {
      const sep = dimension_difference(sorted[i], sorted[i - 1]);
      const d_height = H + HS * sep;
      heights.push(heights[i - 2] + d_height);
      for (let k = 0; k <= sep; k++) line_heights.push(heights[i - 2] + H / 2 + HS * k);
    }
    let vertical_names = sorted.slice(1).map((v) => vertical_display_html(v.length === 1 ? v[0] === 1 ? [] : [v[0] - 1] : v));
    return { sorted_verticals: vertical_names, heights, line_heights, entries, left_legs };
  }
  var y_diagram_control = {
    default_data: { current_equiv: void 0, invert_vertical: void 0 },
    draw_diagram: (seq, data) => {
      const mountain = compute_y_mountain_diagram(seq, data.current_equiv);
      if (!mountain) return void 0;
      return draw_mountain_diagram(mountain, {
        invert_vertical: data.invert_vertical ?? false,
        display_html_vertical: true
      });
    },
    handle_action: (data, action) => {
      if (action.type === "scroll") {
        if (action.direction === "down") return { ...data, invert_vertical: true };
        if (action.direction === "up") return { ...data, invert_vertical: false };
      }
      return null;
    }
  };
  function create_magma_notation(type, magma) {
    return {
      id: "omega-y-" + type,
      name: "ω-Y (" + type + " magma)",
      simple_name: "ωY " + type,
      category_id: "category-y-omega",
      display: {
        plain: sequence_display,
        from_display: sequence_from_display
      },
      display_equiv: {
        DBMS: (s) => to_dbms_display(s, "DBMS"),
        DBMS_MN: (s) => to_dbms_display(s, "DBMS'"),
        ADBMS: (s) => to_dbms_display(s, "ADBMS")
      },
      is_limit,
      compare: seq_compare,
      draw_diagram: y_diagram_control,
      ...Y_FS_variants(magma, is_infinity, (index) => [1, index + 1], is_limit, sequence_display),
      credit_text_id: "credit.yukito",
      init: () => [INFINITY(), [1], []]
    };
  }
  var omega_Y_weak = (() => {
    const notation = create_magma_notation("weak", expand_weak_magma);
    notation.display_equiv = {
      ...notation.display_equiv,
      "CWY 紧凑列表": { plain: to_cwy_display }
    };
    return notation;
  })();
  var omega_Y_actual = create_magma_notation("actual", expand_actual_magma);
  var omega_Y_medium = create_magma_notation("medium", expand_medium_magma);
  var omega_Y_strong = create_magma_notation("strong", expand_strong_magma);

  // output/wy-linear-20260914/ner/wy_cwy_entry.ts
  register_notation({
    ...omega_Y_weak,
    id: "omega-y-weak-cwy",
    name: "ω-Y (weak magma) · CWY视图",
    simple_name: "ωY weak · CWY",
    display_equiv: {
      ...omega_Y_weak.display_equiv,
      "CWY 紧凑列表": { plain: to_cwy_display }
    }
  });
})();
