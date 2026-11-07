function word_to_u32(w) {
  let x = 0;
  for (let i = 0; w.$ === "WCon"; i++) {
    x |= Number(w.head) << i;
    w = w.tail;
  }
  return x >>> 0;
}

function u32_to_word(x) {
  let w = {$: "WNil"};
  for (let i = 31; i >= 0; i--) {
    w = {$: "WCon", head: ((x >>> i) & 1) === 1, tail: w};
  }
  return w;
}

function cmp_new(a, b) {
  return {$: a < b ? "LT" : a === b ? "EQ" : "GT"};
}

function nat_divmod(a, b) {
  return b === 0 ? {$: "Tuple", fst: 0, snd: a}
    : {$: "Tuple", fst: Math.trunc(a / b), snd: a % b};
}

function nat_chk(n) {
  if (n > 281474976710655) {
    throw "bend: a Nat past the largest immediate 2^48-1";
  }
  return n;
}

function nat_in(n) {
  if (!Number.isInteger(n) || n < 0 || n > 2 ** 53) {
    throw "bend: expected a Nat host number: an integer from 0 to 2^53";
  }
  return n;
}

function f32_show(x) {
  let s = "nan";
  for (let p = 1; x === x && p <= 9 && f32_round(s) !== x; p += 1) {
    s = String(Number(x.toExponential(p - 1)));
  }
  return (Object.is(x, -0) ? "-0" : s).replace("Infinity", "inf");
}

function f32_bits(x) {
  return new Uint32Array(new Float32Array([x]).buffer)[0];
}

function f32_from_bits(u) {
  return new Float32Array(new Uint32Array([u]).buffer)[0];
}

function f32_read(s) {
  const re = /^[\t\n\v\f\r ]*[+-]?((\d+(?:\.\d*)?|\.\d+)(e[+-]?\d+)?|inf(inity)?|nan)$/i;
  const v = f32_round(s.replace(/inf\w*/i, "Infinity"));
  return re.test(s) ? {$: "Some", value: v} : {$: "None"};
}

const f32_round = function f32_round(s) {
  const d = Number(s);
  const a = Math.abs(d);
  const f = Math.fround(a);
  const g = 2 * a - Math.min(f, 2 ** 128);
  if (g === f || Math.fround(g) !== g || g === Infinity) {
    return Math.sign(d) * f;
  }
  let k = 0;
  while (a * 2 ** k % 1 !== 0) {
    k += 1;
  }
  const [, i, r, e] = /(\d*)\.?(\d*)(?:e([+-]?\d+))?$/i.exec(s);
  const n = Number(e ?? 0) - r.length;
  const x = BigInt(i + r) * 2n ** BigInt(k) * 10n ** BigInt(Math.max(n, 0));
  const y = BigInt(a * 2 ** k) * 10n ** BigInt(Math.max(-n, 0));
  return Math.sign(d) * (x === y || x > y !== g > f ? f : g);
};

const char_new = function char_new(c) {
  return c < 55296 || c >= 57344 && c <= 1114111 ? String.fromCodePoint(c) : String.fromCharCode(56320, c >>> 22, c >>> 11 & 2047, c & 2047);
};

function char_len(s, at = 0) {
  return s[at] === "\uDC00" ? 4 : s.codePointAt(at) > 0xFFFF ? 2 : 1;
}

function char_code(s) {
  return s.length < 4 ? s.codePointAt(0)
    : (s.charCodeAt(1) << 22 | s.charCodeAt(2) << 11 | s.charCodeAt(3)) >>> 0;
}

function string_contains(s, p) {
  // A match must start at a Char boundary, not inside a packed U32 code.
  for (let at = 0; at <= s.length; at += char_len(s, at)) {
    if (s.startsWith(p, at)) {
      return true;
    }
  }
  return false;
}

function str_out(s) {
  return s.replace(/\uDC00[^]{3}/gu, "\uFFFD");
}

function str_in(s) {
  return s.replace(/\p{Cs}/gu, "\uFFFD");
}

// Array
// =====

function array_new(d, v) {
  if (d > 31) {
    throw "bend: an array past the deepest block class 31";
  }
  return Array(2 ** d).fill(v);
}

function array_node(a, b) {
  if (a.length !== b.length) {
    throw "bend: runtime fail-stop";
  }
  return a.concat(b);
}

function array_rmw(a, i, f) {
  const at = i % a.length;
  const old = a[at];
  a[at] = f(old);
  return {$: "Tuple", fst: a, snd: old};
}

// Run
// ===

function run_tail(f, x) {
  return {$: "$JMP", f: f.j?.f === f ? f.j : f, x};
}

function run_clo(j) {
  const f = (x) => run_loop(j(x));
  f.j = j;
  j.f = f;
  return f;
}

function run_loop(r) {
  while (r !== null && typeof r === "object" && r.$ === "$JMP") {
    r = r.f(r.x);
  }
  return r;
}

function run_lib(f, n) {
  return (...a) => a.length < n ? run_lib((...b) => f(...a, ...b), n - a.length)
    : run_loop(f(...a));
}

// Effect
// ======

const $0eff = Object.create(null);

function io_eff(k, run) {
  if (arguments.length > 2) {
    throw new Error("bend: " + k + " takes no need: an effect that waits parks itself");
  }
  if (k in $0eff) {
    throw new Error("bend: two effects register " + k);
  }
  $0eff[k] = run;
}
// Program
// =======

function $bool_ite(_cond_0, _t_0, _f_0) {
  if (_cond_0) {
    return _t_0;
  } else {
    return _f_0;
  }
}

function $nat_ite(_cond_0, _t_0, _f_0) {
  if (_cond_0) {
    return _t_0;
  } else {
    return _f_0;
  }
}

function $box_strut_zero() {
  return {$: "Strut", "inline_start": 0, "inline_end": 0, "block_start": 0, "block_end": 0};
}

function $box_strut_inline_start(_s_0) {
  const _istart_0 = _s_0["inline_start"];
  return _istart_0;
}

function $box_strut_inline_end(_s_0) {
  const _ie_0 = _s_0["inline_end"];
  return _ie_0;
}

function $box_strut_block_start(_s_0) {
  const _bs_0 = _s_0["block_start"];
  return _bs_0;
}

function $box_strut_block_end(_s_0) {
  const _be_0 = _s_0["block_end"];
  return _be_0;
}

function $box_strut_inline_sum(_s_0) {
  const _inline_start_0 = _s_0["inline_start"];
  const _inline_end_0 = _s_0["inline_end"];
  return nat_chk(_inline_start_0 + _inline_end_0);
}

function $box_strut_block_sum(_s_0) {
  const _block_start_0 = _s_0["block_start"];
  const _block_end_0 = _s_0["block_end"];
  return nat_chk(_block_start_0 + _block_end_0);
}

function $box_strut_add(_a_0, _b_0) {
  const _is1_0 = _a_0["inline_start"];
  const _ie1_0 = _a_0["inline_end"];
  const _bs1_0 = _a_0["block_start"];
  const _be1_0 = _a_0["block_end"];
  const _is2_0 = _b_0["inline_start"];
  const _ie2_0 = _b_0["inline_end"];
  const _bs2_0 = _b_0["block_start"];
  const _be2_0 = _b_0["block_end"];
  return {$: "Strut", "inline_start": nat_chk(_is1_0 + _is2_0), "inline_end": nat_chk(_ie1_0 + _ie2_0), "block_start": nat_chk(_bs1_0 + _bs2_0), "block_end": nat_chk(_be1_0 + _be2_0)};
}

function $margin_strut_ite(_cond_0, _t_0, _f_0) {
  if (_cond_0) {
    return _t_0;
  } else {
    return _f_0;
  }
}

function $margin_strut_empty() {
  return {$: "MStrut", "pos": 0, "neg": 0};
}

function $margin_strut_append(_s1_0, _s2_0) {
  const _p1_0 = _s1_0["pos"];
  const _n1_0 = _s1_0["neg"];
  const _p2_0 = _s2_0["pos"];
  const _n2_0 = _s2_0["neg"];
  return {$: "MStrut", "pos": (_p1_0 > _p2_0 ? _p1_0 : _p2_0), "neg": (_n1_0 > _n2_0 ? _n1_0 : _n2_0)};
}

function $margin_strut_sum(_s_0) {
  const _pos_0 = _s_0["pos"];
  const _neg_0 = _s_0["neg"];
  return (_pos_0 < _neg_0 ? 0 : _pos_0 - _neg_0);
}

function $margin_strut_apply_offset(_y_0, _s_0) {
  const _pos_0 = _s_0["pos"];
  const _neg_0 = _s_0["neg"];
  const _x_0 = nat_chk(_y_0 + _pos_0);
  return (_x_0 < _neg_0 ? 0 : _x_0 - _neg_0);
}

function $font_height_zero() {
  return {$: "FHeight", "ascent": 0, "descent": 0};
}

function $font_height_ascent(_h_0) {
  const _ascent_0 = _h_0["ascent"];
  return _ascent_0;
}

function $font_height_descent(_h_0) {
  const _descent_0 = _h_0["descent"];
  return _descent_0;
}

function $font_height_line_height(_h_0) {
  const _ascent_0 = _h_0["ascent"];
  const _descent_0 = _h_0["descent"];
  return nat_chk(_ascent_0 + _descent_0);
}

function $font_height_merge(_h1_0, _h2_0) {
  const _a1_0 = _h1_0["ascent"];
  const _d1_0 = _h1_0["descent"];
  const _a2_0 = _h2_0["ascent"];
  const _d2_0 = _h2_0["descent"];
  return {$: "FHeight", "ascent": (_a1_0 > _a2_0 ? _a1_0 : _a2_0), "descent": (_d1_0 > _d2_0 ? _d1_0 : _d2_0)};
}

function $maybe_nat_ite(_cond_0, _t_0, _f_0) {
  if (_cond_0) {
    return _t_0;
  } else {
    return _f_0;
  }
}

function $maybe_nat_get_or(_m_0, _fallback_0) {
  if (_m_0.$ === "NoneNat") {
    return _fallback_0;
  } else {
    const _val_0 = _m_0["val"];
    return _val_0;
  }
}

function $maybe_nat_is_some(_m_0) {
  if (_m_0.$ === "NoneNat") {
    return false;
  } else {
    return true;
  }
}

function $maybe_nat_is_none(_m_0) {
  if (_m_0.$ === "NoneNat") {
    return true;
  } else {
    return false;
  }
}

function $nat_le($0, $1) {
  for (;;) {
    {
      const _a_0 = $0;
      const _b_0 = $1;
      if (_a_0 === 0) {
        return true;
      } else {
        const _p_0 = (_a_0 - 1);
        if (_b_0 === 0) {
          return false;
        } else {
          const _q_0 = (_b_0 - 1);
          $0 = _p_0;
          $1 = _q_0;
          continue;
        }
      }
    }
  }
}

function $nat_is_zero(_a_0) {
  if (_a_0 === 0) {
    return true;
  } else {
    return false;
  }
}

function $nat_pos(_a_0) {
  if (_a_0 === 0) {
    return false;
  } else {
    return true;
  }
}

function $inline_item_id(_it_0) {
  if (_it_0.$ === "TextSeg") {
    const _id_0 = _it_0["item_id"];
    return _id_0;
  } else if (_it_0.$ === "AtomicInline") {
    const _id_1 = _it_0["item_id"];
    return _id_1;
  } else if (_it_0.$ === "OpenTag") {
    const _id_2 = _it_0["item_id"];
    return _id_2;
  } else if (_it_0.$ === "CloseTag") {
    const _id_3 = _it_0["item_id"];
    return _id_3;
  } else {
    const _id_4 = _it_0["item_id"];
    return _id_4;
  }
}

function $inline_item_raw_inline_size(_it_0) {
  if (_it_0.$ === "TextSeg") {
    const _w_0 = _it_0["inline_size"];
    return _w_0;
  } else if (_it_0.$ === "AtomicInline") {
    const _w_1 = _it_0["inline_size"];
    return _w_1;
  } else if (_it_0.$ === "OpenTag") {
    const _b_0 = _it_0["border_inline_start"];
    const _p_0 = _it_0["padding_inline_start"];
    const _m_0 = _it_0["margin_inline_start"];
    const _x_0 = nat_chk(_b_0 + _p_0);
    return nat_chk(_x_0 + _m_0);
  } else if (_it_0.$ === "CloseTag") {
    const _b_1 = _it_0["border_inline_end"];
    const _p_1 = _it_0["padding_inline_end"];
    const _m_1 = _it_0["margin_inline_end"];
    const _x_1 = nat_chk(_b_1 + _p_1);
    return nat_chk(_x_1 + _m_1);
  } else {
    return 0;
  }
}

function $inline_item_font_height(_it_0) {
  if (_it_0.$ === "TextSeg") {
    const _fh_0 = _it_0["font_height"];
    return _fh_0;
  } else if (_it_0.$ === "AtomicInline") {
    const _fh_1 = _it_0["font_height"];
    return _fh_1;
  } else if (_it_0.$ === "OpenTag") {
    const _fh_2 = _it_0["font_height"];
    return _fh_2;
  } else if (_it_0.$ === "CloseTag") {
    return {$: "FHeight", "ascent": 0, "descent": 0};
  } else {
    return {$: "FHeight", "ascent": 0, "descent": 0};
  }
}

function $inline_item_is_empty_list(_items_0) {
  if (_items_0.$ === "Nil") {
    return true;
  } else {
    return false;
  }
}

function $take_line_aux_choose(_fits_0, _next_0, _cur_width_0, _non_break_count_0, _more_0, _rec_0) {
  if (_fits_0) {
    const _sub_items_0 = _rec_0["items"];
    const _final_w_0 = _rec_0["inline_size"];
    const _final_cnt_0 = _rec_0["non_break_count"];
    const _rem_0 = _rec_0["remaining"];
    return {$: "TakeAuxRes", "items": {$: "Con", "head": _next_0, "tail": _sub_items_0}, "inline_size": _final_w_0, "non_break_count": _final_cnt_0, "remaining": _rem_0};
  } else {
    return {$: "TakeAuxRes", "items": {$: "Nil"}, "inline_size": _cur_width_0, "non_break_count": _non_break_count_0, "remaining": {$: "Con", "head": _next_0, "tail": _more_0}};
  }
}

function $take_line_aux(_items_0, _avail_0, _cur_width_0, _pending_space_0, _non_break_count_0) {
  if (_items_0.$ === "Nil") {
    return {$: "TakeAuxRes", "items": {$: "Nil"}, "inline_size": _cur_width_0, "non_break_count": _non_break_count_0, "remaining": {$: "Nil"}};
  } else {
    const _t_0 = _items_0["head"];
    if (_t_0.$ === "ForcedBreak") {
      const _id_0 = _t_0["item_id"];
      const _more_0 = _items_0["tail"];
      return {$: "TakeAuxRes", "items": {$: "Con", "head": {$: "ForcedBreak", "item_id": _id_0}, "tail": {$: "Nil"}}, "inline_size": _cur_width_0, "non_break_count": _non_break_count_0, "remaining": _more_0};
    } else if (_t_0.$ === "TextSeg") {
      const _id_1 = _t_0["item_id"];
      const _w_0 = _t_0["inline_size"];
      const _fh_0 = _t_0["font_height"];
      const _cb_0 = _t_0["can_break_after"];
      const _t_1 = _t_0["is_trailing_space"];
      if (_t_1) {
        const _more_1 = _items_0["tail"];
        return $take_line_aux_choose(($nat_le(_cur_width_0, _avail_0)), {$: "TextSeg", "item_id": _id_1, "inline_size": _w_0, "font_height": _fh_0, "can_break_after": _cb_0, "is_trailing_space": true}, _cur_width_0, _non_break_count_0, _more_1, ($take_line_aux(_more_1, _avail_0, _cur_width_0, nat_chk(_pending_space_0 + _w_0), nat_chk(_non_break_count_0 + 1))));
      } else {
        const _more_2 = _items_0["tail"];
        const _x_0 = nat_chk(_cur_width_0 + _pending_space_0);
        const _new_w_0 = nat_chk(_x_0 + _w_0);
        return $take_line_aux_choose(($nat_le(_new_w_0, _avail_0)), {$: "TextSeg", "item_id": _id_1, "inline_size": _w_0, "font_height": _fh_0, "can_break_after": _cb_0, "is_trailing_space": false}, _cur_width_0, _non_break_count_0, _more_2, ($take_line_aux(_more_2, _avail_0, _new_w_0, 0, nat_chk(_non_break_count_0 + 1))));
      }
    } else {
      const _more_3 = _items_0["tail"];
      const _w_1 = ($inline_item_raw_inline_size(_t_0));
      const _x_1 = nat_chk(_cur_width_0 + _pending_space_0);
      const _new_w_1 = nat_chk(_x_1 + _w_1);
      return $take_line_aux_choose(($nat_le(_new_w_1, _avail_0)), _t_0, _cur_width_0, _non_break_count_0, _more_3, ($take_line_aux(_more_3, _avail_0, _new_w_1, 0, nat_chk(_non_break_count_0 + 1))));
    }
  }
}

function $take_line_wrap(_first_0, _aux_0) {
  const _tail_items_0 = _aux_0["items"];
  const _final_w_0 = _aux_0["inline_size"];
  const _final_cnt_0 = _aux_0["non_break_count"];
  const _rem_0 = _aux_0["remaining"];
  return {$: "TakeRes", "line": {$: "LInfo", "items": {$: "Con", "head": _first_0, "tail": _tail_items_0}, "inline_size": _final_w_0, "non_break_item_count": _final_cnt_0}, "remaining": _rem_0};
}

function $take_line(_avail_0, _first_0, _rest_0) {
  if (_first_0.$ === "ForcedBreak") {
    const _id_0 = _first_0["item_id"];
    return {$: "TakeRes", "line": {$: "LInfo", "items": {$: "Con", "head": {$: "ForcedBreak", "item_id": _id_0}, "tail": {$: "Nil"}}, "inline_size": 0, "non_break_item_count": 0}, "remaining": _rest_0};
  } else if (_first_0.$ === "TextSeg") {
    const _id_1 = _first_0["item_id"];
    const _w_0 = _first_0["inline_size"];
    const _fh_0 = _first_0["font_height"];
    const _cb_0 = _first_0["can_break_after"];
    const _t_0 = _first_0["is_trailing_space"];
    if (_t_0) {
      return $take_line_wrap({$: "TextSeg", "item_id": _id_1, "inline_size": _w_0, "font_height": _fh_0, "can_break_after": _cb_0, "is_trailing_space": true}, ($take_line_aux(_rest_0, _avail_0, 0, _w_0, 1)));
    } else {
      return $take_line_wrap({$: "TextSeg", "item_id": _id_1, "inline_size": _w_0, "font_height": _fh_0, "can_break_after": _cb_0, "is_trailing_space": false}, ($take_line_aux(_rest_0, _avail_0, _w_0, 0, 1)));
    }
  } else {
    const _w_1 = ($inline_item_raw_inline_size(_first_0));
    return $take_line_wrap(_first_0, ($take_line_aux(_rest_0, _avail_0, _w_1, 0, 1)));
  }
}

function $take_line_info(_r_0) {
  const _line_0 = _r_0["line"];
  return _line_0;
}

function $take_line_rem(_r_0) {
  const _rem_0 = _r_0["remaining"];
  return _rem_0;
}

function $inline_item_list_len(_items_0) {
  if (_items_0.$ === "Nil") {
    return 0;
  } else {
    const _t_0 = _items_0["tail"];
    const _x_0 = ($inline_item_list_len(_t_0));
    return nat_chk(1 + _x_0);
  }
}

function $break_lines_fuel(_fuel_0, _avail_0, _items_0) {
  if (_fuel_0 === 0) {
    return {$: "Nil"};
  } else {
    const _p_0 = (_fuel_0 - 1);
    if (_items_0.$ === "Nil") {
      return {$: "Nil"};
    } else {
      const _first_0 = _items_0["head"];
      const _rest_0 = _items_0["tail"];
      const _step_0 = ($take_line(_avail_0, _first_0, _rest_0));
      return {$: "Con", "head": ($take_line_info(_step_0)), "tail": ($break_lines_fuel(_p_0, _avail_0, ($take_line_rem(_step_0))))};
    }
  }
}

function $break_lines(_avail_0, _items_0) {
  return $break_lines_fuel(($inline_item_list_len(_items_0)), _avail_0, _items_0);
}

function $line_info_items(_li_0) {
  const _items_0 = _li_0["items"];
  return _items_0;
}

function $line_info_inline_size(_li_0) {
  const _isz_0 = _li_0["inline_size"];
  return _isz_0;
}

function $line_info_non_break_count(_li_0) {
  const _cnt_0 = _li_0["non_break_item_count"];
  return _cnt_0;
}

function $line_info_list_len(_ls_0) {
  if (_ls_0.$ === "Nil") {
    return 0;
  } else {
    const _t_0 = _ls_0["tail"];
    const _x_0 = ($line_info_list_len(_t_0));
    return nat_chk(1 + _x_0);
  }
}

function $line_info_head_inline_size(_ls_0) {
  if (_ls_0.$ === "Nil") {
    return 0;
  } else {
    const _h_0 = _ls_0["head"];
    return $line_info_inline_size(_h_0);
  }
}

function $line_info_head_non_break_count(_ls_0) {
  if (_ls_0.$ === "Nil") {
    return 0;
  } else {
    const _h_0 = _ls_0["head"];
    return $line_info_non_break_count(_h_0);
  }
}

function $inline_item_append(_xs_0, _ys_0) {
  if (_xs_0.$ === "Nil") {
    return _ys_0;
  } else {
    const _h_0 = _xs_0["head"];
    const _t_0 = _xs_0["tail"];
    return {$: "Con", "head": _h_0, "tail": ($inline_item_append(_t_0, _ys_0))};
  }
}

function $accumulate_line_metrics(_items_0, _strut_0) {
  if (_items_0.$ === "Nil") {
    return _strut_0;
  } else {
    const _it_0 = _items_0["head"];
    const _rest_0 = _items_0["tail"];
    return $font_height_merge(($inline_item_font_height(_it_0)), ($accumulate_line_metrics(_rest_0, _strut_0)));
  }
}

function $place_line_items(_items_0, _line_metrics_0, _inline_off_0) {
  if (_items_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _it_0 = _items_0["head"];
    const _rest_0 = _items_0["tail"];
    const _fh_0 = ($inline_item_font_height(_it_0));
    const _w_0 = ($inline_item_raw_inline_size(_it_0));
    const _x_0 = ($font_height_ascent(_line_metrics_0));
    const _x_1 = ($font_height_ascent(_fh_0));
    return {$: "Con", "head": {$: "PlacedItem", "item_id": ($inline_item_id(_it_0)), "inline_offset": _inline_off_0, "block_offset": (_x_0 < _x_1 ? 0 : _x_0 - _x_1), "inline_size": _w_0, "block_size": ($font_height_line_height(_fh_0))}, "tail": ($place_line_items(_rest_0, _line_metrics_0, nat_chk(_inline_off_0 + _w_0)))};
  }
}

function $box_stack_active(_st_0) {
  const _active_0 = _st_0["active"];
  return _active_0;
}

function $box_stack_list(_st_0) {
  const _stack_0 = _st_0["stack"];
  return _stack_0;
}

function $step_box_state_stack(_it_0, _stack_0, _active_0) {
  if (_it_0.$ === "OpenTag") {
    const _fh_0 = _it_0["font_height"];
    return {$: "BoxStack", "active": _fh_0, "stack": {$: "Con", "head": _active_0, "tail": _stack_0}};
  } else if (_it_0.$ === "CloseTag") {
    if (_stack_0.$ === "Nil") {
      return {$: "BoxStack", "active": _active_0, "stack": {$: "Nil"}};
    } else {
      const _parent_0 = _stack_0["head"];
      const _rest_0 = _stack_0["tail"];
      return {$: "BoxStack", "active": ($font_height_merge(_parent_0, _active_0)), "stack": _rest_0};
    }
  } else {
    return {$: "BoxStack", "active": ($font_height_merge(_active_0, ($inline_item_font_height(_it_0)))), "stack": _stack_0};
  }
}

function $run_box_state_stack($0, $1, $2) {
  for (;;) {
    {
      const _items_0 = $0;
      const _active_0 = $1;
      const _stack_0 = $2;
      if (_items_0.$ === "Nil") {
        return {$: "BoxStack", "active": _active_0, "stack": _stack_0};
      } else {
        const _it_0 = _items_0["head"];
        const _rest_0 = _items_0["tail"];
        const _next_0 = ($step_box_state_stack(_it_0, _stack_0, _active_0));
        $0 = _rest_0;
        $1 = ($box_stack_active(_next_0));
        $2 = ($box_stack_list(_next_0));
        continue;
      }
    }
  }
}

function $flush_box_state_stack($0, $1) {
  for (;;) {
    {
      const _stack_0 = $0;
      const _active_0 = $1;
      if (_stack_0.$ === "Nil") {
        return _active_0;
      } else {
        const _parent_0 = _stack_0["head"];
        const _rest_0 = _stack_0["tail"];
        $0 = _rest_0;
        $1 = ($font_height_merge(_parent_0, _active_0));
        continue;
      }
    }
  }
}

function $apply_box_state_stack(_strut_0, _items_0) {
  const _st_0 = ($run_box_state_stack(_items_0, _strut_0, {$: "Nil"}));
  return $flush_box_state_stack(($box_stack_list(_st_0)), ($box_stack_active(_st_0)));
}

function $placed_item_block_offset(_p_0) {
  const _boff_0 = _p_0["block_offset"];
  return _boff_0;
}

function $placed_item_block_size(_p_0) {
  const _bsz_0 = _p_0["block_size"];
  return _bsz_0;
}

function $placed_item_head_block_offset(_ps_0) {
  if (_ps_0.$ === "Nil") {
    return 0;
  } else {
    const _p_0 = _ps_0["head"];
    return $placed_item_block_offset(_p_0);
  }
}

function $placed_item_head_block_size(_ps_0) {
  if (_ps_0.$ === "Nil") {
    return 0;
  } else {
    const _p_0 = _ps_0["head"];
    return $placed_item_block_size(_p_0);
  }
}

function $line_frag_metrics(_lf_0) {
  const _metrics_0 = _lf_0["metrics"];
  return _metrics_0;
}

function $line_frag_items(_lf_0) {
  const _placed_0 = _lf_0["items"];
  return _placed_0;
}

function $line_frag_block_offset(_lf_0) {
  const _t_0 = _lf_0["bfc_offset"];
  const _boff_0 = _t_0["block_offset"];
  return _boff_0;
}

function $line_frag_list_len(_ls_0) {
  if (_ls_0.$ === "Nil") {
    return 0;
  } else {
    const _t_0 = _ls_0["tail"];
    const _x_0 = ($line_frag_list_len(_t_0));
    return nat_chk(1 + _x_0);
  }
}

function $line_frag_head_block_offset(_ls_0) {
  if (_ls_0.$ === "Nil") {
    return 0;
  } else {
    const _h_0 = _ls_0["head"];
    return $line_frag_block_offset(_h_0);
  }
}

function $line_frag_second_block_offset(_ls_0) {
  if (_ls_0.$ === "Nil") {
    return 0;
  } else {
    const _t_0 = _ls_0["tail"];
    return $line_frag_head_block_offset(_t_0);
  }
}

function $create_line_box(_strut_0, _line_info_0) {
  const _items_0 = _line_info_0["items"];
  const _inline_sz_0 = _line_info_0["inline_size"];
  const _metrics_0 = ($accumulate_line_metrics(_items_0, _strut_0));
  return {$: "LineFrag", "bfc_offset": {$: "LOffset", "inline_offset": 0, "block_offset": 0}, "inline_size": _inline_sz_0, "metrics": _metrics_0, "items": ($place_line_items(_items_0, _metrics_0, 0))};
}

function $line_frag_list_ite(_cond_0, _t_0, _f_0) {
  if (_cond_0) {
    return _t_0;
  } else {
    return _f_0;
  }
}

function $line_frag_with_block_offset(_block_off_0, _lf_0) {
  const _off_0 = _lf_0["bfc_offset"];
  const _isz_0 = _lf_0["inline_size"];
  const _metrics_0 = _lf_0["metrics"];
  const _placed_0 = _lf_0["items"];
  return {$: "LineFrag", "bfc_offset": {$: "LOffset", "inline_offset": 0, "block_offset": _block_off_0}, "inline_size": _isz_0, "metrics": _metrics_0, "items": _placed_0};
}

function $line_frag_line_height(_lf_0) {
  const _metrics_0 = _lf_0["metrics"];
  return $font_height_line_height(_metrics_0);
}

function $stacked_lines_list(_r_0) {
  const _lines_0 = _r_0["lines"];
  return _lines_0;
}

function $stacked_lines_block_size(_r_0) {
  const _tbs_0 = _r_0["total_block_size"];
  return _tbs_0;
}

function $stack_line_boxes(_lines_0, _strut_0, _block_off_0) {
  if (_lines_0.$ === "Nil") {
    return {$: "StackedLines", "lines": {$: "Nil"}, "total_block_size": _block_off_0};
  } else {
    const _li_0 = _lines_0["head"];
    const _rest_0 = _lines_0["tail"];
    const _lb_0 = ($create_line_box(_strut_0, _li_0));
    const _lh_0 = ($line_frag_line_height(_lb_0));
    const _positioned_0 = ($line_frag_with_block_offset(_block_off_0, _lb_0));
    const _tail_0 = ($stack_line_boxes(_rest_0, _strut_0, nat_chk(_block_off_0 + _lh_0)));
    return {$: "StackedLines", "lines": {$: "Con", "head": _positioned_0, "tail": ($stacked_lines_list(_tail_0))}, "total_block_size": ($stacked_lines_block_size(_tail_0))};
  }
}

function $child_node_id(_c_0) {
  if (_c_0.$ === "BlockChild") {
    const _id_0 = _c_0["node_id"];
    return _id_0;
  } else {
    const _id_1 = _c_0["node_id"];
    return _id_1;
  }
}

function $child_margin(_c_0) {
  if (_c_0.$ === "BlockChild") {
    const _m_0 = _c_0["margin"];
    return _m_0;
  } else {
    const _m_1 = _c_0["margin"];
    return _m_1;
  }
}

function $child_resolve_inline_size(_avail_inline_0, _c_0) {
  if (_c_0.$ === "BlockChild") {
    const _m_0 = _c_0["margin"];
    const _ew_0 = _c_0["explicit_inline_size"];
    const _x_0 = ($box_strut_inline_sum(_m_0));
    return $maybe_nat_get_or(_ew_0, (_avail_inline_0 < _x_0 ? 0 : _avail_inline_0 - _x_0));
  } else {
    const _m_1 = _c_0["margin"];
    const _ew_1 = _c_0["explicit_inline_size"];
    const _x_1 = ($box_strut_inline_sum(_m_1));
    return $maybe_nat_get_or(_ew_1, (_avail_inline_0 < _x_1 ? 0 : _avail_inline_0 - _x_1));
  }
}

function $child_is_self_collapsing(_c_0) {
  if (_c_0.$ === "BlockChild") {
    const _b_0 = _c_0["border"];
    const _p_0 = _c_0["padding"];
    const _eh_0 = _c_0["explicit_block_size"];
    const _bfc_0 = _c_0["is_new_bfc"];
    const _has_c_0 = _c_0["has_inflow_content"];
    const _x_0 = ($box_strut_block_sum(_b_0));
    const _x_1 = ($box_strut_block_sum(_p_0));
    return $Bool_and(($Bool_and(($Bool_and(($nat_is_zero(nat_chk(_x_0 + _x_1))), ($maybe_nat_is_none(_eh_0)))), ($Bool_not(_has_c_0)))), ($Bool_not(_bfc_0)));
  } else {
    const _b_1 = _c_0["border"];
    const _p_1 = _c_0["padding"];
    const _eh_1 = _c_0["explicit_block_size"];
    const _items_0 = _c_0["items"];
    const _x_2 = ($box_strut_block_sum(_b_1));
    const _x_3 = ($box_strut_block_sum(_p_1));
    return $Bool_and(($Bool_and(($nat_is_zero(nat_chk(_x_2 + _x_3))), ($maybe_nat_is_none(_eh_1)))), ($inline_item_is_empty_list(_items_0)));
  }
}

function $margin_strut_pos(_p_0) {
  return {$: "MStrut", "pos": _p_0, "neg": 0};
}

function $child_start_margin_strut(_c_0) {
  if (_c_0.$ === "BlockChild") {
    const _b_0 = _c_0["border"];
    const _p_0 = _c_0["padding"];
    const _m_0 = _c_0["margin"];
    const _bfc_0 = _c_0["is_new_bfc"];
    const _ist_0 = _c_0["inner_start_strut"];
    const _outer_0 = ($margin_strut_pos(($box_strut_block_start(_m_0))));
    const _x_0 = ($box_strut_block_start(_b_0));
    const _x_1 = ($box_strut_block_start(_p_0));
    const _x_2 = ($nat_pos(nat_chk(_x_0 + _x_1)));
    return $margin_strut_ite((_x_2 || _bfc_0), _outer_0, ($margin_strut_append(_outer_0, _ist_0)));
  } else {
    const _m_1 = _c_0["margin"];
    return {$: "MStrut", "pos": ($box_strut_block_start(_m_1)), "neg": 0};
  }
}

function $child_end_margin_strut(_c_0) {
  if (_c_0.$ === "BlockChild") {
    const _b_0 = _c_0["border"];
    const _p_0 = _c_0["padding"];
    const _m_0 = _c_0["margin"];
    const _eh_0 = _c_0["explicit_block_size"];
    const _bfc_0 = _c_0["is_new_bfc"];
    const _ien_0 = _c_0["inner_end_strut"];
    const _outer_0 = ($margin_strut_pos(($box_strut_block_end(_m_0))));
    const _x_0 = ($box_strut_block_end(_b_0));
    const _x_1 = ($box_strut_block_end(_p_0));
    const _x_2 = ($nat_pos(nat_chk(_x_0 + _x_1)));
    const _x_3 = (_x_2 || _bfc_0);
    const _x_4 = ($maybe_nat_is_some(_eh_0));
    return $margin_strut_ite((_x_3 || _x_4), _outer_0, ($margin_strut_append(_ien_0, _outer_0)));
  } else {
    const _m_1 = _c_0["margin"];
    return {$: "MStrut", "pos": ($box_strut_block_end(_m_1)), "neg": 0};
  }
}

function $child_inline_lines(_avail_inline_0, _c_0) {
  if (_c_0.$ === "BlockChild") {
    return {$: "StackedLines", "lines": {$: "Nil"}, "total_block_size": 0};
  } else {
    const _b_1 = _c_0["border"];
    const _p_1 = _c_0["padding"];
    const _m_1 = _c_0["margin"];
    const _ew_1 = _c_0["explicit_inline_size"];
    const _st_0 = _c_0["line_strut"];
    const _items_0 = _c_0["items"];
    const _x_0 = ($box_strut_inline_sum(_m_1));
    const _box_inline_0 = ($maybe_nat_get_or(_ew_1, (_avail_inline_0 < _x_0 ? 0 : _avail_inline_0 - _x_0)));
    const _x_1 = ($box_strut_inline_sum(_b_1));
    const _x_2 = ($box_strut_inline_sum(_p_1));
    const _x_3 = nat_chk(_x_1 + _x_2);
    const _content_inline_0 = (_box_inline_0 < _x_3 ? 0 : _box_inline_0 - _x_3);
    const _x_4 = ($box_strut_block_start(_b_1));
    const _x_5 = ($box_strut_block_start(_p_1));
    const _start_off_0 = nat_chk(_x_4 + _x_5);
    return $stack_line_boxes(($break_lines(_content_inline_0, _items_0)), _st_0, _start_off_0);
  }
}

function $child_border_box_block_size(_avail_inline_0, _c_0) {
  if (_c_0.$ === "BlockChild") {
    const _id_0 = _c_0["node_id"];
    const _b_0 = _c_0["border"];
    const _p_0 = _c_0["padding"];
    const _m_0 = _c_0["margin"];
    const _ew_0 = _c_0["explicit_inline_size"];
    const _eh_0 = _c_0["explicit_block_size"];
    const _bfc_0 = _c_0["is_new_bfc"];
    const _csz_0 = _c_0["content_block_size"];
    const _has_c_0 = _c_0["has_inflow_content"];
    const _ist_0 = _c_0["inner_start_strut"];
    const _ien_0 = _c_0["inner_end_strut"];
    const _x_0 = ($box_strut_block_end(_b_0));
    const _x_1 = ($box_strut_block_end(_p_0));
    const _x_2 = ($nat_pos(nat_chk(_x_0 + _x_1)));
    const _x_3 = (_x_2 || _bfc_0);
    const _x_4 = ($maybe_nat_is_some(_eh_0));
    const _has_end_edge_0 = (_x_3 || _x_4);
    const _trailing_0 = ($nat_ite(_has_end_edge_0, ($margin_strut_sum(_ien_0)), 0));
    const _x_5 = ($box_strut_block_sum(_b_0));
    const _x_6 = ($box_strut_block_sum(_p_0));
    const _bp_0 = nat_chk(_x_5 + _x_6);
    const _x_7 = nat_chk(_bp_0 + _csz_0);
    return $maybe_nat_get_or(_eh_0, ($nat_ite(($child_is_self_collapsing({$: "BlockChild", "node_id": _id_0, "border": _b_0, "padding": _p_0, "margin": _m_0, "explicit_inline_size": _ew_0, "explicit_block_size": _eh_0, "is_new_bfc": _bfc_0, "content_block_size": _csz_0, "has_inflow_content": _has_c_0, "inner_start_strut": _ist_0, "inner_end_strut": _ien_0})), 0, nat_chk(_x_7 + _trailing_0))));
  } else {
    const _id_1 = _c_0["node_id"];
    const _b_1 = _c_0["border"];
    const _p_1 = _c_0["padding"];
    const _m_1 = _c_0["margin"];
    const _ew_1 = _c_0["explicit_inline_size"];
    const _eh_1 = _c_0["explicit_block_size"];
    const _st_0 = _c_0["line_strut"];
    const _items_0 = _c_0["items"];
    const _stacked_0 = ($child_inline_lines(_avail_inline_0, {$: "InlineChild", "node_id": _id_1, "border": _b_1, "padding": _p_1, "margin": _m_1, "explicit_inline_size": _ew_1, "explicit_block_size": _eh_1, "line_strut": _st_0, "items": _items_0}));
    const _x_8 = ($box_strut_block_end(_p_1));
    const _x_9 = ($box_strut_block_end(_b_1));
    const _x_10 = ($stacked_lines_block_size(_stacked_0));
    const _x_11 = nat_chk(_x_8 + _x_9);
    return $maybe_nat_get_or(_eh_1, ($nat_ite(($child_is_self_collapsing({$: "InlineChild", "node_id": _id_1, "border": _b_1, "padding": _p_1, "margin": _m_1, "explicit_inline_size": _ew_1, "explicit_block_size": _eh_1, "line_strut": _st_0, "items": _items_0})), 0, nat_chk(_x_10 + _x_11))));
  }
}

function $child_state_fragments(_st_0) {
  const _frags_0 = _st_0["fragments"];
  return _frags_0;
}

function $child_state_bfc_resolved(_st_0) {
  const _res_0 = _st_0["bfc_resolved"];
  return _res_0;
}

function $child_state_first_resolved_strut(_st_0) {
  const _first_0 = _st_0["first_resolved_strut"];
  return _first_0;
}

function $child_state_logical_block_offset(_st_0) {
  const _pos_0 = _st_0["logical_block_offset"];
  return _pos_0;
}

function $child_state_margin_strut(_st_0) {
  const _strut_0 = _st_0["margin_strut"];
  return _strut_0;
}

function $layout_children(_cs_0, _avail_inline_0, _bfc_resolved_0, _pos_0, _strut_0) {
  if (_cs_0.$ === "Nil") {
    return {$: "ChildState", "fragments": {$: "Nil"}, "bfc_resolved": _bfc_resolved_0, "first_resolved_strut": _strut_0, "logical_block_offset": _pos_0, "margin_strut": _strut_0};
  } else {
    const _c_0 = _cs_0["head"];
    const _rest_0 = _cs_0["tail"];
    const _is_self_0 = ($child_is_self_collapsing(_c_0));
    const _start_strut_0 = ($margin_strut_append(_strut_0, ($child_start_margin_strut(_c_0))));
    const _end_strut_0 = ($child_end_margin_strut(_c_0));
    const _inline_sz_0 = ($child_resolve_inline_size(_avail_inline_0, _c_0));
    const _inline_off_0 = ($box_strut_inline_start(($child_margin(_c_0))));
    const _x_0 = ($margin_strut_sum(_start_strut_0));
    const _block_off_0 = ($nat_ite(_bfc_resolved_0, nat_chk(_pos_0 + _x_0), 0));
    const _blk_sz_0 = ($nat_ite(_is_self_0, 0, ($child_border_box_block_size(_avail_inline_0, _c_0))));
    const _lines_0 = ($line_frag_list_ite(_is_self_0, {$: "Nil"}, ($stacked_lines_list(($child_inline_lines(_avail_inline_0, _c_0))))));
    const _next_bfc_0 = ($bool_ite(_is_self_0, _bfc_resolved_0, true));
    const _next_pos_0 = ($nat_ite(_is_self_0, _pos_0, nat_chk(_block_off_0 + _blk_sz_0)));
    const _next_strut_0 = ($margin_strut_ite(_is_self_0, ($margin_strut_append(_start_strut_0, _end_strut_0)), _end_strut_0));
    const _tail_st_0 = ($layout_children(_rest_0, _avail_inline_0, _next_bfc_0, _next_pos_0, _next_strut_0));
    const _first_res_0 = ($margin_strut_ite(_is_self_0, ($child_state_first_resolved_strut(_tail_st_0)), ($margin_strut_ite(_bfc_resolved_0, _strut_0, _start_strut_0))));
    return {$: "ChildState", "fragments": {$: "Con", "head": {$: "ChildBoxFrag", "node_id": ($child_node_id(_c_0)), "offset": {$: "LOffset", "inline_offset": _inline_off_0, "block_offset": _block_off_0}, "border_box_size": {$: "LSize", "inline_size": _inline_sz_0, "block_size": _blk_sz_0}, "lines": _lines_0}, "tail": ($child_state_fragments(_tail_st_0))}, "bfc_resolved": ($child_state_bfc_resolved(_tail_st_0)), "first_resolved_strut": _first_res_0, "logical_block_offset": ($child_state_logical_block_offset(_tail_st_0)), "margin_strut": ($child_state_margin_strut(_tail_st_0))};
  }
}

function $layout_block(_space_0, _node_0) {
  const _avail_inline_0 = _space_0["available_inline_size"];
  const _bfc_line_off_0 = _space_0["bfc_line_offset"];
  const _bfc_block_off_0 = _space_0["bfc_block_offset"];
  const _space_strut_0 = _space_0["margin_strut"];
  const _space_bfc_0 = _space_0["is_new_bfc"];
  const _node_id_0 = _node_0["node_id"];
  const _border_0 = _node_0["border"];
  const _padding_0 = _node_0["padding"];
  const _margin_0 = _node_0["margin"];
  const _exp_inline_0 = _node_0["explicit_inline_size"];
  const _exp_block_0 = _node_0["explicit_block_size"];
  const _node_bfc_0 = _node_0["is_new_bfc"];
  const _children_0 = _node_0["children"];
  const _x_0 = ($box_strut_inline_sum(_margin_0));
  const _border_box_inline_0 = ($maybe_nat_get_or(_exp_inline_0, (_avail_inline_0 < _x_0 ? 0 : _avail_inline_0 - _x_0)));
  const _x_1 = ($box_strut_inline_sum(_border_0));
  const _x_2 = ($box_strut_inline_sum(_padding_0));
  const _x_3 = nat_chk(_x_1 + _x_2);
  const _child_avail_inline_0 = (_border_box_inline_0 < _x_3 ? 0 : _border_box_inline_0 - _x_3);
  const _x_4 = ($box_strut_block_start(_border_0));
  const _x_5 = ($box_strut_block_start(_padding_0));
  const _content_start_0 = nat_chk(_x_4 + _x_5);
  const _x_6 = ($nat_pos(_content_start_0));
  const _x_7 = (_x_6 || _space_bfc_0);
  const _has_start_edge_0 = (_x_7 || _node_bfc_0);
  const _init_pos_0 = ($nat_ite(_has_start_edge_0, _content_start_0, 0));
  const _init_strut_0 = ($margin_strut_ite(_has_start_edge_0, ($margin_strut_empty()), _space_strut_0));
  const _st_0 = ($layout_children(_children_0, _child_avail_inline_0, _has_start_edge_0, _init_pos_0, _init_strut_0));
  const _st_resolved_0 = ($child_state_bfc_resolved(_st_0));
  const _st_first_strut_0 = ($child_state_first_resolved_strut(_st_0));
  const _st_pos_0 = ($child_state_logical_block_offset(_st_0));
  const _st_strut_0 = ($child_state_margin_strut(_st_0));
  const _x_8 = ($box_strut_block_end(_padding_0));
  const _x_9 = ($box_strut_block_end(_border_0));
  const _content_end_0 = nat_chk(_x_8 + _x_9);
  const _x_10 = ($nat_pos(_content_end_0));
  const _x_11 = (_x_10 || _space_bfc_0);
  const _has_end_edge_0 = (_x_11 || _node_bfc_0);
  const _is_self_collapsing_container_0 = ($Bool_and(($Bool_and(($Bool_not(_st_resolved_0)), ($nat_is_zero(_content_end_0)))), ($maybe_nat_is_none(_exp_block_0))));
  const _x_12 = ($margin_strut_sum(_space_strut_0));
  const _x_13 = ($margin_strut_sum(_st_first_strut_0));
  const _x_14 = ($margin_strut_sum(_st_strut_0));
  const _block_off_0 = ($nat_ite(_st_resolved_0, ($nat_ite(_has_start_edge_0, nat_chk(_bfc_block_off_0 + _x_12), nat_chk(_bfc_block_off_0 + _x_13))), ($nat_ite(_is_self_collapsing_container_0, _bfc_block_off_0, nat_chk(_bfc_block_off_0 + _x_14)))));
  const _x_15 = ($margin_strut_sum(_st_strut_0));
  const _x_16 = nat_chk(_st_pos_0 + _x_15);
  const _intrinsic_0 = ($nat_ite(_st_resolved_0, ($nat_ite(_has_end_edge_0, nat_chk(_x_16 + _content_end_0), _st_pos_0)), ($nat_ite(_is_self_collapsing_container_0, 0, _content_end_0))));
  const _final_block_0 = ($nat_ite(_is_self_collapsing_container_0, 0, ($maybe_nat_get_or(_exp_block_0, _intrinsic_0))));
  const _bfc_off_0 = ($maybe_nat_ite(_is_self_collapsing_container_0, {$: "NoneNat"}, {$: "SomeNat", "val": _block_off_0}));
  const _x_17 = ($maybe_nat_is_some(_exp_block_0));
  const _out_strut_0 = ($margin_strut_ite(_st_resolved_0, ($margin_strut_ite((_has_end_edge_0 || _x_17), ($margin_strut_empty()), _st_strut_0)), ($margin_strut_ite(_is_self_collapsing_container_0, _st_strut_0, ($margin_strut_empty())))));
  return {$: "LResult", "fragment": {$: "BoxFrag", "node_id": _node_id_0, "offset": {$: "LOffset", "inline_offset": _bfc_line_off_0, "block_offset": _block_off_0}, "border_box_size": {$: "LSize", "inline_size": _border_box_inline_0, "block_size": _final_block_0}, "children": ($child_state_fragments(_st_0)), "lines": {$: "Nil"}}, "bfc_block_offset": _bfc_off_0, "end_margin_strut": _out_strut_0, "intrinsic_block_size": _intrinsic_0};
}

function $layout_result_intrinsic_block_size(_r_0) {
  const _intrinsic_0 = _r_0["intrinsic_block_size"];
  return _intrinsic_0;
}

function $layout_result_bfc_block_offset_or(_r_0, _fallback_0) {
  const _bfc_off_0 = _r_0["bfc_block_offset"];
  return $maybe_nat_get_or(_bfc_off_0, _fallback_0);
}

function $layout_result_end_margin_pos(_r_0) {
  const _t_0 = _r_0["end_margin_strut"];
  const _pos_0 = _t_0["pos"];
  return _pos_0;
}

function $collapsed_flow_block_size_from(_cs_0, _avail_inline_0, _prev_strut_0) {
  if (_cs_0.$ === "Nil") {
    return $margin_strut_sum(_prev_strut_0);
  } else {
    const _c_0 = _cs_0["head"];
    const _rest_0 = _cs_0["tail"];
    const _collapsed_0 = ($margin_strut_sum(($margin_strut_append(_prev_strut_0, ($child_start_margin_strut(_c_0))))));
    const _x_0 = ($child_border_box_block_size(_avail_inline_0, _c_0));
    const _x_1 = nat_chk(_collapsed_0 + _x_0);
    const _x_2 = ($collapsed_flow_block_size_from(_rest_0, _avail_inline_0, ($child_end_margin_strut(_c_0))));
    return nat_chk(_x_1 + _x_2);
  }
}

function $total_collapsed_flow_block_size(_avail_inline_0, _cs_0) {
  return $collapsed_flow_block_size_from(_cs_0, _avail_inline_0, ($margin_strut_empty()));
}

function $Bool_and(_a_0, _b_0) {
  if (!_a_0) {
    return false;
  } else {
    return _b_0;
  }
}

function $Bool_not(_b_0) {
  if (!_b_0) {
    return true;
  } else {
    return false;
  }
}
export default {
  "bool_ite": run_lib((a0,a1,a2) => run_loop($bool_ite(a0,a1,a2)), 3),
  "nat_ite": run_lib((a0,a1,a2) => run_loop($nat_ite(a0,nat_in(a1),nat_in(a2))), 3),
  "box_strut_zero": run_lib(() => run_loop($box_strut_zero()), 0),
  "box_strut_inline_start": run_lib((a0) => run_loop($box_strut_inline_start(a0)), 1),
  "box_strut_inline_end": run_lib((a0) => run_loop($box_strut_inline_end(a0)), 1),
  "box_strut_block_start": run_lib((a0) => run_loop($box_strut_block_start(a0)), 1),
  "box_strut_block_end": run_lib((a0) => run_loop($box_strut_block_end(a0)), 1),
  "box_strut_inline_sum": run_lib((a0) => run_loop($box_strut_inline_sum(a0)), 1),
  "box_strut_block_sum": run_lib((a0) => run_loop($box_strut_block_sum(a0)), 1),
  "box_strut_add": run_lib((a0,a1) => run_loop($box_strut_add(a0,a1)), 2),
  "margin_strut_ite": run_lib((a0,a1,a2) => run_loop($margin_strut_ite(a0,a1,a2)), 3),
  "margin_strut_empty": run_lib(() => run_loop($margin_strut_empty()), 0),
  "margin_strut_append": run_lib((a0,a1) => run_loop($margin_strut_append(a0,a1)), 2),
  "margin_strut_sum": run_lib((a0) => run_loop($margin_strut_sum(a0)), 1),
  "margin_strut_apply_offset": run_lib((a0,a1) => run_loop($margin_strut_apply_offset(nat_in(a0),a1)), 2),
  "font_height_zero": run_lib(() => run_loop($font_height_zero()), 0),
  "font_height_ascent": run_lib((a0) => run_loop($font_height_ascent(a0)), 1),
  "font_height_descent": run_lib((a0) => run_loop($font_height_descent(a0)), 1),
  "font_height_line_height": run_lib((a0) => run_loop($font_height_line_height(a0)), 1),
  "font_height_merge": run_lib((a0,a1) => run_loop($font_height_merge(a0,a1)), 2),
  "maybe_nat_ite": run_lib((a0,a1,a2) => run_loop($maybe_nat_ite(a0,a1,a2)), 3),
  "maybe_nat_get_or": run_lib((a0,a1) => run_loop($maybe_nat_get_or(a0,nat_in(a1))), 2),
  "maybe_nat_is_some": run_lib((a0) => run_loop($maybe_nat_is_some(a0)), 1),
  "maybe_nat_is_none": run_lib((a0) => run_loop($maybe_nat_is_none(a0)), 1),
  "nat_le": run_lib((a0,a1) => run_loop($nat_le(nat_in(a0),nat_in(a1))), 2),
  "nat_is_zero": run_lib((a0) => run_loop($nat_is_zero(nat_in(a0))), 1),
  "nat_pos": run_lib((a0) => run_loop($nat_pos(nat_in(a0))), 1),
  "inline_item_id": run_lib((a0) => run_loop($inline_item_id(a0)), 1),
  "inline_item_raw_inline_size": run_lib((a0) => run_loop($inline_item_raw_inline_size(a0)), 1),
  "inline_item_font_height": run_lib((a0) => run_loop($inline_item_font_height(a0)), 1),
  "inline_item_is_empty_list": run_lib((a0) => run_loop($inline_item_is_empty_list(a0)), 1),
  "take_line_aux_choose": run_lib((a0,a1,a2,a3,a4,a5) => run_loop($take_line_aux_choose(a0,a1,nat_in(a2),nat_in(a3),a4,a5)), 6),
  "take_line_aux": run_lib((a0,a1,a2,a3,a4) => run_loop($take_line_aux(a0,nat_in(a1),nat_in(a2),nat_in(a3),nat_in(a4))), 5),
  "take_line_wrap": run_lib((a0,a1) => run_loop($take_line_wrap(a0,a1)), 2),
  "take_line": run_lib((a0,a1,a2) => run_loop($take_line(nat_in(a0),a1,a2)), 3),
  "take_line_info": run_lib((a0) => run_loop($take_line_info(a0)), 1),
  "take_line_rem": run_lib((a0) => run_loop($take_line_rem(a0)), 1),
  "inline_item_list_len": run_lib((a0) => run_loop($inline_item_list_len(a0)), 1),
  "break_lines_fuel": run_lib((a0,a1,a2) => run_loop($break_lines_fuel(nat_in(a0),nat_in(a1),a2)), 3),
  "break_lines": run_lib((a0,a1) => run_loop($break_lines(nat_in(a0),a1)), 2),
  "line_info_items": run_lib((a0) => run_loop($line_info_items(a0)), 1),
  "line_info_inline_size": run_lib((a0) => run_loop($line_info_inline_size(a0)), 1),
  "line_info_non_break_count": run_lib((a0) => run_loop($line_info_non_break_count(a0)), 1),
  "line_info_list_len": run_lib((a0) => run_loop($line_info_list_len(a0)), 1),
  "line_info_head_inline_size": run_lib((a0) => run_loop($line_info_head_inline_size(a0)), 1),
  "line_info_head_non_break_count": run_lib((a0) => run_loop($line_info_head_non_break_count(a0)), 1),
  "inline_item_append": run_lib((a0,a1) => run_loop($inline_item_append(a0,a1)), 2),
  "accumulate_line_metrics": run_lib((a0,a1) => run_loop($accumulate_line_metrics(a0,a1)), 2),
  "place_line_items": run_lib((a0,a1,a2) => run_loop($place_line_items(a0,a1,nat_in(a2))), 3),
  "box_stack_active": run_lib((a0) => run_loop($box_stack_active(a0)), 1),
  "box_stack_list": run_lib((a0) => run_loop($box_stack_list(a0)), 1),
  "step_box_state_stack": run_lib((a0,a1,a2) => run_loop($step_box_state_stack(a0,a1,a2)), 3),
  "run_box_state_stack": run_lib((a0,a1,a2) => run_loop($run_box_state_stack(a0,a1,a2)), 3),
  "flush_box_state_stack": run_lib((a0,a1) => run_loop($flush_box_state_stack(a0,a1)), 2),
  "apply_box_state_stack": run_lib((a0,a1) => run_loop($apply_box_state_stack(a0,a1)), 2),
  "placed_item_block_offset": run_lib((a0) => run_loop($placed_item_block_offset(a0)), 1),
  "placed_item_block_size": run_lib((a0) => run_loop($placed_item_block_size(a0)), 1),
  "placed_item_head_block_offset": run_lib((a0) => run_loop($placed_item_head_block_offset(a0)), 1),
  "placed_item_head_block_size": run_lib((a0) => run_loop($placed_item_head_block_size(a0)), 1),
  "line_frag_metrics": run_lib((a0) => run_loop($line_frag_metrics(a0)), 1),
  "line_frag_items": run_lib((a0) => run_loop($line_frag_items(a0)), 1),
  "line_frag_block_offset": run_lib((a0) => run_loop($line_frag_block_offset(a0)), 1),
  "line_frag_list_len": run_lib((a0) => run_loop($line_frag_list_len(a0)), 1),
  "line_frag_head_block_offset": run_lib((a0) => run_loop($line_frag_head_block_offset(a0)), 1),
  "line_frag_second_block_offset": run_lib((a0) => run_loop($line_frag_second_block_offset(a0)), 1),
  "create_line_box": run_lib((a0,a1) => run_loop($create_line_box(a0,a1)), 2),
  "line_frag_list_ite": run_lib((a0,a1,a2) => run_loop($line_frag_list_ite(a0,a1,a2)), 3),
  "line_frag_with_block_offset": run_lib((a0,a1) => run_loop($line_frag_with_block_offset(nat_in(a0),a1)), 2),
  "line_frag_line_height": run_lib((a0) => run_loop($line_frag_line_height(a0)), 1),
  "stacked_lines_list": run_lib((a0) => run_loop($stacked_lines_list(a0)), 1),
  "stacked_lines_block_size": run_lib((a0) => run_loop($stacked_lines_block_size(a0)), 1),
  "stack_line_boxes": run_lib((a0,a1,a2) => run_loop($stack_line_boxes(a0,a1,nat_in(a2))), 3),
  "child_node_id": run_lib((a0) => run_loop($child_node_id(a0)), 1),
  "child_margin": run_lib((a0) => run_loop($child_margin(a0)), 1),
  "child_resolve_inline_size": run_lib((a0,a1) => run_loop($child_resolve_inline_size(nat_in(a0),a1)), 2),
  "child_is_self_collapsing": run_lib((a0) => run_loop($child_is_self_collapsing(a0)), 1),
  "margin_strut_pos": run_lib((a0) => run_loop($margin_strut_pos(nat_in(a0))), 1),
  "child_start_margin_strut": run_lib((a0) => run_loop($child_start_margin_strut(a0)), 1),
  "child_end_margin_strut": run_lib((a0) => run_loop($child_end_margin_strut(a0)), 1),
  "child_inline_lines": run_lib((a0,a1) => run_loop($child_inline_lines(nat_in(a0),a1)), 2),
  "child_border_box_block_size": run_lib((a0,a1) => run_loop($child_border_box_block_size(nat_in(a0),a1)), 2),
  "child_state_fragments": run_lib((a0) => run_loop($child_state_fragments(a0)), 1),
  "child_state_bfc_resolved": run_lib((a0) => run_loop($child_state_bfc_resolved(a0)), 1),
  "child_state_first_resolved_strut": run_lib((a0) => run_loop($child_state_first_resolved_strut(a0)), 1),
  "child_state_logical_block_offset": run_lib((a0) => run_loop($child_state_logical_block_offset(a0)), 1),
  "child_state_margin_strut": run_lib((a0) => run_loop($child_state_margin_strut(a0)), 1),
  "layout_children": run_lib((a0,a1,a2,a3,a4) => run_loop($layout_children(a0,nat_in(a1),a2,nat_in(a3),a4)), 5),
  "layout_block": run_lib((a0,a1) => run_loop($layout_block(a0,a1)), 2),
  "layout_result_intrinsic_block_size": run_lib((a0) => run_loop($layout_result_intrinsic_block_size(a0)), 1),
  "layout_result_bfc_block_offset_or": run_lib((a0,a1) => run_loop($layout_result_bfc_block_offset_or(a0,nat_in(a1))), 2),
  "layout_result_end_margin_pos": run_lib((a0) => run_loop($layout_result_end_margin_pos(a0)), 1),
  "collapsed_flow_block_size_from": run_lib((a0,a1,a2) => run_loop($collapsed_flow_block_size_from(a0,nat_in(a1),a2)), 3),
  "total_collapsed_flow_block_size": run_lib((a0,a1) => run_loop($total_collapsed_flow_block_size(nat_in(a0),a1)), 2),
};
