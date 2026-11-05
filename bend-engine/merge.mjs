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
  const d = Number(s), a = Math.abs(d), f = Math.fround(a), g = 2 * a - Math.min(f, 340282366920938500000000000000000000000);
  if (g === f || Math.fround(g) !== g || g === 1 / 0)
    return Math.sign(d) * f;
  let k = 0;
  while (a * 2 ** k % 1 !== 0)
    k += 1;
  const [, i, r, e] = /(\d*)\.?(\d*)(?:e([+-]?\d+))?$/i.exec(s), n = Number(e ?? 0) - r.length, x = BigInt(i + r) * 2n ** BigInt(k) * 10n ** BigInt(Math.max(n, 0)), y = BigInt(a * 2 ** k) * 10n ** BigInt(Math.max(-n, 0));
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
  // A match starts at a Char, not inside a packed U32 code.
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
const io_file_append = new Set();

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

function $cmp_of(_p_0) {
  const _t_0 = _p_0["fst"];
  const _c_0 = _p_0["snd"];
  return _c_0;
}

function $skey_cmp(_a_0, _b_0) {
  return $cmp_of($$String_cmp(_a_0, _b_0));
}

function $lp_max(_a_0, _b_0) {
  const _c1_0 = _a_0["crowns"];
  const _n1_0 = _a_0["attempts"];
  const _b1_0 = _a_0["best"];
  const _p1_0 = _a_0["played"];
  const _c2_0 = _b_0["crowns"];
  const _n2_0 = _b_0["attempts"];
  const _b2_0 = _b_0["best"];
  const _p2_0 = _b_0["played"];
  return {$: "Lp", "crowns": (_c1_0 > _c2_0 ? _c1_0 : _c2_0), "attempts": (_n1_0 > _n2_0 ? _n1_0 : _n2_0), "best": (_b1_0 > _b2_0 ? _b1_0 : _b2_0), "played": (_p1_0 > _p2_0 ? _p1_0 : _p2_0)};
}

function $last_or0(_m_0) {
  if (_m_0.$ === "None") {
    return 0;
  } else {
    const _x_0 = _m_0["value"];
    return _x_0;
  }
}

function $card_pick(_c_last_0, _c_reps_0, _c_due_0, _a_0, _b_0) {
  if (_c_last_0.$ === "LT") {
    return _b_0;
  } else if (_c_last_0.$ === "GT") {
    return _a_0;
  } else {
    if (_c_reps_0.$ === "LT") {
      return _b_0;
    } else if (_c_reps_0.$ === "GT") {
      return _a_0;
    } else {
      if (_c_due_0.$ === "LT") {
        return _b_0;
      } else if (_c_due_0.$ === "GT") {
        return _a_0;
      } else {
        return _a_0;
      }
    }
  }
}

function $card_merge(_a_0, _b_0) {
  const _i1_0 = _a_0["id"];
  const _l1_0 = _a_0["lessonId"];
  const _v1_0 = _a_0["interval"];
  const _e1_0 = _a_0["ease"];
  const _d1_0 = _a_0["due"];
  const _s1_0 = _a_0["lapses"];
  const _r1_0 = _a_0["reps"];
  const _t1_0 = _a_0["last"];
  const _i2_0 = _b_0["id"];
  const _l2_0 = _b_0["lessonId"];
  const _v2_0 = _b_0["interval"];
  const _e2_0 = _b_0["ease"];
  const _d2_0 = _b_0["due"];
  const _s2_0 = _b_0["lapses"];
  const _r2_0 = _b_0["reps"];
  const _t2_0 = _b_0["last"];
  const _x_0 = $$last_or0(_t1_0);
  const _x_1 = $$last_or0(_t2_0);
  return $card_pick(cmp_new(_x_0, _x_1), cmp_new(_r1_0, _r2_0), cmp_new(_d1_0, _d2_0), {$: "Card", "id": _i1_0, "lessonId": _l1_0, "interval": _v1_0, "ease": _e1_0, "due": _d1_0, "lapses": _s1_0, "reps": _r1_0, "last": _t1_0}, {$: "Card", "id": _i2_0, "lessonId": _l2_0, "interval": _v2_0, "ease": _e2_0, "due": _d2_0, "lapses": _s2_0, "reps": _r2_0, "last": _t2_0});
}

function $lins_c(_t_0, _c_0, _e_0, _h_0) {
  if (_t_0.$ === "Nil") {
    if (_c_0.$ === "LT") {
      return {$: "Con", "head": _e_0, "tail": {$: "Con", "head": _h_0, "tail": {$: "Nil"}}};
    } else if (_c_0.$ === "EQ") {
      const _ve_0 = _e_0["val"];
      const _kh_0 = _h_0["key"];
      const _vh_0 = _h_0["val"];
      return {$: "Con", "head": {$: "LEntry", "key": _kh_0, "val": $$lp_max(_vh_0, _ve_0)}, "tail": {$: "Nil"}};
    } else {
      return {$: "Con", "head": _h_0, "tail": {$: "Con", "head": _e_0, "tail": {$: "Nil"}}};
    }
  } else {
    const _t_1 = _t_0["head"];
    const _k2_0 = _t_1["key"];
    const _v2_0 = _t_1["val"];
    const _t2_0 = _t_0["tail"];
    if (_c_0.$ === "LT") {
      return {$: "Con", "head": _e_0, "tail": {$: "Con", "head": _h_0, "tail": {$: "Con", "head": {$: "LEntry", "key": _k2_0, "val": _v2_0}, "tail": _t2_0}}};
    } else if (_c_0.$ === "EQ") {
      const _ve_1 = _e_0["val"];
      const _kh_1 = _h_0["key"];
      const _vh_1 = _h_0["val"];
      return {$: "Con", "head": {$: "LEntry", "key": _kh_1, "val": $$lp_max(_vh_1, _ve_1)}, "tail": {$: "Con", "head": {$: "LEntry", "key": _k2_0, "val": _v2_0}, "tail": _t2_0}};
    } else {
      const _ke_2 = _e_0["key"];
      const _ve_2 = _e_0["val"];
      return {$: "Con", "head": _h_0, "tail": $$lins_c(_t2_0, $$skey_cmp(_ke_2, _k2_0), {$: "LEntry", "key": _ke_2, "val": _ve_2}, {$: "LEntry", "key": _k2_0, "val": _v2_0})};
    }
  }
}

function $lins(_e_0, _s_0) {
  const _ke_0 = _e_0["key"];
  const _ve_0 = _e_0["val"];
  if (_s_0.$ === "Nil") {
    return {$: "Con", "head": {$: "LEntry", "key": _ke_0, "val": _ve_0}, "tail": {$: "Nil"}};
  } else {
    const _t_0 = _s_0["head"];
    const _kh_0 = _t_0["key"];
    const _vh_0 = _t_0["val"];
    const _t_1 = _s_0["tail"];
    return $lins_c(_t_1, $$skey_cmp(_ke_0, _kh_0), {$: "LEntry", "key": _ke_0, "val": _ve_0}, {$: "LEntry", "key": _kh_0, "val": _vh_0});
  }
}

function $lfold($0, $1) {
  for (;;) {
    {
      const _xs_0 = $0;
      const _acc_0 = $1;
      if (_xs_0.$ === "Nil") {
        return _acc_0;
      } else {
        const _h_0 = _xs_0["head"];
        const _t_0 = _xs_0["tail"];
        $0 = _t_0;
        $1 = $$lins(_h_0, _acc_0);
        continue;
      }
    }
  }
}

function $merge_lessons(_a_0, _b_0) {
  return $lfold(_b_0, $$lfold(_a_0, {$: "Nil"}));
}

function $cins_c(_t_0, _c_0, _e_0, _h_0) {
  if (_t_0.$ === "Nil") {
    if (_c_0.$ === "LT") {
      return {$: "Con", "head": _e_0, "tail": {$: "Con", "head": _h_0, "tail": {$: "Nil"}}};
    } else if (_c_0.$ === "EQ") {
      const _ve_0 = _e_0["val"];
      const _kh_0 = _h_0["key"];
      const _vh_0 = _h_0["val"];
      return {$: "Con", "head": {$: "CEntry", "key": _kh_0, "val": $$card_merge(_vh_0, _ve_0)}, "tail": {$: "Nil"}};
    } else {
      return {$: "Con", "head": _h_0, "tail": {$: "Con", "head": _e_0, "tail": {$: "Nil"}}};
    }
  } else {
    const _t_1 = _t_0["head"];
    const _k2_0 = _t_1["key"];
    const _v2_0 = _t_1["val"];
    const _t2_0 = _t_0["tail"];
    if (_c_0.$ === "LT") {
      return {$: "Con", "head": _e_0, "tail": {$: "Con", "head": _h_0, "tail": {$: "Con", "head": {$: "CEntry", "key": _k2_0, "val": _v2_0}, "tail": _t2_0}}};
    } else if (_c_0.$ === "EQ") {
      const _ve_1 = _e_0["val"];
      const _kh_1 = _h_0["key"];
      const _vh_1 = _h_0["val"];
      return {$: "Con", "head": {$: "CEntry", "key": _kh_1, "val": $$card_merge(_vh_1, _ve_1)}, "tail": {$: "Con", "head": {$: "CEntry", "key": _k2_0, "val": _v2_0}, "tail": _t2_0}};
    } else {
      const _ke_2 = _e_0["key"];
      const _ve_2 = _e_0["val"];
      return {$: "Con", "head": _h_0, "tail": $$cins_c(_t2_0, $$skey_cmp(_ke_2, _k2_0), {$: "CEntry", "key": _ke_2, "val": _ve_2}, {$: "CEntry", "key": _k2_0, "val": _v2_0})};
    }
  }
}

function $cins(_e_0, _s_0) {
  const _ke_0 = _e_0["key"];
  const _ve_0 = _e_0["val"];
  if (_s_0.$ === "Nil") {
    return {$: "Con", "head": {$: "CEntry", "key": _ke_0, "val": _ve_0}, "tail": {$: "Nil"}};
  } else {
    const _t_0 = _s_0["head"];
    const _kh_0 = _t_0["key"];
    const _vh_0 = _t_0["val"];
    const _t_1 = _s_0["tail"];
    return $cins_c(_t_1, $$skey_cmp(_ke_0, _kh_0), {$: "CEntry", "key": _ke_0, "val": _ve_0}, {$: "CEntry", "key": _kh_0, "val": _vh_0});
  }
}

function $cfold($0, $1) {
  for (;;) {
    {
      const _xs_0 = $0;
      const _acc_0 = $1;
      if (_xs_0.$ === "Nil") {
        return _acc_0;
      } else {
        const _h_0 = _xs_0["head"];
        const _t_0 = _xs_0["tail"];
        $0 = _t_0;
        $1 = $$cins(_h_0, _acc_0);
        continue;
      }
    }
  }
}

function $merge_srs(_a_0, _b_0) {
  return $cfold(_b_0, $$cfold(_a_0, {$: "Nil"}));
}

function $xins_c(_t_0, _c_0, _e_0, _h_0) {
  if (_t_0.$ === "Nil") {
    if (_c_0.$ === "LT") {
      return {$: "Con", "head": _e_0, "tail": {$: "Con", "head": _h_0, "tail": {$: "Nil"}}};
    } else if (_c_0.$ === "EQ") {
      const _ve_0 = _e_0["val"];
      const _kh_0 = _h_0["key"];
      const _vh_0 = _h_0["val"];
      return {$: "Con", "head": {$: "XEntry", "key": _kh_0, "val": (_vh_0 > _ve_0 ? _vh_0 : _ve_0)}, "tail": {$: "Nil"}};
    } else {
      return {$: "Con", "head": _h_0, "tail": {$: "Con", "head": _e_0, "tail": {$: "Nil"}}};
    }
  } else {
    const _t_1 = _t_0["head"];
    const _k2_0 = _t_1["key"];
    const _v2_0 = _t_1["val"];
    const _t2_0 = _t_0["tail"];
    if (_c_0.$ === "LT") {
      return {$: "Con", "head": _e_0, "tail": {$: "Con", "head": _h_0, "tail": {$: "Con", "head": {$: "XEntry", "key": _k2_0, "val": _v2_0}, "tail": _t2_0}}};
    } else if (_c_0.$ === "EQ") {
      const _ve_1 = _e_0["val"];
      const _kh_1 = _h_0["key"];
      const _vh_1 = _h_0["val"];
      return {$: "Con", "head": {$: "XEntry", "key": _kh_1, "val": (_vh_1 > _ve_1 ? _vh_1 : _ve_1)}, "tail": {$: "Con", "head": {$: "XEntry", "key": _k2_0, "val": _v2_0}, "tail": _t2_0}};
    } else {
      const _ke_2 = _e_0["key"];
      const _ve_2 = _e_0["val"];
      return {$: "Con", "head": _h_0, "tail": $$xins_c(_t2_0, $$skey_cmp(_ke_2, _k2_0), {$: "XEntry", "key": _ke_2, "val": _ve_2}, {$: "XEntry", "key": _k2_0, "val": _v2_0})};
    }
  }
}

function $xins(_e_0, _s_0) {
  const _ke_0 = _e_0["key"];
  const _ve_0 = _e_0["val"];
  if (_s_0.$ === "Nil") {
    return {$: "Con", "head": {$: "XEntry", "key": _ke_0, "val": _ve_0}, "tail": {$: "Nil"}};
  } else {
    const _t_0 = _s_0["head"];
    const _kh_0 = _t_0["key"];
    const _vh_0 = _t_0["val"];
    const _t_1 = _s_0["tail"];
    return $xins_c(_t_1, $$skey_cmp(_ke_0, _kh_0), {$: "XEntry", "key": _ke_0, "val": _ve_0}, {$: "XEntry", "key": _kh_0, "val": _vh_0});
  }
}

function $xfold($0, $1) {
  for (;;) {
    {
      const _xs_0 = $0;
      const _acc_0 = $1;
      if (_xs_0.$ === "Nil") {
        return _acc_0;
      } else {
        const _h_0 = _xs_0["head"];
        const _t_0 = _xs_0["tail"];
        $0 = _t_0;
        $1 = $$xins(_h_0, _acc_0);
        continue;
      }
    }
  }
}

function $merge_xp(_a_0, _b_0) {
  return $xfold(_b_0, $$xfold(_a_0, {$: "Nil"}));
}

function $xsum(_xs_0) {
  if (_xs_0.$ === "Nil") {
    return 0;
  } else {
    const _t_0 = _xs_0["head"];
    const _v_0 = _t_0["val"];
    const _t_1 = _xs_0["tail"];
    const _x_0 = $$xsum(_t_1);
    return nat_chk(_v_0 + _x_0);
  }
}

function $merge_state(_a_0, _b_0) {
  const _la_0 = _a_0["lessons"];
  const _ca_0 = _a_0["srs"];
  const _xa_0 = _a_0["xpByDay"];
  const _lb_0 = _b_0["lessons"];
  const _cb_0 = _b_0["srs"];
  const _xb_0 = _b_0["xpByDay"];
  const _mx_0 = $$merge_xp(_xa_0, _xb_0);
  return {$: "Out", "lessons": $$merge_lessons(_la_0, _lb_0), "srs": $$merge_srs(_ca_0, _cb_0), "xpByDay": _mx_0, "xp": $$xsum(_mx_0)};
}

function $String_cmp(_a_0, _b_0) {
  if (_a_0 === "") {
    if (_b_0 === "") {
      return {$: "Tuple", "fst": {$: "Tuple", "fst": "", "snd": ""}, "snd": {$: "EQ"}};
    } else {
      const _h_0 = _b_0.slice(0, char_len(_b_0));
      const _t_0 = _b_0.slice(char_len(_b_0));
      return {$: "Tuple", "fst": {$: "Tuple", "fst": "", "snd": (_h_0 + _t_0)}, "snd": {$: "LT"}};
    }
  } else {
    const _h_1 = _a_0.slice(0, char_len(_a_0));
    const _t_1 = _a_0.slice(char_len(_a_0));
    if (_b_0 === "") {
      return {$: "Tuple", "fst": {$: "Tuple", "fst": (_h_1 + _t_1), "snd": ""}, "snd": {$: "GT"}};
    } else {
      const _h2_0 = _b_0.slice(0, char_len(_b_0));
      const _t2_0 = _b_0.slice(char_len(_b_0));
      return $String_cmp_fin(_t_1, _t2_0, $$Char_cmp(_h_1, _h2_0));
    }
  }
}

function $String_cmp_fin(_t1_0, _t2_0, _hc_0) {
  const _t_0 = _hc_0["fst"];
  const _h1b_0 = _t_0["fst"];
  const _h2b_0 = _t_0["snd"];
  const _t_1 = _hc_0["snd"];
  if (_t_1.$ === "LT") {
    return {$: "Tuple", "fst": {$: "Tuple", "fst": (_h1b_0 + _t1_0), "snd": (_h2b_0 + _t2_0)}, "snd": {$: "LT"}};
  } else if (_t_1.$ === "EQ") {
    return $String_cmp_rec(_h1b_0, _h2b_0, $$String_cmp(_t1_0, _t2_0));
  } else {
    return {$: "Tuple", "fst": {$: "Tuple", "fst": (_h1b_0 + _t1_0), "snd": (_h2b_0 + _t2_0)}, "snd": {$: "GT"}};
  }
}

function $Char_cmp(_a_0, _b_0) {
  const _x_0 = char_code(_a_0);
  const _y_0 = char_code(_b_0);
  return {$: "Tuple", "fst": {$: "Tuple", "fst": _a_0, "snd": _b_0}, "snd": cmp_new(_x_0, _y_0)};
}

function $String_cmp_rec(_h1b_0, _h2b_0, _rr_0) {
  const _t_0 = _rr_0["fst"];
  const _t1b_0 = _t_0["fst"];
  const _t2b_0 = _t_0["snd"];
  const _r_0 = _rr_0["snd"];
  return {$: "Tuple", "fst": {$: "Tuple", "fst": (_h1b_0 + _t1b_0), "snd": (_h2b_0 + _t2b_0)}, "snd": _r_0};
}

const $$String_cmp = $String_cmp;
const $$last_or0 = $last_or0;
const $$lp_max = $lp_max;
const $$skey_cmp = $skey_cmp;
const $$lins_c = $lins_c;
const $$lins = $lins;
const $$lfold = $lfold;
const $$card_merge = $card_merge;
const $$cins_c = $cins_c;
const $$cins = $cins;
const $$cfold = $cfold;
const $$xins_c = $xins_c;
const $$xins = $xins;
const $$xfold = $xfold;
const $$xsum = $xsum;
const $$merge_xp = $merge_xp;
const $$merge_lessons = $merge_lessons;
const $$merge_srs = $merge_srs;
const $$Char_cmp = $Char_cmp;export default {
  "cmp_of": run_lib((a0) => run_loop($cmp_of(a0)), 1),
  "skey_cmp": run_lib((a0,a1) => run_loop($skey_cmp(str_in(a0),str_in(a1))), 2),
  "lp_max": run_lib((a0,a1) => run_loop($lp_max(a0,a1)), 2),
  "last_or0": run_lib((a0) => run_loop($last_or0(a0)), 1),
  "card_pick": run_lib((a0,a1,a2,a3,a4) => run_loop($card_pick(a0,a1,a2,a3,a4)), 5),
  "card_merge": run_lib((a0,a1) => run_loop($card_merge(a0,a1)), 2),
  "lins_c": run_lib((a0,a1,a2,a3) => run_loop($lins_c(a0,a1,a2,a3)), 4),
  "lins": run_lib((a0,a1) => run_loop($lins(a0,a1)), 2),
  "lfold": run_lib((a0,a1) => run_loop($lfold(a0,a1)), 2),
  "merge_lessons": run_lib((a0,a1) => run_loop($merge_lessons(a0,a1)), 2),
  "cins_c": run_lib((a0,a1,a2,a3) => run_loop($cins_c(a0,a1,a2,a3)), 4),
  "cins": run_lib((a0,a1) => run_loop($cins(a0,a1)), 2),
  "cfold": run_lib((a0,a1) => run_loop($cfold(a0,a1)), 2),
  "merge_srs": run_lib((a0,a1) => run_loop($merge_srs(a0,a1)), 2),
  "xins_c": run_lib((a0,a1,a2,a3) => run_loop($xins_c(a0,a1,a2,a3)), 4),
  "xins": run_lib((a0,a1) => run_loop($xins(a0,a1)), 2),
  "xfold": run_lib((a0,a1) => run_loop($xfold(a0,a1)), 2),
  "merge_xp": run_lib((a0,a1) => run_loop($merge_xp(a0,a1)), 2),
  "xsum": run_lib((a0) => run_loop($xsum(a0)), 1),
  "merge_state": run_lib((a0,a1) => run_loop($merge_state(a0,a1)), 2),
};
