# bend-json

A JSON library in pure Bend 2 (checked with Bend 2.0.39): an RFC 8259 parser,
compact and pretty printers, and exact decimal numbers. Its round-trip laws
are machine-checked: `bend PROOF.bend` prints `ALL PROOFS CHECK`. There is no
`@unsafe` code and no foreign code anywhere.

```
decimal.bend  exact numbers (Num), normalization, printing, conversions
bignat.bend   big naturals in 16-bit limbs (used for exact to_f32)
value.bend    the Json value, get / at / is_eq / depth / is_norm
text.bend     string escaping and the string decoder
parser.bend   parse, parse_with, parse_number
printer.bend  print, pretty, print_number, print_par
utf8.bend     strict UTF-8 bytes -> String (for reading files)
LAWS.bend     the laws        PROOF.bend  their proofs   SPEC.bend  law helpers
tests.bend    the test table  corpus.bend JSONTestSuite runner
bench.bend    timings         example.bend usage         gen_bench.py bench input
```

## API

```python
import ./value.bend as V
import ./parser.bend as P
import ./printer.bend as Pr
import ./decimal.bend as D

P.parse(s)            # Result<Err, Json>: Done{v} or Fail{Err{pos, msg}}
P.parse_with(max, s)  # same, with a nesting limit (parse uses 512)
P.parse_number(s)     # Maybe<Num>: s is exactly one JSON number
Pr.print(v)           # compact text, no whitespace
Pr.pretty(ind, v)     # one item per line, ind spaces per level
Pr.print_number(n)
V.Json.get(v, key)    # the LAST member named key (as JavaScript does)
V.Json.at(v, i)       # the i-th array item
D.Num.to_u32(n), D.Num.to_nat(n)    # Maybe: None if out of range or not an integer
D.Num.from_u32(x), D.Num.from_nat(x)
D.Num.to_f32(n)       # nearest F32, ties to even (lossy)
D.Num.is_eq(a, b)     # numeric equality of normalized numbers
```

The value type:

```python
type Json is Data:
  JNull{}  JBool{value: Bool}  JNum{value: D.Num}  JStr{value: String}
  JArr{items: List<&2, Json>}
  JObj{items: List<&2, Member>}      # Mem{key: String, value: Json}, in order, duplicates kept
```

`example.bend` (run `bend example.bend`) prints:

```
{"a":1,"price":19.99,"a":[true,null,"é"]}
{
  "a": 1,
  "price": 19.99,
  "a": [
    true,
    null,
    "é"
  ]
}
last "a": Some([true,null,"é"])
error at 6: expected a value                  <- "[1, 2,]": trailing comma, char 6
error at 1: maximum nesting depth exceeded    <- parse_with(1n, "[[1]]")
199.9 exact; as U32: None; as F32: 199.9      <- "19.990e1"
1e+400                                        <- exact, never through F32
```

Errors carry the 0-based position of the offending character (code points,
not bytes); an early end reports the input's length.

## What the parser accepts

Strict RFC 8259. It rejects trailing commas, comments, leading zeros, `NaN`
and `Infinity`, `+1`, `.5`, `1.`, single quotes, unescaped control
characters, invalid escapes, bad `\u` digits and lone surrogates. It joins
`\uD8xx\uDCxx` pairs into one char. Only space, tab, LF and CR count as
whitespace. Objects keep every member, in order.

## Numbers

A `Num` is `Num{neg, coef, eneg, exp}`: the value is `±coef × 10^(±exp)`.
`coef` and `exp` are decimal digit lists, least significant digit first. So
`19.99` is `1999 × 10^-2` and `1e400` is `1 × 10^400`, both exact.
Exponents are unbounded too (`4.5e-1000000` and `1e999999999999999999` are
tested). Nothing passes through F32.

**Why decimal digits rather than U32 limbs?**
- At runtime Bend's `Nat` is one 64-bit word and stops the program past
  2^48−1, so it can't hold big coefficients.
- 16-bit binary limbs would make printing a base conversion, and proving
  law 2 would then mean verifying bignum division by 10 on bit-level U32
  arithmetic.
- With digits, printing and parsing are digit-for-digit, so law 2 is
  provable.
- `bignat.bend` (16-bit limbs in U32s, all products and carries within 32
  bits) is still used where real arithmetic is needed: the correctly rounded
  `to_f32`.

**Normalized** means:
- no zero digit at either end of `coef`; trailing zeros move into the
  exponent, so `1.50`, `15e-1` and `0.15e1` are the same value;
- no high zero in `exp`;
- zero is the single value `Num{False, [], False, []}`, so `-0` reads as `0`.

The parser always returns normalized numbers. `D.Num.normalize` normalizes
any `Num`, and `is_norm` checks the property.

**Printing** uses the shortest natural form:

| Form | Examples |
|---|---|
| Plain digits, at most 21 digits including padding zeros | `1500`, `100000000000000000000` |
| Point inside the digits | `19.99` |
| `0.` plus up to 5 zeros | `0.000001` |
| Otherwise, exponent form (digits are never moved past the point) | `1e+21`, `15e+398`, `1e-7` |

**Conversions:**
- `to_u32` and `to_nat` return `None` unless the number is an integer in
  range (`to_nat` stops at Bend's 2^48−1).
- `to_f32` rounds to nearest, ties to even, with subnormals and ±infinity.
  It truncates past 120 significant digits; that tail can't change an F32
  rounding, since a tie needs at most about 113 digits.

## What is proven (`bend PROOF.bend` → ALL PROOFS CHECK)

`LAWS.bend` states the laws using the library's own functions; `PROOF.bend`
(about 3,200 lines) proves them.

1. **`unescape(escape(s)) == Some{s}` for every String.** This includes lone
   surrogates and codes past U+10FFFF, because escape keeps every non-control
   char raw.
2. **`parse_number(print_number(n)) == Some{n}` for every normalized `n`.**
   This covers all four print forms.
3. **`parse(print(v)) == Done{v}` and `parse(pretty(ind, v)) == Done{v}`, for
   every indent.** They hold whenever `v`'s numbers are normalized
   (`Json.is_norm`) and its nesting depth is at most 512 (`Json.depth`).
   Both conditions are needed: deeper values are rejected by design, and an
   unnormalized number reads back as its normalized form.
4. **Compact output has no char below U+0020; pretty output has none except
   `\n`.**

The proofs work against the actual parser, a character-level state machine.
`PROOF.bend` follows that machine through every print form and every escape.
For control characters, the proof derives at the bit level that such a char
has only five low bits, then splits into 32 cases that close by computation.

Notes:
- Some binders in `LAWS.bend` carry `+` (`for +s`, `for +h1`). That only lets
  a proof use the variable twice, as the Bend demos do; the claim is
  unchanged.
- `bend PROOF.bend --verdict`, the recheck by Bend's Lean-verified kernel, was
  **not run**: it needs a Lean 4.34.0 toolchain, which this environment
  could not run.
- `print_par` is tested to equal `print`, but not proven to.

## Tests

`bend tests.bend` checks 170 cases: literals, structure, escapes, surrogate
pairs, numbers and their formats, about 60 rejections with exact error
positions, the 512 and 513 depth limits, `get` returning the last match, U32,
Nat and F32 conversions (F32 against IEEE bit patterns), round trips and
`print_par`. The native build gives identical results:

```
bend tests.bend                                    -> tests: 170 passed, 0 failed
bend tests.bend -o tests && ./tests                -> tests: 170 passed, 0 failed
```

The JSONTestSuite `test_parsing` corpus (`corpus.bend <dir> <files…>`; files
are read as bytes and must be strict UTF-8, per RFC 8259 §8.1):

```
y_ (must accept): 95 accepted, 0 rejected
n_ (must reject): 188 rejected, 0 accepted
i_ (either way):  11 accepted, 24 rejected
```

The JS and native output is byte-identical.
- **`i_` accepted (11):** 10 number files with huge or tiny values, kept
  exactly, plus `i_structure_500_nested_arrays`.
- **`i_` rejected (24):** lone or invalid surrogates, invalid or overlong
  UTF-8, UTF-16 input, Latin-1, a UTF-8 BOM, and a code point past U+10FFFF.

## Timings

Measured on a 1,017,347-byte file (3,600 mixed records from `gen_bench.py`)
on a 4-core Linux VM. Times are in milliseconds; the native column is the
median of three runs.

| | JS (`bend bench.bend f`) | native, 1 thread | native, 4 threads |
|---|---|---|---|
| parse | 430–600 | 100 | 100 |
| print (compact) | 170–260 | 46 | 46 |
| pretty | 240–320 | 78 | 75–93 |
| print_par | 210–300 | 96 | 80 |

`print_par` splits a top-level array into balanced halves (2 levels) and forks
them, but it is **not faster** than `print`. Strings are linked lists, so
joining the halves costs a copy the fork never wins back; deeper splits were
slower still (171 ms at 10 levels). Use `print`. Parsing is a single
sequential state machine.

## Known limitations

- Strings are linked lists of chars, so memory use is a few words per
  character.
- A `\u0000` in input decodes to `Chr{0}`. Input must already be decoded
  text: `utf8.bend` does that strictly for files.
- `-0` normalizes to `0`, and exponent-form numbers print as `15e+398`,
  never `1.5e+399`.
- `to_nat` stops at 2^48−1, Bend's largest runtime Nat.
- A raw lone-surrogate char inside a String value round-trips, but a real
  UTF-8 encoder could not write it.
- The install script at bend-lang.com was blocked here, so the library was
  checked with Bend 2.0.39 run from the GitHub checkout
  (`bun bend2/main.ts`).
