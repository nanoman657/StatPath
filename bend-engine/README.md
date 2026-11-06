# bend-engine: the learning-data merge, in Bend and in Lean

`src/engine/merge.ts` merges two copies of a learner's progress. This folder checks its learning-data
part: lessons, SRS cards and XP per day. Cosmetic settings, the streak (which depends on local time),
the UI and effects are out of scope.

| File | What it is |
|------|------------|
| `merge.bend` | The merge in Bend: lessons, SRS cards and XP as sorted association lists |
| `LAWS.bend` | The merge laws stated in Bend: the lesson, XP, SRS, card-order and state laws |
| `PROOF.bend` | Their proofs, checked by Bend's kernel (see "Bend kernel proofs") |
| `ORDER.bend` | The order facts the proofs use: flip, transitivity and "EQ means equal" for the word, U32, string and Nat orders |
| `KEYS.bend` | The key order of the merge in Bend (`skey_cmp`), with its `Key.skey_eq_order` fact |
| `SORTED.bend` | Sortedness of the three maps: `SortedL`, `SortedX` and `SortedC` say that the keys strictly increase |
| `SORTMAP.bend` | The sorted-map layer for lessons: `Agree` and `SameLook`, and the laws `lookup_ins`, `lookup_fold` and `eq_of_sorted_lookup` (their proofs are in `PROOF.bend`) |
| `merge.mjs` | Generated from `merge.bend` by `gen.sh`; committed |
| `merge.d.mts` | The types of `merge.mjs` (written by hand; the tests check behaviour) |
| `gen.sh` | Checks `merge.bend`, then regenerates `merge.mjs` |
| `Merge.lean` | The model in Lean 4.34.0 (core only) and its laws, all proved |
| `model_vectors.py` | Writes `model_vectors.txt`: the Lean model's merge results on every pair of maps in a bounded domain |
| `model_vectors.txt` | Those results, committed (1,137 vectors); the test checks the compiled Bend against them |
| `compiler_check.py` | Runs the checker's reader (`CompilerCheck.lean`) on the compiled maxima, writes the report |
| `compiler_check_report.txt` | The committed report of that run, with the candidates and the reader's results |
| `../tests/merge_bend.test.ts` | Compiled Bend against `mergeProgress`, the Lean model and the laws; the Bend gate (`PROOF.bend --verdict`); staleness; this README's rows |

## Representation

- Each map is a list of entries, strictly increasing by key (Bend's `String.cmp`), so a key appears once.
- A key in both maps is combined: lessons take the larger of each field; XP takes the larger day total;
  cards take `mergeCard(a, b)`.
- Numbers are `Nat`. An absent `lastReview` is `None`; the comparisons read it as 0, as merge.ts does with
  `?? 0`, and the output keeps it absent.
- The Lean laws take sorted inputs (the `Sorted` hypotheses in `Merge.lean`). The Bend commutativity laws
  (lessons, XP, SRS and the whole state) take any two lists. The Bend idempotence laws take a sortedness
  witness from `SORTED.bend`, so they say nothing about unsorted input.

### The SRS tie-break

`mergeCard` keeps the later review, then more reps, then the later due date. On a full tie of those, it
keeps the card with the larger content. The owner chose this rule, after a finding that the earlier
tie-break was not commutative.

The cards are compared field by field, in this order: `id`, `lessonId`, `interval`, `ease`, `due`,
`lapses`, `reps`, then `lastReview` with an absent one first. The owner asked for "serialized content". JSON
strings cannot be reproduced in Bend, which has no float-to-text, so the comparison is field by field. The
order is total. merge.ts (`compareCards`), `merge.bend` (`full_cmp`) and `Merge.lean` (`fullCmp`) implement
the same one.

## Commands

    bend bend-engine/merge.bend --check-only     # the check (passes)
    bend bend-engine/PROOF.bend                   # the Bend proofs (ALL PROOFS CHECK)
    bend bend-engine/PROOF.bend --verdict         # the same, re-checked by the kernel
    bend-engine/gen.sh                            # regenerate merge.mjs
    npx vitest run tests/merge_bend.test.ts       # differential, laws in code, staleness, the Bend gate, these rows
    export PATH=/root/.elan/toolchains/leanprover--lean4---v4.34.0/bin:$PATH
    lean bend-engine/Merge.lean                   # compiles; prints the axioms of the laws
    python3 bend-engine/model_vectors.py          # regenerate model_vectors.txt from Merge.lean
    python3 bend-engine/compiler_check.py         # regenerate compiler_check_report.txt

Bend's own `--verdict` is used on `PROOF.bend` only; `merge.bend` itself has no proofs.

## Lean theorems

Layers: **proved** means proved in `Merge.lean` for the model. **code tested** means the compiled Bend code
is checked against `mergeProgress`, against the law, or against the model's own results on every pair of maps
in a bounded domain (`model_vectors.txt`), in `merge_bend.test.ts`. The model is linked to the code by a hand
transcription, which is not mechanized (see below).

The test `every row points to a real theorem, function and test` checks that each row's
Lean theorem, Bend function and TypeScript function exist, and that each quoted test name is a test in
`merge_bend.test.ts`.

| Lean theorem | Bend function | TypeScript | Test | Layer |
|---|---|---|---|---|
| `lessons_comm` | `merge_lessons` | `mergeProgress` (lessons, `mergeLesson`) | "the compiled merges are commutative on random pairs, the SRS merge included"; "agrees with mergeProgress on 10,000 random pairs, with ties and missing entries" | proved; proved in Bend; code tested |
| `lessons_idem` | `merge_lessons` | `mergeProgress(a, a)` (lessons) | "the compiled merges are idempotent: merging a copy with itself gives the copy" | proved; proved in Bend; code tested |
| `xp_comm` | `merge_xp` | `mergeProgress` (`xpByDay`) | "the compiled merges are commutative on random pairs, the SRS merge included" | proved; proved in Bend; code tested |
| `xp_idem` | `merge_xp` | `mergeProgress` (`xpByDay`) | "the compiled merges are idempotent: merging a copy with itself gives the copy" | proved; proved in Bend; code tested |
| `xsum_comm` | `merge_state` (output `xp`, `xsum`) | `mergeProgress(...).xp` | "the compiled merges are commutative on random pairs, the SRS merge included" | proved; proved in Bend; code tested |
| `cardMerge_comm` | `merge_srs` (`card_pick`, `full_cmp`) | `mergeCard`, `compareCards` | "the compiled merges are commutative on random pairs, the SRS merge included" | proved; proved in Bend; code tested |
| `srs_comm` | `merge_srs` | `mergeProgress` (`srs`, `mergeCard`) | "the compiled merges are commutative on random pairs, the SRS merge included" | proved; proved in Bend; code tested |
| `srs_idem` | `merge_srs` | `mergeProgress` (`srs`, `mergeCard`) | "the compiled merges are idempotent: merging a copy with itself gives the copy" | proved; proved in Bend; code tested |
| `cardMerge_cA_cB` | `merge_srs` (`card_pick`, `full_cmp`) | `mergeCard` (tie on ease) | "the tie-break keeps the card with the larger content, in either order (ease)" | proved; code tested |
| `cardMerge_cD_cC` | `merge_srs` (`card_pick`, `full_cmp`) | `mergeCard` (absent against 0) | "the tie-break counts an absent lastReview as before any time (absent against 0)" | proved; code tested |
| `state_comm` | `merge_state` | `mergeProgress` | "the compiled merges are commutative on random pairs, the SRS merge included" | proved; proved in Bend; code tested |

Supporting lemmas (`insC_spec`, `ins_lookup`, `fold_lookup`, `mergeMap_lookup`, `eq_of_sorted_lookup`,
`mergeMap_sorted`, `cardMerge_eq`, `cardCmp_swap`, `fullCmp_eq`) are the model's proofs. Insertion keeps a
map sorted. Two sorted maps with the same lookups are equal. The card order flips with its arguments, and a
tie is the same card. The rows above use them. Bend proves the sorted-map counterparts `lookup_ins`, `lookup_fold` and `eq_of_sorted_lookup` (see "Bend kernel proofs").

Proved axioms (printed by `lean`): `propext`, `Classical.choice`, `Quot.sound` only. No placeholder proofs.

## Bend kernel proofs

`LAWS.bend` states the laws and `PROOF.bend` proves them with Bend's own kernel, against `merge.bend`
(imported as `Merge`). `bend PROOF.bend` prints `ALL PROOFS CHECK` when every law has a proof; an open law
shows as a TODO, and a wrong proof as `SOME PROOFS FAIL`. `--verdict` re-checks the proofs with the kernel.

Proved in Bend:

- `max_comm`, `max_self`, `max_assoc`: `Nat.max` is commutative, idempotent and associative.
- `lp_max_comm`, `lp_max_self`, `lp_max_assoc`: the lesson merge `lp_max` has the same three laws, field by field.
- `tie_ease`, `tie_absent`: two concrete SRS tie-breaks. On a tie of the other fields, the card with the
  larger ease wins; an absent `lastReview` loses to `Some{0}`. These are closed equalities, checked by
  reduction. A negative control (a wrong expected card) makes the gate fail, so the check is not vacuous.

- The string-order swap law: `Cmp.flip` (the reverse of a comparison) is an involution; `Bool.cmp`,
  `Word.cmp`, `U32.cmp`, `String.order.go` and `String.order` each flip when their two arguments are swapped.
  This is one half of antisymmetry for the key order.
- The card order, as in `LAWS.bend`: `skey_cmp_flip` (the key order flips when its strings are swapped),
  `skey_eq_of` (an `EQ` key comparison means the strings are equal), `cmp_then_flip` and `cmp_then_swap`
  (`cmp_then` flips), `full_cmp_flip` (the whole-card order flips), `last_key_eq` (lastReview values whose keys
  compare `EQ` are equal), `full_eq_card` (a whole-card `EQ` means the cards are equal), `card_pick_flip`
  (`card_pick` with flipped comparisons and swapped cards picks the same card), `card_merge_comm`, the
  general `cardMerge_comm` row above: `card_merge` is commutative. `card_merge_assoc` and `card_merge_self`:
  `card_merge` is associative and idempotent. These two have no row in the table above.
- `skey_lt_trans`: the key order is transitive: `a < b` and `b < c` give `a < c`.
- `lessons_comm`, `xp_comm`, `srs_comm`: merging two lists gives the same list in either order, for any two
  lists. The insertion-order lemmas hold for every list, so these need no sortedness.
- `xsum_comm`: the total XP is a function of the merged XP map, so it follows from `xp_comm`.
- `state_comm`: the whole-state merge is commutative: the lessons, SRS cards, XP days and total XP each agree
  either way.
- `lessons_idem`, `xp_idem`, `srs_idem`: merging a sorted map with itself gives the map back. These take the
  sortedness witnesses `SortedL`, `SortedX` and `SortedC` from `SORTED.bend`.

The gate is the vitest test "the Bend proofs of the laws", which runs `bend PROOF.bend --verdict` and requires `ALL PROOFS CHECK`. Negative controls, run on scratch copies of this folder: a wrong proof (the body of `Laws.srs_idem` replaced by `{==}`) makes the gate fail with `SOME PROOFS FAIL` and a type mismatch at `Laws.srs_idem`; a law whose proof is deleted (`state_comm`) fails with `SOME PROOFS FAIL` and `1 TODO found`.

`SORTMAP.bend` states the sorted-map layer for lessons, the Bend side of the Lean model's `ins_lookup`, `fold_lookup` and `eq_of_sorted_lookup`. `PROOF.bend` proves all three:

- `lookup_ins`: the lookup after inserting an entry is the insertion spec `ins_look_l`, for a sorted map.
- `lookup_fold`: the lookup after folding a sorted map into a sorted accumulator is `comb_opt_l` of the two lookups.
- `eq_of_sorted_lookup`: two sorted maps are equal when each entry of one is in the other with the same value (`SameLook`). Lean's hypothesis, that the two lookups agree at every key, implies `SameLook`, so the Bend law is at least as strong as Lean's. It is stated for lessons only.

The proofs use the step-1 encoding of the key order from `ORDER.bend`. `IsLT` and `IsEQ` are witness types for a `Cmp` value. `IsLT.to` and `IsEQ.to` turn an equation `skey_cmp(a, b) == LT{}` (or `EQ{}`) into a witness, and `IsLT.of` turns a witness back into an equation (`IsEQ.of` is defined but no proof uses it). `Cmp.trLT` and `Cmp.trEQ` carry a witness across an equation of comparisons. The refutations `IsLT.neq_gt`, `IsEQ.neq_lt` and `IsEQ.neq_gt` turn a witness and an equation for another constructor into `Empty`; they are built from the `!=` laws (`Cmp.eq_ne_lt` and the others).
Base declares the order's antisymmetry as a law (`String.cmp`) but does not prove it, and no Bend proof uses it.

## What is not mechanized

- **The transcription.** `Merge.lean` follows `merge.bend` by hand, function for function: `insC` is
  `lins_c`, `ins` is `lins`, `fold` is `lfold`, `fullCmp` is `full_cmp`, and so on. No tool proves that
  correspondence. What the tests add is evidence on two levels:
  - the compiled code against `mergeProgress` on 10,000 random states (differential);
  - the compiled code against the model's own results on every pair of maps in a bounded domain: two
    keys, the empty map, one key with each value, or both keys with each pair of values; lessons with 3
    values, SRS cards with 4 (one differing in ease, one with no review time, one with reps 2), XP with 3.
    That is 1,137 pairs, all checked (`model_vectors.txt`). A change of one comparison in the compiled
    code makes this test fail on its first vector (checked by hand: the XP maximum changed to a minimum).
  The bounded agreement is exhaustive for its domain, not for all inputs. So the rows above are proved for
  the model, and the code is tested against the model on that domain; they are not linked by a proof.
- **Numbers.** The Bend code and the model use `Nat`. merge.ts uses doubles, and `ease` and `bestAccuracy`
  are not integers in general. The merge only compares and selects numbers and never computes with them, so
  the laws do not depend on the representation; the tests use integer values. This is assumed, not proved.
- **Key order.** The model uses Lean's `<` on `String`; the code uses `String.cmp`. The test
  `orders keys as JavaScript orders them, on random strings` checks them against JavaScript's string order on
  random strings. That is a test of the order, not a proof that the two agree on every string.
- **Out of scope:** the streak, the cosmetic settings, the other engine modules.

## Translation validation: `CompilerCheck.lean`

The checker's reader, `parseJS`, takes the JavaScript of a transition as a function whose name starts with
`$`, with arithmetic in its return expression. `compiler_check.py` runs it, unchanged, on the candidates
taken from `merge.mjs` as the compiler emitted them. The full report, with the texts, is
`compiler_check_report.txt`. Its results:

- **The lesson maxima** (`crowns`, `attempts`, `best`, `played`, from `$lp_max`) and **the XP maximum** (from
  `$xins_c`), each as a one-line function `return (a > b ? a : b);`, are **refused**: `parseJS` returns no
  function.
- **The same text with `>` changed to `<`** (crowns and XP, parse-only: the guard is the only change) **is
  parsed**. So the refusal comes from the `>` guard, and nothing else in the text.
- **The whole `$lp_max`** is refused too. It returns a record, not an arithmetic expression.
- **The Bend side.** The checker's `parseBend` refuses the Bend definition `Nat.max(c1, c2)` and accepts
  `Nat.min(c1, c2)`. Its definitions are `var`, `add`, `sub` and `min`: there is no maximum, so a maximum
  cannot be stated on the Bend side at all.

So the checker does not validate the compiled lesson or XP maxima. It would need the guard `>` (or a maximum
construct on the Bend side), and the lesson merge's record result is outside its fragment (a `Nat` from `Nat`
arguments). The report is reproduced by `test`; the repository's `CompilerCheck.lean` is not modified.

## The SRS tie-break: the finding and its resolution

The first version of `mergeCard` returned `a` on a full tie of review time, reps and due date, so
`merge(a, b)` and `merge(b, a)` could differ. `Merge.lean` proved two counterexamples at the time: cards that
differ only in ease, and a card with no review time against one with 0. The owner chose to break ties on the
whole card (see "The SRS tie-break" above). That rule is now implemented in `src/engine/merge.ts`
(commits `9372632`), `bend-engine/merge.bend` and `merge.mjs`, and `Merge.lean` (commit `87df171`). The
counterexamples became the commutativity rows above; the two examples now show the order deciding the ties.

## Assumed, and not yet done

- The Lean toolchain `lean-4.34.0` was obtained from GitHub; its checksum was not verified against a published
  value (see `browser/README.md`, "The Lean recheck").
- The staleness test fails when `bend` is not on PATH; it does not skip. It needs `bend` installed.
- `merge.d.mts` is written by hand. Generating declarations from the Bend types is not done.
- The model-to-code correspondence is a hand transcription, with the bounded agreement above (see "What is not
  mechanized").
