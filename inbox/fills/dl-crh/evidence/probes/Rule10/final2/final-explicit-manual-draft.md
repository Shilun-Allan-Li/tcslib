# Explicit-list source review draft

Status: source review complete; native constant-kind/home review pending.
This draft issues no final clearance of native definition candidates.

The reviewed input is `final-scan-plan.json`, SHA-256
`ae5ab691f8f143b2cc6a2302e46ba5f5397453f24d0fec5668fe6730d5d3350f`.
All 595 inventory rows were read by declaration and source context: 383 NEW,
4 CHANGED, and 208 SAME. `final-explicit-manual-draft.json` contains one
individual disposition record for every 1-based input row. It retains the
expected kind, scope rationale, lexical corrections, and pending-native status.

The final2 rebinding tool is
`evidence/tools/manual_explicit_review_final2_draft.py`, run as
`python3 -I evidence/tools/manual_explicit_review_final2_draft.py`. It first
verifies that all 595 final2 inventory rows exactly equal the final1 rows, then
reuses the unchanged archived manual source classifications from
`evidence/tools/manual_explicit_review_draft.py`. Final1 artifacts are unchanged.
The underlying materializer encodes the
manual source classifications in explicit symbol lists and row overrides,
rejects unreviewed heads, and runs no Lean or Lake process. It does not infer
native constant kinds or clear a definition by name pattern.

| Source classification | Rows | Draft treatment |
|---|---:|---|
| Same-file definition in an unchanged declaration | 36 | Expected def/home recorded; native confirmation pending |
| Local proof equation | 66 | Binding and mathematical equality individually recorded |
| Local let body | 8 | Exact local let recorded; no foreign definition body involved |
| Public TCSlib reader candidate | 309 | Expected theorem; native kind/home pending |
| Core/Mathlib equation candidate | 159 | Expected theorem; native kind/home pending |
| Published theorem used through dot notation | 12 | Exact WellFormedIndex theorem identified; native confirmation pending |
| Inline typed equation proof | 1 | `show` syntax, with the actual proof supplier recorded |
| Built-in conditional simplifier control | 4 | `↓reduceIte` syntax, not a global definition token |

The 36 expected same-file definitions all occur in SAME declarations. There
is no source-level named foreign-definition expansion identified in the NEW or
CHANGED rows. This remains a provisional source conclusion until the native
kind/home table is joined and every global hit is checked.

## Required lexical corrections

Rows 153 and 197 name `ZMod.val_natCast`; row 488 names `ZMod.val_mul`.
The lexical `local_names` inventory incorrectly captured `ZMod` from a type
expression as if it were a binder. These qualified tokens are global theorem
candidates and must not receive a local-binder clearance.

Rows 398, 437, 446, 457, 477, 480, 491, 494, 540, 573, 580, and 588 use
`hw.dlW_eq`. In each source declaration `hw : WellFormedIndex n i`, so dot
notation denotes the published theorem
`TCSlib.Cryptography.Candidates.WellFormedIndex.dlW_eq`. These are not arbitrary
local member reductions. The theorem statement is an exact width equality.

Conversely, the lexer omits some real local equations introduced by
`obtain`, `cases ... :`, `split_ifs with`, and `set ... with`. The individual
row records correct `ha/hb/hc` (rows 2, 4–6), `he` (115, 343, 455), `hvdef`
(130, 133), `hs` (131, 134, 424, 427), and `hkey` (539). No global symbol
sharing these short suffixes should override their actual local bindings.

The eight local-let expansions are rows 325, 337, 360, 361, 370, 371, 423,
and 426. They are only the proof-local `width`, `u`, and sampler-result `w`.
All remaining local records name proof equations rather than definition bodies.

Row 114 is an inline `show ... = ... from (hs z).2`, where `hs` is the
published block-rejection host contract returned locally. The parser's head
`show` is term syntax, not a foreign constant. Rows 216, 219, 483, and 486
are the built-in simplifier control `↓reduceIte`.

## Remaining native review

After the native scan exists, join all 595 records by their input row number.
Every candidate of kind `def` requires an explicit fully-qualified name, home,
and disposition, including Core and Mathlib definitions. The same-file
definition expectation must be confirmed rather than assumed from a suffix.

Every unresolved or ambiguous row requires an individual scope explanation.
For local equations, preserve the source binding as the deciding evidence;
for `hw.dlW_eq` and the false `ZMod` locals, use the actual published theorem
identity. A candidate table can contain unrelated same-suffix constants; these
are not themselves evidence that the original source read a definition body.

If any expected-equation item resolves to a foreign definition, report it as
an open Rule 10 finding instead of retaining the draft's expected-theorem label.
The final review must also distinguish inherited SAME-file behavior from new
behavior and retain the full base/final evidence. Whole-file seals independently
check implicit TCSlib body reads and do not replace this explicit-list review.
