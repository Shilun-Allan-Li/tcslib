# Pair decoder reuse assessment

2026-11-07; bounded source review only. No Lean elaboration, delivered-script execution,
source/Git changes, screens, or pushes. The only written output is this report.

**Existing published interfaces suffice for a proof refactor; a new `pairDecode` API is
not forced by `fwdMap_parse`.** The current moved proof still reads the foreign definition,
and this assessment does not repair it or close its seal gap.

## Sources and current gap

Inspected the actual delivery found through `rg --files`:

- `checkpoint05-2026-11-07/cp05/fill-mig1-mega-cp05/source/TCSlib/Complexity/TuringMachine/Build/Primitives.lean.txt`.
- `checkpoint07-2026-11-07/extracted/fill-mig1-mega-cp07/source/TCSlib/Complexity/TuringMachine/Build/Primitives.lean.txt`.

Both files are byte-identical, SHA-256
`8fc691da32fbf79e773605c286345dd6cc0985c3e5220de16de0340bd14a09d1`.
The cp05 lines 3060, 3076, 3089, 3094, 3100 and 3107 explicitly pass `pairDecode` to
simplification; line 3068 obtains the singleton result by `cases b <;> rfl`. Its displayed
seal set omits `pairDecode`. The singleton conversion is a definition read too.

No named recursive/case-reader family for `pairDecode` was found in current
`TCSlib/Complexity/TuringMachine/Encoding.lean`. Compiler-generated equations are not
treated as an approved interface by this review.

## Published information already available

All three declarations below are public in `Encoding.lean`, namespace `Turing`:

```lean
-- line 151
pairDecode_pairEncode (x α : List Bool) :
  pairDecode (pairEncode x α) = some (x, α)

-- line 253
eq_pairEncode_of_pairDecode (z a b : List Bool)
  (h : pairDecode z = some (a, b)) : z = pairEncode a b

-- line 225
pairDecode_eq_none (z : List Bool) (h : pairDecode z = none) :
  ∃ w tail, z = dbl w ++ tail ∧
    (tail = [] ∨ (∃ b, tail = [b]) ∨ ∃ r, tail = true :: false :: r)
```

Also available are `pairEncode_eq` (line 139), `pairEncode_eq_dbl` (210),
`length_pairEncode` (214), and the published `dbl_nil`, `dbl_cons`, and `length_dbl`
equations (183, 186, 189). None requires unfolding the decoder in a consumer.

The failure theorem is **one-way**: it requires a known decoder failure. It must not be
used as an iff or to assert failure solely from a malformed-tail shape.

## How to use these interfaces without a new reader

Keep `fwdMap_parse`'s statement and case-split on the opaque value `pairDecode rest`
**before** proving the machine behavior. This supplies the premise for the appropriate
published shape theorem and removes the decoder match in the conclusion.

| Decoder result | Published shape | Remaining machine argument |
| --- | --- | --- |
| `some (d, b)` | `rest = pairEncode d b`, by `eq_pairEncode_of_pairDecode` | Induct on `d`; its equal-bit blocks use existing `fwdMap_block`. At the delimiter `01`, use that block and existing `fwdMap_finish`. |
| `none` | `rest = dbl w ++ tail`, with the three listed malformed tails, by `pairDecode_eq_none` | Induct on `w`, using `dbl_cons` and `fwdMap_block`. Handle empty, singleton, or `10` terminal input by the machine's existing rejecting transitions. |

The decoder stays opaque throughout these inductions: its result was fixed by the outer
case split. In particular, the nil/singleton/`10` cases no longer need new facts evaluating
`pairDecode` at those inputs, and equal-bit cases no longer need its recursive equations.
The native-machine endpoint/control arguments still need their own rule-10 repairs;
this review only addresses the decoder dependency.

This route matches the available machine facts: `fwdMap_block` (cp05 line 2795) appends
one buffered bit on equal bits, starts suffix copying at `01`, and rejects `10` without
output. `fwdMap_finish` (3013) already supplies the successful suffix-buffering and emission
endpoint. The original empty/singleton machine arguments can be retained after their
decoder-dependent reductions are removed. The published length equations support the
existing linear budget: doubled-prefix traversal costs two steps per bit, followed by
the same terminal or finishing phase. No uniqueness assumption for the malformed-prefix
decomposition is needed.

An alternative is to derive the needed recursive equalities from the same public inverse
and shape lemmas, but that would add proof work reproducing the parser grammar. The
shape-based split avoids proposing or adding another decoder-reader family here.

For the separate `pairEncode` arguments at cp05 lines 3034 and 3474, the existing
`pairEncode_eq` supplies the explicit encoding equation; that is a routine substitution
followed by the existing list equations.

## Remaining validation

This is a source-level reuse route, **not an elaborated replacement proof**. The fill
still needs the refactor, exact bound/configuration checks, argument inspection, and a
fresh seal that includes `pairDecode` (and `pairEncode` where reached), with paired
controls. No current checkpoint is accepted or sealed by this report. No new public
statement is requested on this evidence.
