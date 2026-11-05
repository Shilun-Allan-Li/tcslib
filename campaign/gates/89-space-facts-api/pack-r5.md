# External audit pack, round 5: four space facts out of `Machines/ARMWidth`, and the binary-length bounds (PR #181, an API gate)

**Rounds 1–4** (`pack.md` … `pack-r4.md`; findings `findings.md` … `findings-r4.md`; resolutions
`resolutions.md`). Round 4 was **OPEN, 0 blockers, 1 major, 3 minors**, with no mathematical defect
in the move or the re-points. The major: BL-1's site list (elementary binary-length bounds re-derived
from `Nat.size`) missed copies in five files, and `Codec/Layout` reached 2 of 9 declarations.
**Ruled (user, 2026-11-04): re-point now in #181.**

**The PR now:** #181 on `lean/logspace-move`, head `98912ab293dc329b3f7274ee27977fa19789ce78`.
Round 5's Lean commits (`evidence/round5/patches/`) are `d789d6db` (the re-points) and `98912ab2`
(one docstring). The two merges in between bring in campaign records and change no Lean. Against
the campaign, #181 now changes 25 Lean files: round 4's 14 and 11 more.

## What changed since round 4 (verify)

| File · declaration | Change |
|---|---|
| `Machines/Bin` · `Complexity.LogProg.two_pow_bits_le` (new) | `2 ^ |bits L| ≤ 2L` for `L ≥ 1`, moved from `Codec/Layout` (`Complexity.Codec.two_pow_bits_le`, removed); statement and proof byte-identical; a sketch added; listed under main results |
| `Codec/Word` · `Complexity.Codec.wP_eq` (new) | `wP n = |bits (n + 1)|`, by `rfl` |
| `Codec/Layout` · `wP_le` | its logarithmic proof becomes `rw [wP_eq]; exact Turing.length_bits_le_self (n + 1)` |
| `ClassPSPACE/TQBFHardParams` · `Complexity.TQBFHard.wP_le` | **removed**: it restated `Codec.wP_le` (same `wP`; the file opens `Codec`). Its one use resolves to `Codec.wP_le` |
| `Codec/Parse` · `bitsVal_le_of_width`; `Logspace/PathHard` · `two_pow_ell_le`; `Randomized/RandomWalkPad` · `padDegree_le`; `Randomized/BPLInP` · `two_pow_codes_le`; `Randomized/SpaceAmplifyPoly` · `two_pow_bits_le` | their re-derivations of (v) cite `two_pow_bits_le` |
| `ClassP/BinaryArith/PrimeFind` · `polyTimeComputable_countLoop`, `polyTimeComputable_dblLoop`; `TuringMachine/CodeSimulator` · `canonOffset_spec`; `TuringMachine/Build/RecordTable` · `rt_exists_boundTM`, `rt_exists_boundFieldTM`; `Randomized/SpaceAmplifyPoly` · `ell_le` | their re-derivations of (iii) cite `Turing.length_bits_le_self` |
| `Logspace/ISCountGenCorrect` · `bits_succ_le`; `Logspace/PathHard` · `ell_mono`; `SpaceComplexity/WindowClock` · `FinTM.configBound_le_two_pow` | (i) cites `length_bits_le`, (ii) `length_bits_mono`, (iv) `Turing.record_pos_lt` |
| `Randomized/BPLInP` · `two_pow_codes_le`'s docstring | its sketch cites `two_pow_bits_le` |

Freeze (`evidence/round5/freeze/`, each file at round 4's head `227d92ee` against the head):
- exactly the declarations above change; no statement changes;
- `Bin` +1, `Word` +1, `Layout` −1 and `TQBFHardParams` −1 public declarations.

The moved lemma's users in `Layout`, `Layout2`, `Deciders` and `StepDecider` keep the unqualified name,
which now resolves through `open LogProg` (`evidence/round5/api-search/`: no other ref declares or
uses the moved, removed or new names).

The records:
- the ledger's BL-1 entry: the scope correction, the re-points and the residual;
- LS-3's census;
- `evidence/round5/ls1-search/classification.md`, rewritten.

## Brief for the auditor

1. **Is round 4's major closed?** Every group of the binary-length sweep at the head is classified
   (`evidence/round5/ls1-search/bitsweep-classes.md`, by `bitclasses.py` over `bitsweep.tsv`; each
   group in context in `bitsweep-context.txt`). Is any group misclassified? Is any BL-1 member
   missing from the ledger's residual? That residual is 13 groups, each with its reason:
   colleague-owned `CircuitComplexity`, `Machines/Bin` above the file's layer, no reachable lemma, or
   E-D's in-flight `NTimeDiagonalizer`. E-D's landing re-points `qy_call_bound`; the file's other four
   members cannot reach `Machines/Bin` and go to the dedup window. One of them, `qy_ones_ge` (iv), is
   new in round 5's sweep, and the user's acknowledgment of it is recorded in the resolutions. Does any file now exceed one fifth?
2. **The re-points and the move:** are the changed proofs correct? Is the move of `two_pow_bits_le`
   faithful (namespace `Codec` → `LogProg`)? Is removing `TQBFHard.wP_le` safe? Do `wP_eq` and the
   other proofs read other files' definitions only through published lemmas (rule 10)?
3. **Round 4's minors:**
   - LS-3's census and the converse's wording;
   - the searches described as candidate enumeration with inspection;
   - the portable sweep: 191 rows at round 4's head, 179 at this head;
   - the screen's population: 33 distinct files, with no duplicate.
4. **The screen** (`evidence/round5/screen/`): 33 files, base a `git archive` export of `711f5444`.
   The head was screened at `b0f95123`, which differs from the audited head only in one docstring;
   the screen strips comments. Results: 665 → 662 declarations, 166 → 166 pairs (`pairdiff.txt`).
   - **Gone:** `Parse`'s `bitsVal_le_of_width` reproducing `Layout`'s `two_pow_bits_le` (100%), the
     inline copy round 5 removes.
   - **New:** `BPLInP`'s `two_pow_codes_le` reproducing `SpaceAmplifyPoly`'s `two_pow_bits_le`
     (94/107, 88%). Both now consist of the same zero split followed by a citation of `Bin`'s
     `two_pow_bits_le`: shared phrasing, not a re-derivation.

   Is that right, and is anything else copied?
5. **Lint** (`evidence/round5/lint/`): `campaign_style_lint` over `SpaceComplexity`, `Randomized`,
   `TuringMachine`, `ClassP` and `ClassPSPACE` at base and head. The only changes are file lengths and
   `Word`'s check-8 list losing `wP`. `style_lint`'s findings on the round-5 files are the base's,
   at shifted lines.

## Repository-side attestations (verify or challenge)

- **Elaboration** (`evidence/round5/elab/`, `elab_chain.sh`). The round-5 files and the moved
  lemma's unchanged users were compiled in dependency order with `lean -o` into a copy-on-write
  clone of `oleans-lsm4`: `Bin`, `Word`, `Parse`, `Layout`, `Layout2`, `Deciders`, `StepDecider`,
  `PathHard`, `ISCountGenCorrect`, `WindowClock`, `SpaceAmplifyPoly`, `BPLInP`, `RandomWalkPad`,
  `PrimeFind`, `TQBFHardParams`, `CodeSimulator` and `RecordTable`. Every output is empty except
  `RecordTable`'s four `sorry` warnings, which the base has too (four `sorry`s before and after).
  `PrimeFind` and `BPLInP` were re-run after their last edits.
- **Replay:** `replay-lsm5.sh` (`evidence/round5/merged-tree/`), the 25 files' downstream closure,
  **209 modules**. It is larger than round 4's 137, because `CodeSimulator` and `RecordTable` sit low.
  It builds fresh `.olean`s from `oleans-leqc3`, pinning the 25 blobs. The precheck passed at the
  head; **not yet run.** `replay-lsm4` (round 4's head) passed but no longer certifies the PR.
- **Overlap:** #181 merges first; #182 and then #184 take their merged-tree replays after it (as
  ruled). #184 also edits `Codec/Word`, `Codec/Parse` and `Codec/Deciders`, in other hunks.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

The severity guide is in `campaign/standards/TEMPLATE.md`. Findings are copied verbatim into
`campaign/gates/89-space-facts-api/findings-r5.md`. The gate closes when it has zero blockers and
zero majors.

**Deliver your findings as a downloadable Markdown file named `space-facts-api-r5-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
