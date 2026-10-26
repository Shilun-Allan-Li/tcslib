# External audit pack — `spaceConstructible_poly` proved (PR #166, a maintainer landing)

Campaign: the Arora-Barak chapters 3-4 plan, the second fill track (megafill D). The target
`Complexity.spaceConstructible_poly` (`SpaceComplexity/Savitch.lean`, the frozen statement
`(c : ℕ) (hc : 1 ≤ c) : SpaceConstructible fun n => n ^ c + 1`) was blocked by rule 10 until A1
(#164) published readings of the chapter predicates. The megafill D review's consumer probe
(`campaign/fills/megafill/reviews/megafill-d/probe/A1ConsumerProbe.lean.txt`) then proved the
whole statement with A1's final names, under a seal. **The user ruled (2026-10-25): land it
directly** from that probe, by a maintainer PR and this gate, instead of briefing it as a fill.
A1's own gate (76) closed with a PASS, 0/0/0/14 (`campaign/gates/76-a1-predicates-api/`).

**The head:** `lean/scp-landing` at `0282b487`, one commit (`evidence/scp-landing.patch`) on A1's
head `ae4849af`. PR #166 is stacked on #164, with base `lean/a1-predicates`, and is retargeted to
the campaign branch once #164 merges. This bundle's Lean files are from `0282b487`, and its
records from the records commit that the dispatch prompt names.

| Change in `SpaceComplexity/Savitch.lean` | |
|---|---|
| Import | `TCSlib.Complexity.ClassNP.Transducer` (Transducer's closure does not contain Savitch; the review's `probe/scp-new-import-up.txt`) |
| Privates (8, `scp_`) | the tail transducer's tables `scp_tailδ`, `scp_tailO`; `scp_transduce_copy` (cites `transduce_of_copy`), `scp_transduce_tail`; `scp_tail_pow_le`, `scp_value`, `scp_time_arith`, `scp_space_arith` |
| `spaceConstructible_poly` | the `sorry` replaced by the probe's route; the statement unchanged; the docstring's proof sketch rewritten to the route taken (see brief item 4) |
| Module text | the status paragraph and the main-results entry say the lemma is proved; nothing else |

## The route

- **Dominance:** `logSpace n ≤ n + 1 ≤ n ^ c + 1`, by `Complexity.logSpace_le_succ`
  (`Machines/ARMWidth`) and `Nat.le_self_pow`.
- **The witness:** a timed conditional on `x = []` (`Turing.FinTM.computesFunInTime_cond`), with
  the decider `computesFunInTime_ifEq [] [true] [false]` converted to `[decide (x = [])]` by a
  funext.
  - On the empty input the branch is `computesFunInTime_const (Nat.bits 1)`.
  - On other inputs the branch is four phases by `bufferedCompTM_computesInTime`, each at its
    exact time: the tail transducer (`transducerTM_computes`, then `scp_transduce_tail`);
    `polyUnaryTM 1 c` (`polyUnaryTM_computes`); `prependTM [true]` (`prependTM_computes`); the
    length counter (`computesFunInTime_lengthBits`).
  - `scp_value` identifies the branch function with `x ↦ (|x| ^ c + 1).bits`.
- **Space from time:** `Turing.MultiTapeTM.spaceUsed_le_mul_succ` at the halting time, then
  `scp_space_arith`. The space constant is `M.k * (c_M (c_D + c₁ + 2K + 2) + 1) + 1`, where
  `K = 5c + 20 + 3c_L`.

## Brief for the auditor

1. **Faithfulness.** Does the proof establish the frozen statement for every `c ≥ 1` and every
   input, including the empty input and `|x| = 1`, where the unary word is `true :: []`? Do the
   two arithmetic lemmas hold as stated, and do they bound the composed time and the conditional's
   time as used? Is `scp_value` right on both branches?
2. **The published rows.** Is each row applied at its own statement: the exact times of the four
   phases, `computesFunInTime_cond`'s bound `c (T₀ + max T₁ T₂ + 1)`, and `spaceUsed_le_mul_succ`'s
   `k (t + 1)`? Is any row's hypothesis met only by unfolding?
3. **Rule 10** (with the scope of 2026-10-23). The seal makes the 12 TCSlib definitions the proof
   reaches irreducible. The review's definition scan, retargeted to the landing, finds those 12
   plus three `FinTM` projections, the same set as the review's. Does any step still close only
   because another file's definition reduces? The `simp only` sets name only this file's two
   tables, core and Mathlib list, `Nat`, `Bool` and `Option` lemmas, and the core simproc
   `reduceCtorEq`. Check this.
4. **The docstring.** The planned sketch named two catalog space rows that the proof does not
   use: `computesFunInTime_polyUnary_spaceUsed` and the polyBits row's space clause. The review
   (F10) asked a fill to add a "Fill appendix"; this maintainer landing rewrites the sketch
   instead. Is the new sketch an accurate reading of the proof, naming its key steps? Are the
   status and main-results edits accurate, and is all new text public-facing (no campaign labels,
   paths or dates)?
5. **Duplication.** The v3 screen on 14 files (`evidence/screen-population.txt`): `Savitch`,
   `Constructible`, `Basic`, `ARMWidth`, `Transducer`, `TimeConstructible`, the two
   transducer-instance files, `Finite`, `Simulation`, `Composition`, `Build/Primitives`,
   `Build/Wrappers` and `Build/Catalog`. It ran at A1's head (`ae4849af`) and at the landing
   (`0282b487`): 863 → 868 declarations, 1,209 → 1,209 pairs, none new and none gone
   (`evidence/screen-scp-*.txt`, `pairdiff-head-vs-base.txt`). Semantic: are any of the eight
   privates a re-derivation of published API? The review's dossier (`out/04`) found none beyond F1,
   the dominance step, which is now the citation `logSpace_le_succ`. It named
   `spaceConstructible_linear`'s closing calc (`Constructible.lean`) as a copy-text hazard. Is the
   landing's closing calc, the same four steps, a copy that should be a shared lemma, or a short
   standard pattern? The copying-state step is the citation that ledger TC-1 records.
6. **A1 dependence.** The checks ran on A1's ten lemmas declared before the file's text, because
   A1 is not yet in any olean tree. Is that overlay faithful to A1's head (`mkoverlay.py.txt` takes
   A1's added text from its diff, asserting exactly ten declarations)? Does anything in the
   landing depend on the overlay beyond A1's statements?

## Repository-side attestations (verify or challenge)

- **Elaboration** (against `oleans-lu2api`, the replayed tree after #161, with A1's lemmas
  overlaid; recipe `evidence/check.sh.txt`; the plain file's offset is 90 lines):
  `SavitchLanding-ax.out` reports only `savitch`'s existing sorry warning. Axioms:
  `spaceConstructible_poly` and `PSPACE_eq_NPSPACE` on `[propext, Classical.choice, Quot.sound]`.
- **Seal:** `SavitchSealed-ax.out` has exactly 12 errors, at the 12 controls (lines 161–180), and
  none in the sealed declarations (lines 182–343); the axioms are as above.
  `SavitchControlsUnsealed-ax.out`: with the seal line removed, the controls close (no error).
- **Definition scan** (`SavitchDefScan.out`): 15 TCSlib definitions, equal to the review's
  `probe/SCPRouteDefScan.out`.
- **Code identity** (`evidence/codeid/`): the landing's region, from `scp_tailδ` to the end of the
  proof, equals the consumer probe's with comments stripped. The theorem's name and line break
  are the only edit made before the comparison.
- **Freeze** (`evidence/freeze/freeze-Savitch.txt`): public 3 → 3, none added or removed; no
  statement changed; the one body change, `spaceConstructible_poly`, is authorized; private 0 → 8.
- **Lint** (`evidence/lint-*-SpaceComplexity.txt`): 0 FAIL, 82 WARN over 107 files, as at A1's
  head. The only changed line is Savitch's count, 139 → 282 lines and 0 → 8 privates. No line is
  over 100 characters.
- **Replay:** the downstream closure is 2 modules, `Savitch` and the `SpaceComplexity` facade
  (`evidence/down-lscp.txt`), chained from A1's merged-tree snapshot. **Pending:** the gate is
  dispatched before it, and A1's replay runs after #162 merges.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `campaign/standards/TEMPLATE.md`. Findings go verbatim into
`campaign/gates/77-scp-landing/findings.md`. The gate closes when it has zero blockers and zero
majors.

**Deliver your findings as a downloadable Markdown file named `scp-landing-findings.md`** (the
findings table and the verdict line, no other wrapping), and also paste its content in your reply.
