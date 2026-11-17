# Gate 158 resolutions

## Round 1: HOLD (0 blockers, 1 major, 8 minors, 13 notes; `findings.md`, verbatim)

The records-only resolutions went to the campaign branch first (`12a3ce18`). Seyoon ruled on
the three remaining items on 2026-11-17, and the repair PR carries their Lean repairs together
with these records.

- **G158-01 (major), repaired in the repair PR.** Theorem 3.2's hypothesis. `ntime_hierarchy`
  assumes `f(n+1) + f(n) + n + 1 = o(g(n))`, while the book assumes `f(n+1) = o(g(n))`. Without
  monotonicity of `f`, the auditor's parity-selected pair satisfies the book's hypothesis but
  not ours. **Seyoon (2026-11-17): add the book form for monotone `f`**, mirroring Theorem 3.1's
  pair. Seyoon approved both new public theorems:
  - `Complexity.ntime_hierarchy_book`: `NTIME f ⊊ NTIME (g + 1)`;
  - `Complexity.ntime_hierarchy_book_of_pos`: `NTIME f ⊊ NTIME g` when `g` never vanishes.

  Both follow through the private `nh_book_dom`: `f(n) ≤ f(n+1)` and `n + 1 ≤ f(n+1)` give
  `f(n+1) + f(n) + n + 1 ≤ 3·f(n+1)`. Their axioms are `propext`, `Classical.choice` and
  `Quot.sound` (`evidence/r2-repair/BookProbe.*`). The module docstring now gives the
  counterexample and no longer says that the linear overhead alone reaches book strength.
  `FIDELITY.md` row 3 and §Major record the result: the book's form is covered for monotone
  `f`, and non-monotone `f` remains a disclosed restriction.
- **G158-02 (minor), corrected.** Row 1 now names `Complexity.time_hierarchy` (Diagonal:550)
  with its actual hypothesis `(f(n) + n + 1)^2 = o(g(n))`. The book-form coverage is attributed
  to `time_hierarchy_book` (:786) and `time_hierarchy_book_of_pos` (:799). The parameterized
  core is `DiagSimulator.time_hierarchy` (:310).
- **G158-03 (minor), corrected.** Row 4's book column is now `NTIME(n) ⊊ NTIME(n^1.5)`.
  Lean's `NTIME_linear_ssubset_square` is disclosed as a weaker illustration: a larger exponent
  and a positive normalization. An exact form would need a constructible integer
  normalization of `n^1.5`; it is not added.
- **G158-04 (minor), corrected.** Row 18: AB09 Exercise 4.1 supplies the budget (`SU(α,t,x)`).
  No divergence remains beyond the fixed binary encoding and pairing order.
- **G158-05 (minor), reconciled.** `CARRIED-REGISTER.md` now has:
  - a section for the refactor plan's register: CH34-D3, RW-1 and the `zfBFallback` residual,
    each with its ruling, location, reason and pointer;
  - the optional items of REFACTOR-PLAN §3.2, listed as optional scope;
  - R2c's recorded reason (361 more lines and 10 net screen pairs, `R2C-SCANNER.md`);
  - the 712 stale blueprint entries and draft PR #362;
  - the duplicate readers already in the tree from #354, now marked apart from the prospective
    ch2-4 overlap.
- **G158-06 (minor), classified and repaired.** All 69 flags are in
  `evidence/lint/LINT-CLASSIFIED.json` and summarized in the register:
  - 39 are carried by the existing ruling;
  - 8 are prose false positives;
  - 16 are proof-sketch flags inflated by the signature, each with a body of at most 20 lines;
  - **6 were genuine.** Seyoon (2026-11-17) chose to repair them in the repair PR, which adds
    proof sketches to `mult_contribution`, `mult_next_column`, `mult_validate_field`,
    `compQ_length_le` and `searchDown_run`, and adds `Parse.lean`'s `## Main results`.

  The existing three-kind ruling is not extended. Touching the two Mult docstrings brought
  their proofs under the seal check, and both failed it: they reached `astep` and `AReach` by
  unfolding. Both now cite `astep_inc` and `astep_half`. In the same way, `searchDown_run` now
  cites `preS_of_ins` in place of `simp [PreS]`, which the proof-syntax sweep flagged in run 2.
  `mult_validate_field` cites `canon_bits` in place of `simp [Canon]`, flagged in run 3. The
  evidence is from run 4; the logs of runs 1–3 are kept.
- **G158-07 (minor), corrected.** PLAN D3 now lists Exercise 4.7 (a certificate head moving
  both ways) beside Definition 4.19. It is distinct from the proved Example 4.7.
- **G158-08 (minor), corrected.**
  - Row 5 records `T(n) ≥ n` as a strengthening.
  - Row 11 explains `S + 1` by constant absorption: `SpaceConstructible S` forces
    `S(n) ≥ logSpace(n) ≥ 1`, so `S(n) + 1 ≤ 2S(n)`.
- **G158-09 (minor), repaired in the repair PR.** `EXPCOM.lean`'s module docstring no longer
  calls `exists_uniformMachineCode` a "sorried existence" in the design note or in `expCode`'s
  entry, and the round labels in those sentences are gone (Seyoon, 2026-11-17).
- **Notes.** G158-N1 to N6, C1 to C6 and the glossary need no change, except that C1, C4 and C6 follow
  G158-01, -05 and -06.
