# Gate 158 resolutions

## Round 1: HOLD (0 blockers, 1 major, 8 minors, 13 notes; `findings.md`, verbatim)

Records-only resolutions are on the campaign branch. Three items need Seyoon's disposition
before round 2. They are marked **pending**.

- **G158-01 (major), pending.** Theorem 3.2's hypothesis. `ntime_hierarchy` assumes
  `f(n+1) + f(n) + n + 1 = o(g(n))`. The book assumes `f(n+1) = o(g(n))`. Without monotonicity
  of `f`, the auditor's parity-selected pair satisfies the book's hypothesis but not ours.
  `FIDELITY.md` now records row 3 as a genuine restriction and corrects the summary
  ("no statement is weaker" is withdrawn). The options are:
  - add a book-form corollary for monotone `f` (new public API, a small gated Lean PR). Its
    proof is short: `n ≤ f(n) ≤ f(n+1)` and `1 ≤ f(n+1)` give
    `f(n+1) + f(n) + n + 1 ≤ 4·f(n+1)`;
  - record the restricted scope only.

  Either option also needs a decision on the module docstring of `NTimeHierarchy.lean`, which
  says the linear-overhead universal machine "puts the theorem at book strength".
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
- **G158-06 (minor), classified; partly pending.** All 69 flags are in
  `evidence/lint/LINT-CLASSIFIED.json` and summarized in the register:
  - 39 are carried by the existing ruling;
  - 8 are prose false positives;
  - 16 are proof-sketch flags inflated by the signature, each with a body of at most 20 lines;
  - **6 are genuine and pending:** five proofs without sketches (three in `Mult`, one in
    `QueryReshape`, one in `NARMPSem`) and `Parse.lean`'s missing `## Main results` section.

  The existing three-kind ruling is not extended to them.
- **G158-07 (minor), corrected.** PLAN D3 now lists Exercise 4.7 (a certificate head moving
  both ways) beside Definition 4.19. It is distinct from the proved Example 4.7.
- **G158-08 (minor), corrected.**
  - Row 5 records `T(n) ≥ n` as a strengthening.
  - Row 11 explains `S + 1` by constant absorption: `SpaceConstructible S` forces
    `S(n) ≥ logSpace(n) ≥ 1`, so `S(n) + 1 ≤ 2S(n)`.
- **G158-09 (minor), pending.** `EXPCOM.lean`'s module docstring (lines 49 and 69) still calls
  `exists_uniformMachineCode` a "sorried existence". The theorem is proved. The options are
  repair, in the same small Lean PR as the other documentation items, or carry.
- **Notes.** G158-N1 to N6, C1 to C6 and the glossary need no change, except that C1, C4 and C6 follow
  G158-01, -05 and -06.
