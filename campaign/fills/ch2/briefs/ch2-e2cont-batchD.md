# Ch2 fill campaign — E2 continuation, Batch D: the TMSAT `D-*` sites

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch1`** — this exact branch, NOT
  `main`. Every file this brief cites exists only on it.
- Create your working branch off it (suggested name `fill/ch2-e2cont-D`),
  record the base commit hash in `REPORT.md`. The required base is
  `64d82f84dfbbfcd7b5d69689dc0f37fb3d3116c4`.
- **Delivery is by zip, not PR or push**: `fill-ch2-e2cont-D.zip`,
  **flat** (`SHA256SUMS` at the root), with `REPORT.md`, the full
  modified source, the `git format-patch` series, a git bundle, the
  final sweep log, the axiom-print log, and `SHA256SUMS`.

## Context — what changed since your predecessor's checkpoint

The original `briefs/ch2-epoch2-batchD.md` and the checkpoint record
(`audits/ch2-epoch2-agent-reports/batchD.md`) remain binding — in
particular the exact-value emission discipline (never majorize the
certificate length `Q`; the three-case table), the deadline formula, and
the obligation-to-lemma map. Two things changed:

1. **The bridge is discharged.** `timed_universal_quantitative` is a
   proved theorem (the maintainer exported
   `Turing.timed_universal_concrete` from Chapter 1 and closed your
   predecessor's escalation exactly as its REPORT prescribed, via
   `tmsat_concrete_coefficient`). `TMSAT_mem_NP`'s only remaining root
   is `D-MEM`.
2. **The machine-construction library shipped, fully proved**
   (`TCSlib/Complexity/TuringMachine/Build/`, 23 contracts, zero
   admissions; both gates CLOSED). The three `D-*` obligations were
   named customers of its data-plumbing layer; the approved coverage
   mapping is D5 (`audits/ch1-infra-r3-findings.md` item 7), and the
   **canonical pairing-assembly recipe** — building
   `pairEncode (f x) (g x)` for computed `f, g` via
   `pairDup`/`pairMapSnd`/`pairConcat`/`pairSnd` — is recorded verbatim
   in `machine-library-design.md` §9c. D-MEM's D5 row names its residual
   obligations explicitly; they are yours.

## Owned file and targets

- `TCSlib/Complexity/ClassNP/TMSAT.lean` — the three `D-*` admissions,
  in order (12 pts; `TMSAT_NPComplete` closes automatically):
  1. **`D-MEM`** (inside `TMSAT_mem_NP`, ≈ line 964; 5 pts). The
     verifier: parse the nested quadruple
     `pairEncode (pairEncode (bits t) α) (pairEncode x u)` by iterated
     `pairFst`/`pairSnd` with `pairValid` guards (`cond` is the proved
     branch); the unary-to-binary clock conversion is `pairMapSnd` with
     a length-counting payload transform (the D5 row's named route —
     `lengthBits`' machine on the payload); the D5-named residuals —
     the timed extraction of `w.take n` from the parsed unary clock,
     the all-true unary-shape checks, and the complete-answer test
     `[true, true]` — are your bespoke pieces; assemble the
     well-formed request and invoke the **proved bridge** through your
     predecessor's proved `tmsat_simulator_total`/`tmsatAnswer_accept`/
     `tmsat_simulation_budget` chain.
  2. **`D-WRAP`** (inside `TMSAT_NPHard`, ≈ line 1152; 3 pts). The D5
     route verbatim: `pairValid` guard + **`pairConcat`**
     (`pairEncode x u ↦ x ++ u`) + the captured verifier run + the
     `cond` constant-reject branch realizing `tmsatWrapperOutput`'s
     malformed-`[false]` clause.
  3. **`D-EMIT`** (inside `TMSAT_NPHard`, ≈ line 1190; 4 pts). The §9c
     recipe applied to the two **exact** unary runs: `Q` by your
     predecessor's proved `tmsat_exact_certificate_bits` three-case
     discipline (its case machines are `computesFunInTime_polyUnary`
     instances and `computesFunInTime_const`-style chains — exact
     values, never majorized), `T'` by the proved
     `tmsat_deadline_bound` formula via `polyUnary` at the prescribed
     `(D, 2er - 1)` parameters; pair them per §9c, retain `x` via
     `pairDup`, and apply `computesFunInTime_pairEncodeFixed α₀` for
     the outer layer. `tmsat_quad_injective` and
     `tmsat_reduction_correct` (proved) finish the hardness argument as
     the docstring's audited route prescribes.

## Rules on the superseded in-file privates

`polyUnaryTM`/`poly_unary_computes` were harvested into the library's
catalog; both copies are proved. **Cite either; remove or modify
neither** (dedup is a recorded E5 task). New helpers private,
distinctly named, listed.

## Sanctioned `sorryAx`

**None.** The bridge is proved, the library is proved, the in-file
semantic layer is proved. On completion `TMSAT_mem_NP`, `TMSAT_NPHard`,
and `TMSAT_NPComplete` all print at most the standard triple with empty
root sets — your REPORT includes all three prints.

## Environment, ground rules, verification

As the original E2 brief, with the 57-module order update
(`scripts/ab_ch1_module_order.txt`). Pinned toolchain;
`lake exe cache get` once; **never `lake build`**; iterate the owned
module plus later modules; final full fresh 57-module sweep, zero
`error:` lines; kernel-traversal root verification
(`audits/programs/ch1-libfill-ClosureAxioms.lean` is the template).
Exclusive ownership; statement freeze absolute; escalation over
alteration; docstrings stay (append-only notes; the `D-*` CONTINUATION
markers may be converted to historical notes when their sites close).
The file is at 1,206 lines under its recorded exception — report the
final size. **12 points; continuation per the B2 precedent if
exhausted** — fill strictly MEM → WRAP → EMIT.

## Out-of-scope sorries you will see (leave untouched)

`enumMachine_contracts` (2A-cont, concurrent); the `Nondeterminism.lean`
cluster (2B-cont + epoch 3); `mem_NP_iff_exists_length_le` (2C-cont);
`EXP_subset_NEXP`; everything in E3/E4 files.

## REPORT.md checklist

- [ ] Three sites filled in order (or the frontier exact); the original
      brief's obligation-to-lemma map completed for every remaining
      open row; the library contracts and §9c recipe steps named per
      use; the D5 residual obligations' discharge points named.
- [ ] The exact-value discipline attested: `Q` emitted exactly per the
      three-case table; only the deadline majorized.
- [ ] Base hash; new privates listed; final file size.
- [ ] Axiom prints: all three TMSAT targets (and the bridge) at most
      the standard triple, roots empty.
- [ ] Final sweep log tail; diff touches only `TMSAT.lean`; archive
      flat.

## Known pitfalls at this pin

The original E2-D list carries over verbatim, plus:
- `pairEncode` nesting: get the quadruple's associativity from the
  statement, not memory — the parse order is `pairFst` for
  `pairEncode (bits t) α`, then `pairSnd` twice down the spine.
- C1 (`pairMapSnd`) transforms the **payload only**; any
  cross-component step (the clock count against `x`'s length) goes
  through the §9c retained-whole-request pattern, never a payload
  function peeking at the head.
- The extractors' `getD []` conflates failure with a genuinely empty
  component — guard with `pairValid` **before** extraction at every
  spine level (the audit's recorded design).
- `polyUnary` instances emit `C·(n+1)^e` of **their own input's**
  length — when the emission must be a function of a *component's*
  length, route through `pairMapSnd` so the component is the payload.
- The bridge's budget is consumed through `tmsat_simulation_budget`
  (proved) — do not re-derive the coefficient arithmetic.
