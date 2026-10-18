# Ch2 fill campaign — E2 continuation, Batch B: the Theorem-2.6 compilations

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch1`** — this exact branch, NOT
  `main`. Every file this brief cites exists only on it.
- Create your working branch off it (suggested name `fill/ch2-e2cont-B`),
  record the base commit hash in `REPORT.md`. The required base is
  `64d82f84dfbbfcd7b5d69689dc0f37fb3d3116c4`.
- **Delivery is by zip, not PR or push**: `fill-ch2-e2cont-B.zip`,
  **flat** (`SHA256SUMS` at the root), with `REPORT.md`, the full
  modified source, the `git format-patch` series, a git bundle, the
  final sweep log, the axiom-print log, and `SHA256SUMS`.

## Context — what changed since your predecessor's checkpoint

The original `briefs/ch2-epoch2-batchB.md` is **binding in full** — in
particular its verbatim phase-2 invariant table and the five-step
certificates↔choice-words reconstruction contract, and the no-untimed-
composition rule. The checkpoint
(`audits/ch2-epoch2-agent-reports/batchB.md`) banked the certificate
equivalence and two proved prepared-configuration phases (`choiceCore`,
the native simulation with exact time `|u| + 1`; `choiceCopy`, the
three-tape copier) and reduced target 1 to the single goal
`choiceVerifier N (2*a) c ∈ P`. Since then the campaign shipped the
fully proved **machine-construction library**
(`TCSlib/Complexity/TuringMachine/Build/`, 23 contracts, zero
admissions; statement and proof gates both CLOSED) — the startup, split,
capture, branch, and decision glue your predecessor's frontier list
named are now library calls.

## Owned file (modify this and nothing else)

- `TCSlib/Complexity/ClassNP/Nondeterminism.lean` — targets, in order:
  1. `ntime_poly_subset_NP` (6 pts): close `choiceVerifier ∈ P`.
     Library route: the unique split is
     `computesFunInTime_splitSolve` at the batch's own length equation
     (`i + C'·(i+1)^e = total` with your coefficient/degree — the
     split-search contract's shape; connect to your private
     `certificateSplit` by a semantic bridge lemma, minding that the
     library's `solveSplit` convention differs by the recorded
     coefficient shift, round-2 vocabulary note); guard malformed
     inputs with `pairValid`-style staging or your split's failure
     branch; relocate-and-capture the **proved** `choiceCore` phase
     from its prepared configuration (the startup your predecessor
     listed as missing is exactly what `Turing.capture_run` +
     the `Build/Wrappers.lean` host templates + `timed_rewind`'s
     pattern now provide); finish with the decision glue
     (`mem_P_of_dtime_le`/`mem_P_iff`).
  2. `NP_subset_iUnion_NTIME` (8 pts): the ⊇-direction NDTM
     construction. The **nondeterministic guessing table and the
     branch-correspondence argument remain bespoke by design** (the
     library covers deterministic machines only — D5's recorded scope);
     the deterministic verifier phase inside it reuses the same
     relocation/capture assets as target 1. The five-step contract is
     binding verbatim.
  3. `NP_eq_iUnion_NTIME` (1 pt): antisymmetry of 1 and 2.

  The padding cluster in the same file remains **epoch 3 — not yours**.

## Rules on the superseded in-file privates

Your predecessor's `certificateSplit`/`choiceVerifier`/`choiceCore`/
`choiceCopy` families are proved and in-file: **cite them freely; do not
remove, rename, or modify them** (dedup is a recorded E5 task). New
helpers private, distinctly named, listed.

## Sanctioned `sorryAx`

**None.** Everything cited is proved (the library, the epoch-1 run
calculus, your predecessor's phases). On completion the file's remaining
admissions are exactly the five epoch-3 padding declarations.

## Environment, ground rules, verification

As the original E2 brief, with the 57-module order update
(`scripts/ab_ch1_module_order.txt` now includes the four `Build/`
modules). Pinned toolchain; `lake exe cache get` once; **never
`lake build`**; iterate the owned module plus later modules; final full
fresh 57-module sweep, zero `error:` lines; kernel-traversal root
verification (`audits/programs/ch1-libfill-ClosureAxioms.lean` is the
template). Exclusive ownership; statement freeze absolute; escalation
over alteration; docstrings stay. **15 points; continuation per the B2
precedent if exhausted** — fill strictly in the order above.

## Out-of-scope sorries you will see (leave untouched)

The padding cluster in your own file (epoch 3); `enumMachine_contracts`
(2A-cont, concurrent); `mem_NP_iff_exists_length_le` (2C-cont); the
`TMSAT.lean` `D-*` sites (2D-cont); everything in E3/E4 files.

## REPORT.md checklist

- [ ] Three targets filled in order (or the frontier exact); the
      invariant-table rows and the five-step mappings per the original
      brief; the library contracts consumed, named per use.
- [ ] The `solveSplit`↔`certificateSplit`-style bridge lemma's exact
      coefficient translation stated.
- [ ] Base hash; new privates listed; final file size.
- [ ] Axiom prints for all three targets: at most the standard triple,
      roots empty.
- [ ] Final sweep log tail; diff touches only `Nondeterminism.lean`;
      archive flat.

## Known pitfalls at this pin

The original E2-B list carries over verbatim, plus:
- The library's `splitSolve` output is the threaded
  `pairEncode (take i) (drop i)` with `[]` on failure — your pipeline
  consumes it through the extractors or a semantic equality to your own
  split, not by re-parsing informally.
- `capture_run`'s host-agreement hypothesis constrains **all** read
  tuples at embedded states — define your controller's table by the
  transformer (`captureAction`) on those states, as the `Build/`
  templates do, rather than proving agreement after the fact.
- The phase boundaries must stay input-length-functions only (five-step
  contract, step 2) — the library's seam discipline helps but does not
  discharge that NDTM-side obligation for you.
- No untimed composition anywhere (phase-2 note 3): the library's
  contracts are all timed; keep your glue at `ComputesInTime`
  granularity.
