# Ch2 fill campaign — E2 continuation, Batch C: the Exercise-2.1 verifier machines

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch1`** — this exact branch, NOT
  `main`. Every file this brief cites exists only on it.
- Create your working branch off it (suggested name `fill/ch2-e2cont-C`),
  record the base commit hash in `REPORT.md`. The required base is
  `64d82f84dfbbfcd7b5d69689dc0f37fb3d3116c4`.
- **Delivery is by zip, not PR or push**: `fill-ch2-e2cont-C.zip`,
  **flat** (`SHA256SUMS` at the root), with `REPORT.md`, the full
  modified source, the `git format-patch` series, a git bundle, the
  final sweep log, the axiom-print log, and `SHA256SUMS`.

## Context — what changed since your predecessor's checkpoint

Three documents are binding, in order: the original
`briefs/ch2-epoch2-batchC.md` (the audited two-verifier construction and
its edge-case obligations), the checkpoint record
(`audits/ch2-epoch2-agent-reports/batchC.md` — the full semantic layer
is proved: `stripCertificate`/`certificateSplit` families, both witness
equivalences, all seven audited edge cases), and the checkpoint's own
continuation document (`audits/ch2-epoch2-agent-reports/
batchC-continuation.md` — the two exact remaining goals with their
contexts). The HALT pair is **done** (proved at the checkpoint; its last
admission root closes with the concurrent 2A continuation), so
`Reductions.lean` is no longer owned. Since the checkpoint, the campaign
shipped the fully proved **machine-construction library**
(`TCSlib/Complexity/TuringMachine/Build/`, 23 contracts, zero
admissions) whose threaded/parser family was built with **your two
goals as named customers** — the approved coverage mapping is D5
(`audits/ch1-infra-r3-findings.md` item 7 / `ch1-libfill-resolutions.md`).

## Owned file and targets

- `TCSlib/Complexity/ClassNP/NP.lean` — the two inline goals inside
  `mem_NP_iff_exists_length_le` (6 pts total):
  1. `pairedVerifier C c V ∈ P`. D5 route: `pairValid`-guarded pipeline
     (`computesFunInTime_cond` is the proved branch); extract with
     `pairFst`/`pairSnd`; the **exact-width** test
     `|u| = C(|x|+1)^c` needs both orientations — `pairLenCheck` at
     `(C, c)` gives one; the reverse orientation is assembled per the
     recorded pairing-derivation recipe (`machine-library-design.md`
     §9c, the audit's `H/s/t` construction) — conjoin; then
     `pairConcat` and the captured run of `V`'s decider
     (`capture_run` with your controller as host); decision glue.
     Your proved `pairedVerifier_pair`/`pairedVerifier_malformed`
     connect the machine's indicator to the predicate.
  2. `paddedVerifier C c V ∈ P`. D5 route, **with the mandatory
     coefficient shift**: the split search is
     `computesFunInTime_splitSolve` at **`(C + 1, c)`** — the recorded
     vocabulary equality is `solveSplit (C+1) c = certificateSplit C c`
     (round-2 note 5; same-parameter equality is FALSE — prove the
     shifted bridge lemma, plus `splitAtLastTrue = stripCertificate`);
     then `computesFunInTime_stripLast` for the marker strip;
     `pairLenCheck` at **`(C, c)`** for the original-bound re-check
     (the audited rule: fitting the enlarged region does not authorize
     a witness); guards reject missing-split and no-marker before the
     old verifier is consulted; finish through target 1's paired
     decider on `pairEncode x u`. Your proved `paddedVerifier_*` family
     supplies every semantic identification.

## Rules on the superseded in-file privates

Nothing in `NP.lean` is superseded — your semantic layer is the spec
side the machines must meet, and it stays. (The `Reductions.lean`
`prefixTM`/`fixedPair` privates are subsumed by catalog entries, D4;
that file is not yours and the dedup is an E5 task.)

## Sanctioned `sorryAx`

**None.** The library, Chapter 1, and your semantic layer are all
proved. On completion `mem_NP_iff_exists_length_le` prints at most the
standard triple with an empty root set — and with the concurrent
2A-continuation integrated, the whole `NP.lean`/`Reductions.lean` pair
goes admission-free.

## Environment, ground rules, verification

As the original E2 brief, with the 57-module order update
(`scripts/ab_ch1_module_order.txt`). Pinned toolchain;
`lake exe cache get` once; **never `lake build`**; iterate the owned
module plus later modules; final full fresh 57-module sweep, zero
`error:` lines; kernel-traversal root verification
(`audits/programs/ch1-libfill-ClosureAxioms.lean` is the template).
Exclusive ownership; statement freeze absolute (including the two
goals' surrounding proof structure — you are filling the two `sorry`s,
not restructuring the audited equivalence proof); escalation over
alteration; docstrings stay. **6 points; continuation per the B2
precedent if exhausted.**

## Out-of-scope sorries you will see (leave untouched)

`enumMachine_contracts` (2A-cont, concurrent — the HALT pair's root
until it lands); the `Nondeterminism.lean` cluster (2B-cont + epoch 3);
the `TMSAT.lean` `D-*` sites (2D-cont); `EXP_subset_NEXP`; everything
in E3/E4 files.

## REPORT.md checklist

- [ ] Both goals filled; each audited edge case's machine-side
      discharge point named (the original brief's seven-row table is
      the rubric); the library contracts consumed, named per use; both
      vocabulary bridge lemmas stated with their exact coefficients.
- [ ] Base hash; new privates listed; final file size.
- [ ] Axiom prints: `mem_NP_iff_exists_length_le` at most the standard
      triple, root-verified empty.
- [ ] Requested shared lemmas / escalations — or "none".
- [ ] Final sweep log tail; diff touches only `NP.lean`; archive flat.

## Known pitfalls at this pin

The original E2-C list carries over verbatim, plus:
- **The coefficient shift is load-bearing**: `solveSplit` at the same
  `(C, c)` as `certificateSplit` is wrong at `C = c = n = 0` — the
  audit's own counterexample. P10 at `(C+1, c)`, P8 at `(C, c)`.
- `splitSolve`'s threaded output carries the *original input* as the
  pair head — that is exactly what lets `pairLenCheck` re-check the
  original bound after stripping; don't discard it and re-measure.
- `stripLast` operates on the *payload* of a valid pair (it guards
  internally); feed it `pairEncode x v`, not bare `v`.
- The exact-width conjunction: build the reverse orientation by the
  §9c recipe verbatim (`pairSnd ∘ pairConcat` over nested encodes) —
  C1 alone cannot make a payload depend on the head component.
- Your `certificateSplit` searches indices with `n + (C+1)(n+1)^c =
  total` — the library equation is `i + C'(i+1)^e = m` over the
  *candidate*; align the variable roles in the bridge lemma carefully
  (the search variable is the input-prefix length in both, but the
  bound coefficient differs by the shift).
