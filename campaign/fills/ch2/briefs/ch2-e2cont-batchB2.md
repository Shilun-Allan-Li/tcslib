# Ch2 fill campaign — E2 continuation, Batch B2: the reverse NDTM host

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch1`** — this exact branch, NOT
  `main`. Every file this brief cites exists only on it.
- Create your working branch off it (suggested name `fill/ch2-e2cont-B2`),
  record the base commit hash in `REPORT.md`. The required base is
  `e72d95bf35ebf09c21aae7e1959e5d895a345686`.
- **Delivery is by zip, not PR or push**: `fill-ch2-e2cont-B2.zip`,
  **flat** (`SHA256SUMS` at the root), with `REPORT.md`, the full
  modified source, the `git format-patch` series, a git bundle, the
  final sweep log, the axiom-print log, and `SHA256SUMS`.

## Context

The last open construction of chapter 2's epoch 2. Three documents are
binding, in order: `briefs/ch2-epoch2-batchB.md` (the phase-2 invariant
tables and the **five-step certificates↔choice-words reconstruction
contract, verbatim and binding**; the no-untimed-composition rule),
`briefs/ch2-e2cont-batchB.md`, and — read it first — your predecessor's
REPORT at `audits/ch2-epoch2-agent-reports/batchB-cont.md`: its
"Reverse five-step contract" table says exactly what is proved versus
remaining, its continuation section is a **five-step work plan written
against the banked assets**, and its warnings are binding (repeated
below). The forward compilation is done (`ntime_poly_subset_NP` is
admission-free); nine of the epoch's ten targets are closed; yours are
the last two.

## Owned file and targets

- `TCSlib/Complexity/ClassNP/Nondeterminism.lean` — targets, in order:
  1. `NP_subset_iUnion_NTIME` (8 pts). The exact remaining goal is
     displayed in your predecessor's REPORT: from the certificate
     characterization and a verifier decider, produce
     `N : FinNDTM Bool` deciding `L` within `K·(n + C(n+1)^c + 1)^r`.
     Banked and proved, in-file: the native guessing table
     (`contGuessTM`, built on the library's `captureAction`
     transformer), its physical-position extraction and coverage
     (`contSelect`/`cont_select_surjective`/`cont_guess_coverage` — at
     actual write positions, zero-coefficient case included), the
     polynomial scheduler instance (`cont_poly_guess_phase`), the
     envelope arithmetic (`cont_guess_time_bound`, exact coefficient
     `K(C+1)^r·2^(r·max 1 c)`), and the final packaging
     (`cont_guess_normalize` — it closes the target once handed a
     whole-decider contract). The forward construction's loader,
     relocation, and capture layers are proved precedents in-file.
     Your work is the **integrated host**, per the predecessor's plan:
     (1) the native host preserving the original input and installing
     the length-only scheduler/countdown — the scheduler relocation
     seam is explicitly missing (see warnings); (2) embed the guessing
     table with disjoint source/administrative tapes and translate the
     write mask into complete branch words including the startup
     offset, reusing `cont_guess_coverage` at the actual scheduler
     completion; (3) assemble `x ++ u`, prepare the relocated verifier
     with blank source tapes and virtual head one, prove the two NDTM
     tables coincide outside guessing, capture the completed output
     (halting emission included), one verdict bit; (4) all-branch
     totality, exact certificate length, acceptance ⟺ membership, a
     **common upper bound** (actual halting times may vary per
     branch); (5) the displayed envelope, then `cont_guess_normalize`.
  2. `NP_eq_iUnion_NTIME` (1 pt): antisymmetry of the proved forward
     target and target 1.

## Binding warnings (the predecessor's, restated)

- `contGuessTM` is a **phase**, not the missing decider; its
  scheduler's completed state is a live, stationary return state — it
  never claims all-branch halting. The host supplies that.
- `cont_poly_guess_phase` runs the scheduler on the **unary word of
  length `n`**, not on an arbitrary original input: relocating the
  library's unary generator to a prepared unary input, or proving an
  equivalent normalization of its input reads, is an explicit missing
  seam — the generator's function-level contract alone does not assert
  value-independent running times on arbitrary inputs.
- The host must dispatch on an **actual completed scheduler** (for
  example its first halt) and prove that seam; do not infer a native
  clock from an upper bound.
- Phase boundaries are input-length functions only (five-step contract,
  step 2) — value-dependent timing breaks witness extraction.
- The NDTM guessing side is bespoke by design (the library covers
  deterministic machines); the deterministic sub-phases reuse the
  proved in-file and library assets freely.

## Rules on in-file material

Everything your predecessors proved — the epoch-2 checkpoint's 32
privates, the continuation's 36 — is citable and **untouchable** (no
removal, renaming, or modification; dedup is E5). The padding cluster
(five admissions) is epoch 3; the third target's current admission body
is yours to fill only after target 1.

## Sanctioned `sorryAx`

**None.** Everything cited is proved. On completion the file's only
admissions are the five epoch-3 padding declarations, and the epoch-2
gate condition — all ten targets admission-free — is met.

## Environment, ground rules, verification

As the prior briefs: pinned toolchain (Lean 4.25.0, `cdd38ac5115b`;
mathlib `029db123ddaa`); `lake exe cache get` once; **never
`lake build`**; bootstrap the 57-module order
(`scripts/ab_ch1_module_order.txt`); iterate the owned module plus
later modules; final full fresh 57-module sweep, zero `error:` lines;
kernel-traversal root verification
(`audits/programs/ch1-libfill-ClosureAxioms.lean` is the template).
Exclusive ownership; statement freeze absolute; escalation over
alteration; docstrings stay (append-only notes; the predecessor's
checkpoint-note tails may be extended per the established pattern).
The file is at 1,670 lines under its recorded exception — report the
final size. **9 points; continuation per the B2 precedent if
exhausted.**

## Out-of-scope sorries you will see (leave untouched)

The padding cluster in your own file (epoch 3); `EXP_subset_NEXP`;
everything in E3/E4 files (`SAT.lean`, `Tautology.lean`,
`CookLevin/*`). Nothing else remains admitted anywhere in scope.

## REPORT.md checklist

- [ ] Both targets filled (or the frontier exact); the five binding
      steps mapped to your discharging lemmas, with the scheduler
      relocation seam, the table-coincidence proof, and the
      common-bound argument called out explicitly.
- [ ] Base hash; new privates listed; final file size.
- [ ] Axiom prints: both targets at most the standard triple, roots
      empty — and, since this closes the epoch, prints for all ten
      epoch-2 targets.
- [ ] Requested shared lemmas / escalations — or "none".
- [ ] Final sweep log tail; diff touches only `Nondeterminism.lean`;
      archive flat.

## Known pitfalls at this pin

The E2-B and e2cont-B lists carry over verbatim, plus:
- `FinNDTM` branch words: the guessing table ignores its choice bit on
  administrative transitions — coverage is at the **actual** physical
  write positions (`contSelect`), never "the first `Q(n)` choices".
- `cont_guess_normalize` wants all-branch halting through
  `acceptsWithin_iff_of_halts` — prove totality for **every** branch,
  accepted or not, on **every** input, in or out of `L`.
- The two tables must coincide outside the guessing phase as a
  **definitional fact of your construction** (the original brief's
  pitfall), not a lemma fought afterwards.
- Budget padding at the end is `Turing.FinNDTM.AcceptsWithin.mono`
  (proved, epoch 1) — don't re-derive absorption.
