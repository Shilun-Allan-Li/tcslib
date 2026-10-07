# Ch2 fill campaign — E3 continuation, Batch A: the padding cluster

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch1`** — this exact branch, NOT
  `main`. Every file this brief cites exists only on it.
- Create your working branch off it (suggested name `fill/ch2-e3cont-A`),
  record the base commit hash in `REPORT.md`. The required base is
  `b75b67715ac2a8b09df5a7c61dd0ca898a1762d7`.
- **Delivery is by zip, not PR or push**: `fill-ch2-e3cont-A.zip`,
  **flat** (`SHA256SUMS` at the root), with `REPORT.md`, the full
  modified sources, the `git format-patch` series, a git bundle, the
  final sweep log, the axiom-print log, and `SHA256SUMS`.

## Context

The continuation of epoch 3's batch A. Three documents are binding, in
order: `briefs/ch2-epoch3-batchA.md` (the original contract: routes,
warnings, ground rules — all carry over verbatim), your predecessor's
REPORT at `audits/ch2-epoch3-agent-reports/batchA.md` — **read it
first**: its "Proved components and binding seams" table says exactly
what exists, its "Exact first-target frontier and continuation plan" is
your work plan, and its warnings are binding — and this brief. The
predecessor banked 35 proved `e3_*` privates: the split semantics, the
exponential choice-word verifier, the native binary evaluator
(`e3ShiftTM`/`e3_exp_bits_timed`), the `exists_loopFindTM` adaptation
(`e3_split_of_body` — it finishes target 1 the moment the body exists),
the verifier assembly (`e3_verifier_of_split`), and the closed
degree-zero case. All citable, all untouchable.

**Concurrent maintainer work, not yours:** an emitter-layer extension of
the machine library is being designed in parallel
(`machine-library-design.md` §11). It does **not** bind you and will not
land before you finish. Build the split-search body **natively,
in-file**, per your predecessor's plan; do not touch anything under
`TCSlib/Complexity/TuringMachine/Build/`. If the maintainer later
generalizes your body into the library, that dedup is a recorded
maintainer task — deliver the bespoke construction without regard to it.

## Owned files and targets (in order)

- `TCSlib/Complexity/ClassNP/Nondeterminism.lean` (3,013 lines, recorded
  exception):
  1. **The native exponential split-search body** (closes
     `ntime_expPow_subset_NEXP`, the file's one local admission). The
     exact remaining existential is displayed in-source at the admission
     site, and your predecessor's REPORT restates its two contracts
     (startup within `A·(|w|+1)^(r+1)` to the anchor with no earlier
     anchor visit; scratch-restoring rounds with positive first return,
     halting with exactly `pairEncode (w.take n) (w.drop n)` on the
     solving candidate, the exact canonical seam otherwise). The
     five-step continuation plan in the REPORT is your work plan:
     one-past-end by a positive silent stall; evaluator run on the
     prepared virtual candidate input with captured output and dispatch
     at **actual completed source states**; suffix length in binary and
     whole-word canonical comparison, **charging evaluation before any
     validity check** and absorbing the `|w|+2` candidate-length factor
     in the pre-validation envelope (no unjustified logarithmic bound);
     success emission of the threaded split with **no leaked evaluator
     output**; failure restore + increment + exact seam. The proved
     `e3_split_of_body` and `e3_verifier_of_split` then close target 1
     with no further machine construction.
  2. `NEXP_subset_iUnion_NTIME` (4 pts): the exponential reverse NDTM
     host. The proved B2 construction (`b2*`) is the in-file precedent;
     **the B2 warnings are binding**: the guessing phase is not a
     decider; dispatch on an actual completed scheduler, never an upper
     bound as a native clock; phase boundaries input-length-only; table
     coincidence outside guessing as a definitional fact. The pad-length
     evaluator differs (binary `E n`, written by your target-1
     machinery's vocabulary); the banked `cont_guess_*` assets and the
     library capture/loop contracts are available as they were to B2.
  3. `NEXP_eq_iUnion_NTIME` (1 pt): antisymmetry of targets 1–2.
  4. `EXP_eq_NEXP_of_P_eq_NP` (8 pts): Theorem 2.22 by the audited
     certificate route — the padded language through the (⇐) direction
     of the proved `mem_NP_iff_exists_length_le`, no nondeterministic
     machines; the **pre-validation bit bound** (phase-3 round-1 finding
     1) and **both exact checks** (pad all-`true` of exactly the
     evaluated length AND `|u|` exactly equal) are binding, as the
     docstring records; then the `EXP` decider by pad emission +
     relocated captured `M_pad`.
  5. `P_ne_NP_of_EXP_ne_NEXP` (1 pt): contraposition of target 4.
- `TCSlib/Complexity/ClassNP/EXP.lean` (2,534 lines, recorded exception):
  6. `EXP_subset_NEXP` (8 pts): the padding verifier per its audited
     docstring sketch — your target-1 body machinery is the natural
     engine for its unique-split recovery (same equation shape at
     `C = 1`); explicit rejection when no split exists, including
     `m = 0`.

## Sanctioned `sorryAx`

**None.** Everything cited is proved. On completion both owned files are
admission-free, and the tree's admissions drop to SAT's reduction (3B
continuation, concurrent), `TAUTOLOGY_coNPComplete`, and the Hardness
five.

## Environment, ground rules, verification

As the prior briefs: pinned toolchain (Lean 4.25.0, `cdd38ac5115b`;
mathlib `029db123ddaa`); `lake exe cache get` once (both E3 hosts'
cache-recovery patterns are on record if the upstream step fails —
disclose whatever you do); **never `lake build`**; bootstrap the
57-module order; iterate owned + later modules; final full fresh
57-module sweep, zero `error:` lines; kernel-traversal root verification
(`audits/programs/ch2-e2-ClosureAxioms.lean` is the template).
Exclusive ownership; statement freeze absolute; escalation over
alteration, always; docstrings append-only; every existing private
citable and untouchable. **≈ 25 points; continuation per the B2
precedent if exhausted — prefer completing targets in order over
starting later ones.**

## Out-of-scope sorries you will see (leave untouched)

`SAT_reducible_SAT3` (3B continuation, concurrent);
`TAUTOLOGY_coNPComplete` (4B); everything in `CookLevin/Hardness.lean`
(4A).

## REPORT.md checklist

- [ ] Targets filled in order (or the frontier exact); the body's
      startup/round contracts, the dispatch-at-actual-halt seam, the
      pre-validation envelope absorption, and the restore/seam proof
      called out explicitly and mapped to discharging lemmas.
- [ ] Base hash; new privates listed; final file sizes.
- [ ] Axiom prints: every closed target at most the standard triple,
      roots empty; final sweep log tail; diff touches only the two owned
      files; archive flat.
- [ ] Requested shared lemmas / escalations — or "none".

## Known pitfalls at this pin

The original 3A brief's list carries over verbatim, plus:
- `e3_split_of_body`'s hypotheses are exact full-configuration
  equalities at the seam (`Cfg.ofWords` anchor discipline, §9b/§9c) —
  build the body to land them, don't weaken and bridge afterwards.
- The candidate invariant permits `s.length ≤ |w| + 1`; the one-past-end
  round must still take a **positive** number of steps (the audited
  0 < t discipline) — a silent stall, not an identity.
- Budget padding on the NDTM side is `Turing.FinNDTM.AcceptsWithin.mono`;
  deterministic absorption is `NTIME.mono`'s truncation pattern — don't
  re-derive either.
