# Ch2 fill campaign — Epoch 3, Batch A: the padding cluster

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch1`** — this exact branch, NOT
  `main`. Every file this brief cites exists only on it.
- Create your working branch off it (suggested name `fill/ch2-e3-A`). The
  required base is `b55180a8bb38b94427e75e63630aa6eab5fd6e95`; record it in
  `REPORT.md` and never rebase onto anything else.
- **Delivery is by zip, not PR or push**: `fill-ch2-e3-A.zip`, **flat**
  (`SHA256SUMS` at the root, every entry at the root), with `REPORT.md`, the
  full modified sources, the `git format-patch` series, a git bundle, the
  final sweep log, the axiom-print log, and `SHA256SUMS`.

## Context

Epochs 1 and 2 are complete and audited: 38 of the chapter's 59 admissions
are proved, including Theorem 2.6 in both directions, Exercise 2.1, the HALT
pair, and the full TMSAT package (`audits/ch2-epoch2-resolutions.md`, gate
CLOSED). Your batch is the **padding cluster** — the NTIME form of `NEXP`,
Theorem 2.22, and `EXP ⊆ NEXP` — and nearly every technique it needs is now
a proved, in-file precedent: the polynomial forward compiler
(`ntime_poly_subset_NP`), the B2 reverse NDTM host (`b2*`, 42 privates), the
banked guessing/normalization assets (`cont_*`), and the audited
machine-construction library (`Build/{Convention,Wrappers,Loop,Primitives}`,
two closed gates — consume its public contracts freely).

## Owned files and targets (in order)

- `TCSlib/Complexity/ClassNP/Nondeterminism.lean` (2,454 lines, recorded
  size exception):
  1. `ntime_expPow_subset_NEXP` (4 pts) — the exponential analogue of the
     proved `ntime_poly_subset_NP`; same verifier-machine shape, different
     arithmetic. The `a = 0` case is vacuous (no decider exists on the
     empty choice word), exactly as the docstring records.
  2. `NEXP_subset_iUnion_NTIME` (4 pts) — the exponential analogue of the
     proved `NP_subset_iUnion_NTIME`: an integrated reverse NDTM host. The
     B2 construction is the proved precedent in-file; its binding warnings
     carry over (below).
  3. `NEXP_eq_iUnion_NTIME` (1 pt) — antisymmetry of targets 1 and 2.
  4. `EXP_eq_NEXP_of_P_eq_NP` (8 pts) — Theorem 2.22 by the certificate
     route of the audited docstring sketch: the padded language through the
     (⇐) direction of the proved `mem_NP_iff_exists_length_le`, **no
     nondeterministic machines**; then the `EXP` decider by pad-emission +
     relocated captured `M_pad`.
  5. `P_ne_NP_of_EXP_ne_NEXP` (1 pt) — contraposition of target 4.
- `TCSlib/Complexity/ClassNP/EXP.lean` (2,534 lines, recorded size
  exception):
  6. `EXP_subset_NEXP` (8 pts) — the padding verifier: unique-split
     recovery by scanning `n ≤ m` with binary evaluation of `2^((n+1)^c)`,
     explicit rejection when no split exists (including `m = 0`),
     relocated captured decider run. The library's `exists_loopFindTM`
     (the split-search engine behind the proved `splitSolve`) and the
     catalog rows are the natural assets; the polynomial-width catalog
     instances do **not** cover the exponential split directly — adapt
     the engine, not the instance.

## Environment and verification

- Pinned toolchain (Lean 4.25.0, `cdd38ac5115b`; mathlib `029db123ddaa`).
  Setup once: `lake exe cache get`. **Never run `lake build`.**
- Bootstrap once:
  `while read -r m; do bash scripts/lean_check_tree.sh "$m" || break; done < scripts/ab_ch1_module_order.txt`
  (**57 modules**).
- Iterate: the owned module plus every later module in the order list.
  Final: the full fresh 57-module sweep, **zero `error:` lines**.
- **Axiom prints** on the final fresh tree: all six targets at most
  `[propext, Classical.choice, Quot.sound]`; `sorryAx` must not appear —
  **zero sanctioned admitted dependencies** in this batch. Kernel-traversal
  root verification: `audits/programs/ch2-e2-ClosureAxioms.lean` is the
  committed template.

## Ground rules (binding)

1. **File ownership.** Only the two owned files; only the six targets'
   proofs plus `private` helpers. List every new declaration in `REPORT.md`.
2. **Statement freeze.** No renames, re-signatures, restatements, or
   attribution edits. Docstring sketch appendices allowed, flagged,
   append-only.
3. **Escalation** on anything unprovable as stated: stop, record, deliver.
4. **No-touch on in-file proved material**: every existing private
   (including the deliberately retained evidence lemmas named in the module
   docstrings' E5 maintainer notes, e.g. `cont_poly_guess_phase`,
   `b2_unary_mask`, `b2_tables_coincide`) is citable and untouchable — no
   removal, renaming, or modification.
5. Docstrings stay. Precise imports; keep `set_option` headers.
6. **Continuation budget** (26 points): if exhausted, deliver a partial
   flat zip whose `REPORT.md` states exactly what is proved, which privates
   are admitted (allowed **only** in a partial delivery, each listed), and
   the frontier — the maintainer issues a continuation brief.

## The audited routes and binding warnings

The six in-file docstring sketches are the audited routes and are binding.
In particular:

- **Pre-validation bit bound** (phase-3 round-1 finding 1, embedded in the
  target-4 docstring): before any validity assumption, `E |x|`'s bit length
  is bounded through the parsed `x` being a substring of the input; the
  logarithmic-in-`|x'|` estimate holds only *after* the padding-length
  check and **must not be used to budget the evaluation itself**.
- **Both exact checks** in target 4's verifier: pad all-`true` of exactly
  the evaluated length AND `|u|` exactly equal — the bounded outer witness
  condition replaces neither.
- **The B2 reverse-host warnings carry over to target 2**: a guessing
  phase is not a decider; dispatch on an **actual completed** scheduler
  state, never a mathematical upper bound as a native clock; phase
  boundaries are input-length functions only; prove table coincidence
  outside guessing as a definitional fact of your construction.
- **No untimed composition, no bare computability substitutions**
  (phase-2 note 3, campaign-wide). Deadline enlargements only ever enlarge
  the deadline, never a certificate length (phase-3 discipline).
- Small-length absorption uses the truncation argument the docstrings name
  (`NTIME.mono` / `DTIME`'s constant); budget padding on the NDTM side is
  `Turing.FinNDTM.AcceptsWithin.mono` — don't re-derive absorption.

## Out-of-scope sorries you will see (leave untouched)

Everything in `SAT.lean` (3B, concurrent), `CookLevin/Snapshot.lean` (3C,
concurrent), `Tautology.lean` (3D, concurrent, and 4B), and
`CookLevin/Hardness.lean` (E4). On completion your two owned files are
admission-free.

## REPORT.md checklist

- [ ] All six targets filled (or the frontier exact); the route of each
      mapped to its discharging lemmas; the split-recovery, pad-evaluation,
      and reverse-host seams called out explicitly.
- [ ] Base hash; new privates listed; final file sizes.
- [ ] Axiom prints for all six targets (standard triple at most, roots
      empty); final sweep log tail; diff touches only the two owned files;
      archive flat.
- [ ] Requested shared lemmas / escalations — or "none".

## Known pitfalls at this pin (hard-won)

- The E2/B2 lists carry over verbatim (`briefs/ch2-epoch2-batchB.md`,
  `briefs/ch2-e2cont-batchB2.md`): `Function.update_of_ne`; `dsimp only`
  after `cases hs : cfg.state`; `omega` needs beta-reduced non-`Fin`
  goals; `MultiTapeTM.runFrom_succ_eq_step'`/`…_step` peel opposite ends;
  `moveInputPos` clamps; destructure `ComputesInTime` via
  `simp only [FinTM.ComputesInTime, MultiTapeTM.ComputesInTimeAndSpace]`.
- `Nat.bits` needs `Mathlib.Data.Nat.Bits`; `Nat.bits (2^w − 1) =
  List.replicate w true` is proved in-file (EXP.lean's continuation layer)
  — cite, don't re-derive.
- Exponential arithmetic: `Nat.one_le_two_pow`, `Nat.pow_le_pow_right`,
  `Complexity.succ_pow_le` (in-file, proved); normalize degrees before
  comparing, as the docstrings' `e = c + d + 2` patterns do.
- The `+ 1` padding of the NTIME unions is deliberate (deviations list);
  match it exactly — statements are frozen.
