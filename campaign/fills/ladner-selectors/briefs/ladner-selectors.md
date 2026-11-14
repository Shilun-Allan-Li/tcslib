# Ladner fill 1 (Codex): the two selector theorems in `Diagonalization/Ladner.lean`

## Repository and branch — read this before anything else

- Repository: `https://github.com/Shilun-Allan-Li/tcslib` (the same repository as your exchange
  checkout).
- **Base commit:** `50bb801a28ffd86ce7b47c91d47c257ab024fade`, the head of branch
  `codex/ab34-ladner-readers` (the campaign `complexity/arora-barak-ch3-4` plus the approved owner
  readers, under review as gate 135). Fetch it (`git fetch origin codex/ab34-ladner-readers`) and
  work on a local branch off it (suggested name `fill/ladner-selectors`). Record the base hash in
  `REPORT.md`. Never rebase.
- **Delivery is by zip and exchange push, not PR:** see "Delivery" at the end.

## What this is

Ladner's theorem [AB09, Theorem 3.3 and its proof] is stated in `Diagonalization/Ladner.lean`
with six admitted targets (gate 128 audited the statements; do not change them). A Codex route
draft (bundled, `campaign/items/ladner/fill-routes-request/delivery/ladner-fill-routes.md`) plans
all six; Seyoon ruled its interfaces on 2026-11-14 (`campaign/backlog.md`, P3.4). **Your targets
are the two selector theorems**, in this order:

1. `Complexity.ladnerH_bounded_of_mem_P : SAT_H ∈ P → ∃ C, ∀ n, ladnerH n ≤ C` (route §4);
2. `Complexity.ladnerH_unbounded_of_not_mem_P :
   SAT_H ∉ P → ∀ C, ∃ N, ∀ n ≥ N, C ≤ ladnerH n` (route §5).

They are independent of the memo computation (`ladnerH_polyTime`) and of the other targets. Target 1
complete beats two partials.

## Owned file (modify this and nothing else)

`TCSlib/Complexity/Diagonalization/Ladner.lean`: the two target proofs, new `private` helpers in
namespace `Complexity`, and, if your route needs it, the import
`TCSlib.Complexity.ClassP.ModelInvariance` (approved; also approved, if needed:
`TCSlib.Complexity.ClassP.BinaryArith.Loops`). Every other declaration of the file — the four
definitions, the six proved readings, the other four admitted targets and `ladner` — stays
**byte-identical**, including their docstrings. No other file changes.

## Ground rules (binding)

1. **Statement freeze.** The two target statements and every existing declaration are frozen.
2. **Rule 10** (`campaign/maintainer/WORKFLOW.md` §2, bundled): read other files' TCSlib
   definitions only through their published equations. Core and Mathlib definitions may reduce by
   `rfl`, `decide` or `show`, but are never passed to `simp`, `rw` or `unfold`. In particular do
   not unfold `P`, `PolyTimeComputable`, `NP`, `SAT`, `DecidesInTime`, `indicator`,
   `ComputesInTime`, `expCode`, `CodeTM.toFinTM` or the uniform-code choice. The readers you need
   exist at the base:
   - `Complexity.polyTimeComputable_iff` (R1, ClassNP/PolyTime);
   - `Turing.FinTM.decidesInTime_iff` (R5, ClassP/DTIME);
   - `Turing.MultiTapeTM.indicator_of_mem` / `indicator_of_not_mem` (R6, Deterministic);
   - `Complexity.polyTimeReducible_iff`, `NPHard_iff`, `NPComplete_iff` (R2–R4; not needed here).
   The route draft's §2 table lists the existing API it checked (`mem_P_iff_one_work_tape`,
   `FinTM.toCodeTM_computesInTime_iff`, `MachineCode.decode_encode_pad`,
   `UniformMachineCode.simulator_accepts`/`_rejects`, `FinTM.exists_comp_on_image`,
   `mem_P_of_test`, `ComputesInTime.output_unique`, `not_computesInTime_zero`, …). If a step needs
   a reading that has no published equation, **stop and escalate** (E-READER in `REPORT.md`, with
   the reader's proposed statement and home); do not unfold.
3. **No new public declarations**, no new files, no `@[simp]` attributes, no `sorry`, `admit` or
   new axioms in delivered code.
4. **Standards** (`policy.md`, bundled): every new declaration has a docstring citing [AB09,
   Theorem 3.3 and its proof] or a library declaration; every proof over 20 lines carries a
   `**Proof sketch.**`; no campaign labels, gate or finding names, or paths in Lean text.
5. **Route.** The route draft's §4–§5 helper plan (bundled) is guidance, not binding: its helper
   names and statements are a starting point (they elaborate at the campaign pin with admitted
   bodies). Keep its risk notes: encode indices canonically (an all-false suffix is insufficient);
   absorb the coefficient as well as the degree; do not demand total Boolean output at a zero
   deadline; use the one-work-tape theorem before code conversion; the simulator's time is
   polynomial in the **numeric** deadline, not its bit length; keep the conclusion's `∀ n ≥ N`.
6. **Escalation** on anything unprovable as stated (E-STATEMENT), any needed reading without an
   equation (E-READER), or any needed host that does not exist (E-HOST). A clean escalation is a
   valid delivery.

## Environment and verification

Follow the bundled fill-environment addendum (v2.6). **Never run `lake build`.** Bootstrap the
import closure of `Ladner.lean` at the base commit into your own scratch olean tree (as your route
probes did), one Lean process at a time. Final checks, all reported with exit codes:

- `Diagonalization/Ladner.lean`: zero errors; the only `sorry` warnings are the four remaining
  admitted targets (`ladnerH_polyTime`, `SAT_H_mem_NP`, `SAT_mem_P_of_padSAT_NPHard`,
  `SAT_H_intermediate`) and `ladner`'s dependence, none in your code;
- `#print axioms` for both targets: at most `propext`, `Classical.choice`, `Quot.sound`;
- the facade `Diagonalization.lean` with zero errors.

## REPORT.md checklist

- [ ] 2/2, or target 1 plus a frontier; the base hash.
- [ ] Every new `private` declaration with its role.
- [ ] Every other-file TCSlib definition each proof reaches, and the published equation used for it.
- [ ] Final check outputs, the two axiom prints, and `git diff --stat` touching only `Ladner.lean`.
- [ ] Environment deviations, as in the route delivery.

## Delivery

Make `fill-ladner-selectors.zip` with `REPORT.md`, the full delivered `Ladner.lean`, the patch
against the base (`git diff 50bb801a… -- TCSlib`), and the check logs. Push it, after
`git pull --rebase` and without force or any other change, to
`arora-barak-ch3-4/inbox/fill-ladner-selectors/` on the exchange branch, and also attach it in
chat. Cumulative checkpoint zips (`fill-ladner-selectors-checkpoint-N.zip`) to the same folder are
welcome on long runs. Do not push to any other branch and do not open a pull request; the
maintainer lands the fill by PR for Seyoon to merge.
