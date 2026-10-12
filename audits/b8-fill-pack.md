# External audit pack — B8 fill gate: a non-time-constructible function (`exists_not_timeConstructible`)

Campaign: Arora-Barak chapters 3-4 (`AroraBarakChapters3-4Plan.md` §4e, cluster B8). The
target is [AB09, Exercise 3.5]'s `Complexity.exists_not_timeConstructible`, in
`TCSlib/Complexity/Diagonalization/NotTimeConstructible.lean`: there is a function
`T` with `∀ n, n ≤ T n` that is not time-constructible. Its statement gate (phase P3.2) found it
**true** (`audits/ch3-p32-findings.md`, row 17 and the discussion of the HALT-bit witness), with
resolutions `audits/ch3-p32-resolutions.md`.

**A maintainer fill.** The drafted B8 brief's pre-ship probe
(`audits/evidence/b8/B8RouteProbe.lean.txt`) closed the whole route. Following the B1 light
half's precedent, the proof went straight into the file, with no agent batch (commit `a96a6ab9`,
PR #36, record `audits/b8-fill-record.md`). Like any fill, it goes to a **fill gate**: this
one. The attached patch is the whole change. Fill gates close on zero blockers and zero majors
(`workflow.md` §4), and the duplication rule (`audits/TEMPLATE.md`, failure mode 5) is in force.

**Every proof is kernel-checked**; the replay and axiom evidence is below. The audit object is:
- the frozen surface;
- the route's fidelity to the audited sketch, and the flagged appendix that records where it
  differs;
- the correctness of the witness and of each stage;
- duplication, and the one new Mathlib import;
- the documentation.

## What changed (verify)

| Class | Declarations |
|---|---|
| **Target body, `sorry` → proof** | `exists_not_timeConstructible` |
| **Privates, 0 → 14** | the `ntc`-prefixed helpers: the dyadic rank and un-rank, the witness `T n := n + [HALT (str n)]`, the four stages, the parity-corrected low-bit tail, the bit identity |
| **Imports** | one added, flagged: `Mathlib.Data.Nat.Digits.Lemmas` |
| **Docstrings** | the flagged **"Route as filled"** appendix; the module status, now "proved" |

## Brief for the auditor

1. **Freeze.** Re-establish it from the attached base (`NotTimeConstructible.base.lean.txt`, at
   `9b47f7b9`), the head and the patch: the statement is unchanged; only the target's body
   changed; the other changes are the 14 new privates, the appendix, the status line and the
   one import.
2. **The witness.** `T n := n + (if HALT c.toMachineCode (str n) = true then 1 else 0)` over the
   dyadic enumeration, with `rank s := codeBitsNat (s ++ [true]) − 1` and
   `str n := (n + 1).bits.dropLast`. Confirm that only `str (rank s) = s` is needed, that
   `∀ n, n ≤ T n` holds, and that the gate's monotonicity remark is not required by the
   statement.
3. **Route fidelity.** The audited sketch has four stages composed by
   `FinTM.exists_comp_partial`. The fill realizes stages (i)–(iii) through the primitive-recursive
   compiler `Turing.codePrim_machine`: the emitter `s ↦ 1^(rank s)`, read as a mapped range,
   with no hand-built counter. Stage (iv) reads the one bit where the two candidates differ: the
   low bit of `(T (rank s)).bits`, exclusive-or the rank's parity, branched with
   `FinTM.exists_cond`; no two-word comparator is used. Rule on whether this stays within the
   sketch and whether the parity correction covers the odd-rank carry the sketch names.
4. **The reduction to HALT.** Confirm that the composite machine computes
   `fun s => [HALT c.toMachineCode s]` on every `s`, so `Complexity.HALT_not_computable c` gives
   the contradiction, and that the classical case split on `HALT` identifies the output with the
   halting bit.
5. **The bit identity and the import.** `(codeBitsNat (s ++ [true])).bits = s ++ [true]` comes
   from Mathlib's `Nat.digits_ofDigits` and `Nat.digits_two_eq_bits`, through a new bridge
   `codeBitsNat = Nat.ofDigits 2`. Confirm that it is not a third copy of the private
   `bridgeNumber_bits` (`MathlibBridge`) or of `UHaltMachine`'s numbering, and whether the flagged
   Mathlib import is justified.
6. **Duplication.** The population screen gives 605 → 616 declarations and 376 → 376 pairs, with
   an identical pair list. The population's 12 files and the screen script are attached; rerun it.
7. **Documentation.** Check the "Route as filled" appendix and the status line against the proof
   as delivered.
8. **Size.** 235 lines. Say whether you disagree.
9. Report anything else the fill or its record misstates, in the standard table.

## Repository-side attestations (verify or challenge)

* **Freeze** (`audits/logs/b8-fill-freeze-lint.log`): the statement is unchanged; only the body
  changed, plus 14 privates; no new public; lint 0 FAIL, 0 WARN.
* **Axioms** (`audits/logs/b8-fill-axioms.log`): `[propext, Classical.choice, Quot.sound]`, with
  no `sorryAx`.
* **Replay** (`audits/logs/b8-fill-replay.log`, user-run): 2 modules (`NotTimeConstructible` and
  the `Diagonalization` facade) at `a96a6ab9`, **0 errors and 0 sorry warnings**.
* **Screen** (`audits/logs/b8-fill-screen-{before,after}.txt`): identical pair lists.
* **Route probe** (`audits/evidence/b8/B8RouteProbe.lean.txt`, with its output): the drafted brief's
  pre-ship check, which closed the route before the fill.
* Execution and freshness of the replay and probe are maintainer attestations.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md` (attached, with `policy.md` and `workflow.md`).
Findings go verbatim into `audits/b8-fill-findings.md`. The B8 fill gate closes when it has
zero blockers and zero majors; cluster B8 is then complete.
