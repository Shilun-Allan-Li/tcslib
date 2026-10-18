# External audit pack — Phase 3 skeleton + fill round 1

Audits commit `f8621285` on `complexity/arora-barak-ch1`. Two things happened since
the closed phase-2 loop (`audits/phase2-resolutions.md`): **(a)** 20 of the 28
outstanding `sorry`s were replaced by real, machine-checked proofs, together with 16
new supporting declarations, and **(b)** the phase-3 skeleton landed — machine
encodings and the universal machine, statements only (5 new `sorry`s; 13 total).
Record findings in `audits/phase3-findings.md`.

**Repository-side attestations** (verify or challenge, but they need not be redone
blind): a comment-stripped git comparison against the phase-2 gate commit `fb91cf88`
shows **no previously audited declaration signature changed and none was removed**;
all 18 modules elaborate with zero errors; the 8 remaining phase-1/2 `sorry`s are
textually unchanged from their audited forms.

## What changed

**Filled (no longer `sorry`; proofs are Lean-checked, so audit *statements* of the
new supporting lemmas, not tactics):** `ComputesInTime.mono`, `output_length_le`,
`output_prefix`; all six oracle obligations (`step_eq_of_ne_qQuery`,
`queryString_length_le`, `runFrom_workTapes_blank`, `runFrom_ofMultiTapeTM`,
`computesInTime_ofMultiTapeTM`, `runFrom_plainEmptyOracle`); `DTIME.mono`,
`DTIME_eq_empty_of_exists_zero`; `mem_P_of_dtime_le`, `mem_P_iff`,
`dtime_one_subset_P`; `PAL_mem_P`; `one_work_tape_binary` (chaining the two still-
`sorry`d simulations); the three ModelInvariance corollaries; and
`computesFunInTime_id`, proved with an explicit one-state copy machine (`idTM`) and
its run invariant — the first fully machine-checked concrete computation in the model.

**New public supporting declarations to blind-restate:** `Turing.succ_pow_le`;
`OracleTM.workTapePos_step_le`, `OracleTM.workTapes_step_eq_of_ne`;
`Cfg.embedOracle_inputSymbol`, `Cfg.embedOracle_workTapeSymbols`,
`Cfg.embedOracle_state_eq_none`, `Cfg.embedOracle_output`, `Cfg.embedOracle_apply`,
`Cfg.embedOracle_init`; `OracleTM.step_ofMultiTapeTM`,
`OracleTM.step_plainEmptyOracle`. (Private helpers — `idTM`, `idTM_run`,
`apply_workTapes_eq_of_ne`, `runFrom_workTapes_invariant` — are internal but attached
for completeness.)

**Still `sorry` from phases 1-2 (8, all heavy constructions, statements unchanged
since their audited rounds):** `computesFunInTime_const`, `computesFunInTime_comp`,
`alphabet_reduction`, `one_work_tape`, `nonnegative_heads`, `oblivious_of_mem_DTIME`,
`timeConstructible_id`, `PAL_mem_DTIME_linear`.

**New phase-3 surface (5 `sorry`s + definitions) — the main blind-restatement
target:** `Encoding.lean` (`CodeTM`, `CodeTM.toFinTM`, `pairEncode`, `MachineCode`,
`MachineCode.decode_encode` (proved), `exists_machineCode`, `exists_codeTM`) and
`Universal.lean` (`universal`, `universal_quadratic`, `timed_universal`).

## Brief for the auditor

Ground rules as in all previous rounds (trusted surface; no blanket approval).
Priority order:

1. **Blind-restate the phase-3 declarations** and compare against [AB09, §1.4,
   §1.4.1, Theorem 1.9, pp. 19-21]. This is new, unaudited surface.
2. **Blind-restate the new public supporting lemmas** (list above): each is now a
   *proved* statement others will build on — a wrong statement here is worse than a
   wrong sorry.
3. **Spot-check the fill round**: confirm the 8 remaining sorries match their audited
   forms and that nothing in the newly proved surface trivializes a downstream
   obligation (e.g. a helper lemma that accidentally assumes what a simulation must
   prove).
4. Assess the attestations in the header.

## Specific questions

1. `pairEncode` (doubled bits + `[false, true]` separator + verbatim second string):
   is this actually self-delimiting — can the doubled region always be parsed
   unambiguously from the left (pairs are `00`/`11` until the first `01`)? Any edge
   case with empty `x` or empty `α`?
2. `MachineCode`: is `decode_encode_pad` (recovery under `true`-padding **of valid
   codes only**) the right weakening of [AB09]'s convention, and does it genuinely
   give property 2 (infinitely many representations)? Is totality-by-type the right
   rendering of property 1? Is the abstract-scheme design (statements relative to any
   `MachineCode`) faithful to the chapter, or does anything downstream (diagonalization
   in phase 4!) need a *fixed* scheme with additional properties — e.g. computability
   of `decode` by a machine, which the current spec does **not** demand? This is the
   question we most want scrutinized: phase 4's `HALT` and `UC` need `Mα(α)`-style
   self-application, and an uncomputable `decode` would trivialize nothing here but
   might block phase 4's reductions.
3. `exists_codeTM`: is the per-input iff (`ComputesInTime` both ways) strong enough
   for the universal-machine chaining, or does the chain need output/timing in a form
   this iff loses?
4. `universal`: quantifier order (`∃ U, ∀ M, ∃ C, ∀ x out t`) versus
   [AB09, Theorem 1.9] — faithful? Is the **linear** bound `C · (t + 1)` for
   already-normal-form coded machines correct (the table scan is constant per step),
   and is the deviation note honest that the book's quadratic appears only in
   `universal_quadratic`?
5. `universal_quadratic`: function-level statement (via `ComputesFunInTime`) rather
   than [AB09]'s per-machine phrasing — anything lost? Constants composition
   `C_U · (c₁ (T+1)² + 1) ≤ C (T+1)²` valid?
6. `timed_universal`: are the two cases exhaustive and correctly phrased (note the
   second is `∀ output, ¬ComputesInTime` — "does not halt within `t`")? Is
   `true :: output` / `[false]` a sound failure convention (can a successful `true ::
   output` ever collide with the failure output `[false]`? — `true ≠ false`); is the
   quadratic clock budget right; and does the statement's use of `Nat.bits t` for
   `⌞t⌟` match `TimeConstructible`'s convention?
7. `idTM` (proved): does the invariant `idTM_run` (live state, head at `t + 1`,
   output = first `t` bits) plus the final halting step actually witness
   `ComputesFunInTime id (fun n => 1 * (n + 1))`? Sanity-check the empty-input case
   (`t = 0`, halts at step 1 with output `[]`).
8. Adversarial instantiations to attempt: `CodeTM` with `numStates = 0` through
   `universal`; `pairEncode [] α`; a `MachineCode` whose `encode` is constant (does
   anything break, i.e. do the specs secretly permit degenerate schemes that make
   `universal` false or vacuous?); `t = 0` through all three universal statements.

## Scope

| Item | Where |
|---|---|
| Files under audit | `TCSlib/Complexity/TuringMachine/{Encoding,Universal,Composition,Oracle,Finite}.lean` primarily; all sixteen modules attached |
| Source text | Arora & Barak 2009, §1.4-§1.4.1 and Theorem 1.9 (PDF pp. 45-47), plus earlier sections for the filled lemmas |
| Context | `AroraBarakChapter1Plan.md` (decision log), `policy.md`, prior audit records in `audits/` |
| Out of scope | tactic scripts (Lean-checked); statements confirmed in closed rounds, beyond the spot-check |

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | blocker / major / minor / note | | | | |

Severity guide: **blocker** = a downstream phase would build on a wrong statement;
**major** = fixable but materially misleading; **minor** = edge case or
naming/attribution defect; **note** = observation, no change required.
