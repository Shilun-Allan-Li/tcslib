# Sub-agent A worklog (gsw-core, F1 Gadget + F2 Noise)

Worktree `/home/user/gsw-A`, base `486f44f84`. Logs under `logs/`.

- 2026-11-16T08:05Z setup check of Gadget at base (setup-check-gadget.log): 5 sorry warnings, 0 errors.
- 08:08Z probe-001 (`probes/NamesA.lean`): #check of Mathlib names at the pin: `Matrix.vecMul_add`,
  `Matrix.add_vecMul`, `Matrix.vecMul_smul` (scalar on the matrix), `Matrix.smul_vecMul` (scalar on the
  vector), `Matrix.vecMul_neg`, `Matrix.vecMul_zero`, `Matrix.vecMul_vecMul`, `Matrix.mul_apply`,
  `Bool.toNat_eq_zero`, `Bool.toNat_le`, `Int.natAbs_natCast`, `ZMod.natCast_zmod_val`,
  `Int.cast_natCast`, `Finset.sum_eq_zero_iff`, `Finset.sum_eq_single`, `List.all_cons`,
  `Finset.induction_on` (explicit `a s` in the insert case), `Matrix.mulVec_transpose`.
- 08:09Z gadget-002: `digits_decomposeVec` by `rw [Lossy.digits_eq, decomposeVec_eq, Equiv.apply_symm_apply]`. OK.
- 08:09Z gadget-003: `gadget_mulVec_decomposeVec`: `Lossy.gadget_mulVec` at `j`, `simp only
  [digits_decomposeVec, digit_val]`, `change` both sides to their `∑` (Mathlib `mulVec`/`dotProduct`/
  `transpose` reduce; `Lossy.gadget` is not unfolded), `← ZMod.natCast_zmod_val`, `← Int.cast_natCast`,
  `← h`, `Int.cast_sum`, termwise `gadget_apply`, `Int.cast_mul`, `Int.cast_natCast`. OK first try.
- 08:09Z gadget-004: `gadget_mul_decompose`: `ext i c`, `Matrix.mul_apply`, `lift_apply`,
  `decompose_apply`, `exact` the column instance of the previous lemma. OK.
- 08:09Z gadget-005: `decomposeVec_block_eq_false`: `digits_val` at `j`, simp `digits_decomposeVec`,
  `digit_val`, `hj`, `ZMod.val_zero`; `Finset.sum_eq_zero_iff`, `Nat.mul_eq_zero`,
  `Bool.toNat_eq_zero`, `pow_ne_zero`. OK.
- 08:10Z gadget-006: `errorSum_decomposeVec_le`: `← finProdFinEquiv.sum_comp`, `Fintype.sum_prod_type`,
  `Finset.sum_eq_single j₀` (off blocks by `decomposeVec_block_eq_false`), then
  `LWE.binaryErrorSum_bound` with `m := ℓ`. OK. Gadget: 0 errors, 0 sorries.
- 08:10Z gadget-007: proof-sketch paragraphs updated to the delivered proofs; recheck 0/0; widths ≤ 100.
- 08:11Z noise-008 (after Gadget rechecked in gadget-007): `encrypts_gadget`, `encrypts_zero`, `.mono`,
  `.add`, `.neg`, `.sub`, `.sum` all through `encrypts_iff`; 0 errors, two unused-simp-arg linter
  warnings (`Pi.smul_apply` in `encrypts_gadget`/`encrypts_zero`), removed in the next edit.
- 08:12Z noise-009: `Encrypts.mul` (witness `j ↦ ∑ᵢ e₁ i·(decompose P C₂ i j).toNat + x₁·e₂ j`;
  `Matrix.vecMul_vecMul` both ways, `Matrix.add_vecMul`, `Matrix.smul_vecMul`, `gadget_mul_decompose`,
  local `hX` reading `e₁ᵗ X` by `change` to its `∑` + `lift_apply`/`Int.cast_sum`; bound by
  `LWE.binaryErrorSum_bound` and `Int.natAbs_mul`), `.mul_bit` (`.mono`, `Int.natAbs_natCast`,
  `Bool.toNat_le`), `.mul_le` (Bool identity by `cases … <;> rfl`, `Nat.succ_mul`), `.nand`
  (`nand_eq`, `.sub` of `encrypts_gadget` and `.mul_bit`, `.mono` for `0 + ·`), `encrypts_chain`
  (induction on `Forall₂`, `chain_nil`/`chain_cons`, `List.all_nil`/`List.all_cons`, local Bool
  identity `hand`, `id_eq`, `mul_assoc`, ring for the noise). 0 errors, 0 sorries, first try.
- 08:12Z noise-010: proof-sketch paragraphs updated to the delivered proofs, step comments in
  `encrypts_chain`; 0/0; widths ≤ 100. `git diff` removes only `sorry` lines and old sketch lines.
- 08:13Z axioms-011 (`probes/AxiomsA.lean`): all 17 targets depend only on propext,
  Classical.choice, Quot.sound.
- 08:14Z seals: Gadget 4 variants all exit=0 errors=0 sorry=0; Noise running (host lock).
- 08:16Z seals done (`seals/seal-run-summary.txt`): Gadget and Noise, all 4 variants (A_coe, A_strict,
  B_coe, B_strict): exit=0 errors=0 sorry=0 harness=True (Gadget requested/active 51, Noise 59);
  both error forms re-counted in every raw log: 0; each log has its GSWCORE-EOF marker.
  Seal dirs copied to `seals/`, probe sources to `probes/`.
- REPORT.md: the harness refused to let a sub-agent write a report `.md` file; the report is in the
  final hand-back message to the lead.
