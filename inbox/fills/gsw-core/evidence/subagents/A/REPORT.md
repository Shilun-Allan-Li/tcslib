# Sub-agent A report (saved by the lead)

Sub-agent A returned its report as its final message; the harness refused a sub-agent-written
`.md` report file, so the lead saved it here verbatim in substance (status, checks, files,
Rule 10, overlap, searches). Lead verification of the integrated files is in `evidence/logs/`.

## Status
F1 (Gadget): `digits_decomposeVec`, `gadget_mulVec_decomposeVec`, `gadget_mul_decompose`,
`decomposeVec_block_eq_false`, `errorSum_decomposeVec_le`: proved.
F2 (Noise): `encrypts_gadget`, `encrypts_zero`, `Encrypts.mono`, `.add`, `.neg`, `.sub`, `.sum`,
`.mul` (exact `x₁.natAbs * β₂` term kept), `.mul_bit`, `.mul_le`, `.nand`, `encrypts_chain`: proved.
No target false; every proof follows the brief's route. Worktree `/home/user/gsw-A`, base
`486f44f8414c20a2d21e452c44de8b8c8d8513a0`; no commits, no git, no `lake`, no other file edited;
every Lean run through `chk.sh` or `seal.py run`.

## Checks (this folder)
- Gadget `logs/gadget-007.log`: exit 0, 0 errors (both forms), 0 sorry warnings, no warnings.
- Noise `logs/noise-010.log`: same, checked after Gadget's final olean.
- Axioms `logs/axioms-011.log` (probe `probes/AxiomsA.lean`): the 17 targets use only propext,
  Classical.choice, Quot.sound.
- Seals (`-DmaxErrors=0`): Gadget A_coe/A_strict/B_coe/B_strict exit=0 errors=0 harness=True,
  requested=active=51; Noise the same, requested=active=59. Both error forms recounted: 0.
  Copied to `seals/seal-Gadget/`, `seals/seal-Noise/`, summary `seals/seal-run-summary.txt`.
- Width ≤ 100; Gadget 204 → 236 lines, Noise 235 → 321.
- Files: Gadget sha256 `34b2c1b6e75681e0ffb3b409ae4df2086fc4d440e2e4691ff7a75d079e068618`,
  Noise sha256 `e0e47ee0c7f08aff1f8ee4244171fd40b1450969bc744f3fec84881f07bec082`.

## Sketch edits
Gadget rewritten: `gadget_mulVec_decomposeVec`, `gadget_mul_decompose`,
`decomposeVec_block_eq_false` (last sentence), `errorSum_decomposeVec_le`; unchanged:
`digits_decomposeVec`. Noise rewritten: `encrypts_gadget`, `encrypts_zero`, `.add`, `.neg`,
`.mul`, `.mul_bit`, `.mul_le`, `.nand`, `encrypts_chain`; unchanged: `.mono`, `.sub`, `.sum`.
Step comments in `errorSum_decomposeVec_le`, `Encrypts.mul`, `encrypts_chain`.

## New auxiliary declarations
None.

## Rule 10
Gadget reads foreign definitions only via `Lossy.digits_eq`, `Lossy.digits_val`,
`Lossy.gadget_mulVec`, `Equiv.apply_symm_apply`; its own via `decomposeVec_eq`, `gadget_apply`,
`lift_apply`, `decompose_apply`. One `change … at h` reads Mathlib's transpose/mulVec/dotProduct
of `(Lossy.gadget …)ᵀ.mulVec x j` as a `∑` (`Lossy.gadget` stays folded).
Noise reads Gadget only via `gadget_mul_decompose`, `lift_apply`; its own via `encrypts_iff`,
`mul_eq`, `nand_eq`, `chain_nil`/`chain_cons`. One `change` reads Mathlib's vecMul as a `∑`.
Every `simp`/`rw` selector is a lemma or local hypothesis; `Bool.toNat` reduces only inside
`cases … <;> rfl`.

## Overlap and reuse
1. `Encrypts.mul`, inline `hX` (`e₁ᵗ · lift X` is the residue of the integer binary sum):
   relatives the inline `herr` of `Regev.encrypt_residual`
   (`TCSlib/Cryptography/Encryption/PublicKey/Regev/Basic.lean:119`) and the last step of
   `Lossy.residual_conceal` (`TCSlib/Cryptography/TrapdoorFunctions/Lossy/Matrix.lean:128`);
   same cast step; not reusable (inline in other proofs), three lines of glue.
2. Bool identities `((a && c).toNat : ℤ) = a.toNat * c.toNat` and `(!c).toNat = 1 − c.toNat`
   (inline in `Encrypts.mul_le`, `Encrypts.nand`, `encrypts_chain`) by `cases … <;> rfl`; no
   core/Mathlib lemma at the pin; the lead's inline `hmsg` in `Eval.homAnd_encrypts` is the same
   identity.
3. Reused directly: `LWE.binaryErrorSum_bound` (`TCSlib/Cryptography/LWE/Basic.lean:79`),
   `Lossy.gadget_mulVec` (`Lossy/Gadget.lean:214`), `Lossy.digits_val` (`Lossy/Gadget.lean:183`);
   not `Regev.subsetError_bound` / `Lossy.error_sum_bound` (specializations).

Searches: `grep -rn` over `TCSlib/` for `Int.cast_sum`, `error_sum_bound|subsetError_bound`,
`toNat` in GSW files; core `Init/Data/Bool.lean` and `Mathlib/Data/Bool/*.lean` for
`theorem toNat_`; Mathlib and batteries for `toNat_and|toNat_not|toNat_mul`; `#check` probe
`probes/NamesA.lean` (`logs/probe-001.log`).

## Scope and promotion requests
None.
