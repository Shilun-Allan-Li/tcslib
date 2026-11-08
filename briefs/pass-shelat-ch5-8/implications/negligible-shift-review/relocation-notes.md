# Optional relocation of Negligible.comp_of_le

**Unapplied, unchecked internal factoring proposal.** The separate patch moves the existing theorem from `TCSlib/Cryptography/ZeroKnowledge/NP.lean` to `TCSlib/Cryptography/Foundations/Negligible.lean` under the unchanged full name `TCSlib.Cryptography.Negligible.comp_of_le`. It introduces no new API or duplicate proof. Gate06 source stays frozen.

Frozen source input: exact Git `3f6db40e1688c4a0bb922c9575dd3bd2157a650b` in `/Users/seyoonr/.codex/worktrees/ps-gate06-integration/tcslib-pass-shelat-ch2-4`.

- Patch SHA-256: `143eaf6789ad0395f22c8e8022cb3688ec640bb66f38dbab68b21a6b4f76962d`.
- Complete moved declaration, from `theorem` through proof, SHA-256: `b9cb83ec2cc7f981254ea1a8fb4e5678da77717544a02c6f6739500be6bed8c0`.

## Minimal changes

The destination inserts the theorem immediately after `Negligible.mono` and lists it in the module's results. Its new docstring describes the general parameter-change property as technical glue and gives a short English sketch. The complete formal header and proof are copied **byte for byte** from original NP source lines 288–297, including every existing nested tactic term. No new tactic block or proof step is authored.

The NP source removes that one declaration. Its section comment retains the Claim-124.d role, `ε(|f x|) = ε(p(|x|))`, and points to the foundational owner. All later uses keep their existing full name and proof text. All definitions, other headers/proofs, options and imports are unchanged. There is exactly one copy of the declaration after composing the patch; the global declaration, tactic-token and admission-token counts remain unchanged.

Both files are in `namespace TCSlib.Cryptography`. The theorem's explicit implicit binder `{μ : ℕ → ℝ}` remains intact, so the destination's surrounding `variable {μ ν : ℕ → ℝ}` contributes no extra parameter. The body refers only to its explicit variables, the destination's own `Negligible` definition and globally available arithmetic lemmas/tactics. It does not use NP's `open Complexity Turing LevinTransfer` context. Reading `Negligible` by the unchanged local proof is now owner-local.

## Import and cycle inspection

No direct import is added or removed. `Foundations/Negligible.lean` imports only three existing Mathlib modules, so the move adds no TCSlib dependency edge and cannot create an import cycle. NP already reaches the destination through the exact frozen import path:

```text
ZeroKnowledge.NP → ZeroKnowledge.NPLemmas → ZeroKnowledge.Defs → Foundations.Negligible
```

The existing Foundation imports already make the required arithmetic lemmas available. Source-level import traversal found, for example:

```text
Mathlib.Analysis.SpecificLimits.Normed
  → Mathlib.Data.Nat.Choose.Bounds
  → Mathlib.Algebra.Order.Ring.Defs
  → Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic

Mathlib.Analysis.SpecificLimits.Normed
  → Mathlib.Analysis.Asymptotics.Lemmas → Mathlib.Analysis.Asymptotics.Defs
  → Mathlib.Analysis.Normed.Field.Basic → Mathlib.Algebra.Order.Group.Pointwise.Interval
  → Mathlib.Algebra.Order.Field.Basic
```

The local pinned primary declarations are `pow_le_pow_left₀` at GroupWithZero/Unbundled/Basic.lean:451–456 and `one_div_le_one_div_of_le` at Field/Basic.lean:73–74. Their signatures match the unchanged proof's use. The destination already uses `pow_pos`, `one_div_le_one_div_of_le`, `exact_mod_cast` and `positivity` elsewhere, so no extra tactic import is suggested. This is a static availability check, not native elaboration.

Local Mathlib source SHA-256:

- `Mathlib/Algebra/Order/GroupWithZero/Unbundled/Basic.lean`: `c8a583903078c8e35bd5ede6816170f687408f623b8b80a995148a1b78eed092`.
- `Mathlib/Algebra/Order/Field/Basic.lean`: `7a0a7285fa3a0adad6ffeaae3dc254d68d1cb8573b0932507178b2ea111d8197`.

## Source fingerprints and later checking

| File | Frozen SHA-256 | Proposed SHA-256 | Lines |
| --- | --- | --- | --- |
| Foundations/Negligible.lean | `5e6d2c9e69dbfe012c36a92bad05ec27e691c044dae73a7277b9599902074e1a` | `22ab17586c533a1ebe196c28231d9dc2ccb05f9b03240f10a47ba3c55a611536` | 234 → 253 |
| ZeroKnowledge/NP.lean | `a324cf2acd579a86946f857e8c69fcd8e3f96fb08efc03f1902d1b5c6ba354fe` | `4ad7331f6e562f6495df5f1ab5cbf24b6a6bcdefd2f58354c8a6042fad850890` | 768 → 759 |

Root can later apply both hunks together on the isolated factoring front and check the destination, NP and affected consumers serially. The existing right-shift application then needs only the foundational import:

```lean
hμ.comp_of_le (fun n => n + s) (fun n => Nat.le_add_right n s)
```

Moving a stored theorem changes its module home and collector ownership. Future evidence for the factoring front must use that actual source and ownership; current frozen Gate06 evidence is not relabeled or reused as checking this move. No whole-file legacy failures or broader normalization transports are cleared by this proposal.

No source file was edited. No Lean/cache/build, app, other repository program, Git mutation or evidence mutation occurred. Only separate ignored patch/notes artifacts were saved; the prior API note remains separate.

**Not yet clear to merge — optional relocation is unapplied and needs root's later isolated native checks.**
