import Mathlib

open Finset Complex

set_option maxHeartbeats 0

set_option relaxedAutoImplicit false

set_option autoImplicit false

set_option linter.unusedSectionVars false

namespace ZkFourier
noncomputable def rootOfUnity (k : ℕ) : ℂ :=
  Complex.exp (2 * ↑Real.pi * I / (k : ℂ))
end ZkFourier

namespace ZkFourier
noncomputable def toOmega {k : ℕ} [NeZero k] (a : ZMod k) : ℂ :=
  rootOfUnity k ^ a.val
end ZkFourier

namespace ZkFourier
lemma isPrimitiveRoot_rootOfUnity {k : ℕ} [NeZero k] :
    IsPrimitiveRoot (rootOfUnity k) k :=
  Complex.isPrimitiveRoot_exp k (NeZero.ne k)
end ZkFourier

namespace ZkFourier
lemma rootOfUnity_pow_k {k : ℕ} [NeZero k] :
    rootOfUnity k ^ k = 1 :=
  isPrimitiveRoot_rootOfUnity.pow_eq_one
end ZkFourier

namespace ZkFourier
lemma toOmega_mul {k : ℕ} [NeZero k] (j a : ZMod k) :
    toOmega (j * a) = (rootOfUnity k ^ j.val) ^ a.val := by
      unfold toOmega;
      rw [ ← pow_mul, ZMod.val_mul ];
      rw [ ← Nat.mod_add_div ( j.val * a.val ) k, pow_add, pow_mul ] ; norm_num [ rootOfUnity_pow_k ]
end ZkFourier

namespace ZkFourier
lemma geom_sum_toOmega {k : ℕ} [NeZero k] (j : ZMod k) :
    ∑ a : ZMod k, toOmega (j * a) = if j = 0 then (k : ℂ) else 0 := by
      split_ifs with h;
      · simp [h];
      · -- When j ≠ 0, the sum is a geometric series with ratio ω_k^j ≠ 1.
        -- We evaluate it using the identity ∑_{a=0}^{k-1} r^a = (r^k - 1)/(r - 1) = 0,
        -- since r^k = ω_k^{jk} = (ω_k^k)^j = 1^j = 1.
        have h_nontrivial : ∑ a ∈ Finset.range k, (rootOfUnity k ^ j.val) ^ a = 0 := by
          rw [ geom_sum_eq ] <;> norm_num;
          · exact Or.inl ( by rw [ ← pow_mul, Nat.mul_comm, pow_mul, rootOfUnity_pow_k, one_pow, sub_self ] );
          · have h_j_val_ne_zero : j.val ≠ 0 := by
              cases k <;> aesop;
            exact fun h => h_j_val_ne_zero <| Nat.eq_zero_of_dvd_of_lt ( isPrimitiveRoot_rootOfUnity.pow_eq_one_iff_dvd _ |>.1 h ) ( ZMod.val_lt j );
        -- Reindex the sum from Finset.range k to ZMod k via the bijection a ↦ a.val.
        convert h_nontrivial using 1;
        refine' Finset.sum_bij ( fun a _ => a.val ) _ _ _ _ <;> simp +decide [ toOmega_mul ];
        · exact fun a => ZMod.val_lt a;
        · exact fun a₁ a₂ h => by simpa [ ZMod.natCast_zmod_val ] using congr_arg ( fun x : ℕ => x : ℕ → ZMod k ) h;
        · exact fun b hb => ⟨ b, ZMod.val_cast_of_lt hb ⟩
end ZkFourier
