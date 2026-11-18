/-- Subtracting the backward draw shift transforms the real garbling exactly
into the simulated garbling at its allowed scalar. [AGW20, Appendix A, (28)–(30),
p.37; IW14, §4.2, p.11], with path sums replacing the determinant argument.

**Proof sketch.** At output coordinates, −(t−z)=z−t. At non-output coordinates,
linearity of vecMul and backward_action give (t−s)B+μe_source=tB. This proves the
pointwise identity with the subtraction sign shown, including empty index types. -/
theorem translation (C : PolyTensor p l n d) (x : Fin l → ZMod (p : ℕ))
    (z : Fin n → ZMod (p : ℕ)) (t : (TIdx l d ⊕ Fin n) → ZMod (p : ℕ)) :
    PartialGarbling.pgbCore (L1 C) (L0 C) x z t =
      PartialGarbling.pgbStarCore (L1 C) (L0 C) (root l d) x
        (dotProduct z (polyTensorEval C x)) (t - shift C x z) := by
  funext row
  cases row with
  | inl j =>
    simp only [PartialGarbling.pgbCore_inl, PartialGarbling.pgbStarCore_inl,
      Pi.sub_apply, shift_inr, neg_sub]
  | inr u =>
    simp only [PartialGarbling.pgbCore_inr, PartialGarbling.pgbStarCore_inr,
      ← matrix_eq C x, Matrix.sub_vecMul, Pi.sub_apply, backward_action,
      sub_add_cancel]
