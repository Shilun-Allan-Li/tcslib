/-- Every real garbling reconstructs z·f(x), independently of its draw.
[AGW20, Lemma 2, p.12; Appendix A, p.38], proved by path sums.

**Proof sketch.** Split the garbling/reconstruction dot product into its output
and non-output blocks. Move the latter matrix action onto forward values using
the published dot-product/mulVec identity, then apply forward_action. The masked
output contribution cancels the draw contribution, leaving z·f(x). -/
theorem rec_spec (C : PolyTensor p l n d) (x : Fin l → ZMod (p : ℕ))
    (z : Fin n → ZMod (p : ℕ)) (t : (TIdx l d ⊕ Fin n) → ZMod (p : ℕ)) :
    dotProduct (PartialGarbling.pgbCore (L1 C) (L0 C) x z t) (rec C x) =
      dotProduct z (polyTensorEval C x) := by
  -- Read the reconstruction blocks without unfolding their definition.
  have hrec : rec C x = Sum.elim (polyTensorEval C x) (forward x) :=
    (Sum.elim_comp_inl_inr (rec C x)).symm.trans
      (congrArg₂ Sum.elim (funext (rec_inl C x)) (funext (rec_inr C x)))
  -- The adversary draw paired with the output-only vector is its output block.
  have ht := sumElim_dotProduct_sumElim
    (u := t ∘ Sum.inl) (x := t ∘ Sum.inr)
    (v := fun _ : TIdx l d => 0) (y := polyTensorEval C x)
  simp only [Sum.elim_comp_inl_inr, dotProduct_zero', zero_add] at ht
  rw [PartialGarbling.pgbCore_eq, hrec, sumElim_dotProduct_sumElim,
    ← matrix_eq C x, ← Matrix.dotProduct_mulVec, forward_action, ht]
  -- Forward reconstruction leaves equal and opposite mask terms.
  change dotProduct (z - t ∘ Sum.inr) (polyTensorEval C x) +
    dotProduct (t ∘ Sum.inr) (polyTensorEval C x) = dotProduct z (polyTensorEval C x)
  rw [sub_dotProduct, sub_add_cancel]
