/-- Every public-degree-d, private-degree-two polynomial is represented by the
PHFE class after appending 1 to the private input. [GJLS21, §9, p.58]. This spells
out the constant/linear-term padding bridge for the tuple representation.

**Proof sketch.** Expand the polynomial as the finite sum of its monomials. For
each monomial, list its public variables with multiplicity, pad to d slots with
the public constant, list its private variables with multiplicity, and pad to
two slots with the private constant. Assign its coefficient to one such ordered
tuple pair. Reindex the finite coefficient sum; padding contributes only 1. -/
theorem pad_one {p : ℕ+} {l n d : ℕ}
    (P : MvPolynomial (Fin l ⊕ Fin n) (ZMod (p : ℕ)))
    (hdeg : BidegreeAtMost d 2 P) :
    ∃ C : PolyTensor p l ((n + 1) * (n + 1)) d,
      ∀ (x : Fin l → ZMod (p : ℕ)) (y : Fin n → ZMod (p : ℕ)),
        MvPolynomial.eval (Sum.elim x y) P = phfeEval C x (Fin.snoc y 1) := by
  obtain ⟨C, hC⟩ := PolynomialTensorAlgebra.exists_quadratic_expansion
    (R := ZMod (p : ℕ)) l n d P ((bidegreeAtMost_iff d 2 P).1 hdeg)
  refine ⟨fun j tau => C (finProdFinEquiv.symm j) tau, fun x y => ?_⟩
  rw [phfeEval_sum]
  simpa only [Fintype.sum_prod_type, polyTensorEval_eq, Equiv.symm_apply_apply,
    xhat_eq, Finset.sum_mul] using hC x y
