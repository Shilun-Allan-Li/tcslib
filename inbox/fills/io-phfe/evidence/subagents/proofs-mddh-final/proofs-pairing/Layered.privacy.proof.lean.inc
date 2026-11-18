/-- Real and simulated layered garblings have identical laws, with no error term.
[IW14, Definition 1, p.6; AGW20, Appendix A, (28)–(30), p.37].

**Proof sketch.** Apply the pointwise translation, then reindex the uniform draw
by Equiv.addRight (−shift C x z), using ProbComp.expect_sample_equiv. No rank,
nonzero-value or positive-dimension event is needed. -/
theorem privacy (C : PolyTensor p l n d) (x : Fin l → ZMod (p : ℕ))
    (z : Fin n → ZMod (p : ℕ)) (test : ((Fin n ⊕ MIdx l d) → ZMod (p : ℕ)) → ℝ) :
    ProbComp.expect (ProbComp.sample ((TIdx l d ⊕ Fin n) → ZMod (p : ℕ)))
        (fun t => test (PartialGarbling.pgbCore (L1 C) (L0 C) x z t)) =
      ProbComp.expect (ProbComp.sample ((TIdx l d ⊕ Fin n) → ZMod (p : ℕ)))
        (fun t => test (PartialGarbling.pgbStarCore (L1 C) (L0 C) (root l d)
          x (dotProduct z (polyTensorEval C x)) t)) := by
  simp only [translation C x z]
  simpa only [Equiv.coe_addRight, sub_eq_add_neg] using
    (ProbComp.expect_sample_equiv (Equiv.addRight (-shift C x z))
      (fun t => test (PartialGarbling.pgbStarCore (L1 C) (L0 C) (root l d)
        x (dotProduct z (polyTensorEval C x)) t)))
