/-- Negating scalar coordinates inverts the target-group representation
[Wee20, §2.1, p. 4].

**Proof sketch.** Apply `pow_val_neg_GT` at every coordinate. -/
theorem expVecT_neg (gT : B.GT) (a : ι → ZMod B.order) :
    B.expVecT gT (-a) = (B.expVecT gT a)⁻¹ :=
  funext fun i =>
    (B.expVecT_apply gT (-a) i).trans
      ((B.pow_val_neg_GT gT (a i)).trans
        (congrArg (fun x : B.GT => x⁻¹) (B.expVecT_apply gT a i).symm))
