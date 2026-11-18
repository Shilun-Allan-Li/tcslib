/-- Negating a scalar vector inverts its implicit source-group vector
[Wee20, §2.1, p. 4].

**Proof sketch.** Apply the published source-group negation law coordinatewise. -/
theorem expVec_neg (g : B.G) (a : ι → ZMod B.order) :
    B.expVec g (-a) = (B.expVec g a)⁻¹ :=
  funext fun i =>
    (B.expVec_apply g (-a) i).trans
      ((B.pow_val_neg g (a i)).trans
        (congrArg (fun x : B.G => x⁻¹) (B.expVec_apply g a i).symm))
