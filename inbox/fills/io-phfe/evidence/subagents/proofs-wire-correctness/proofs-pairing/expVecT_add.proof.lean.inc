/-- Adding scalar vectors multiplies their target-group representations
[Wee20, §2.1, p. 4].

**Proof sketch.** Apply `pow_val_add_GT` at every coordinate. -/
theorem expVecT_add (gT : B.GT) (a b : ι → ZMod B.order) :
    B.expVecT gT (a + b) = B.expVecT gT a * B.expVecT gT b :=
  funext fun i =>
    (B.expVecT_apply gT (a + b) i).trans
      ((B.pow_val_add_GT gT (a i) (b i)).trans
        (congrArg₂ (fun x y : B.GT => x * y)
          (B.expVecT_apply gT a i).symm (B.expVecT_apply gT b i).symm))
