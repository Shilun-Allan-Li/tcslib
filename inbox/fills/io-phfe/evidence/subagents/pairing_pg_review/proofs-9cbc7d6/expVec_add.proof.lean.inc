/-- Adding scalar vectors multiplies their implicit source-group vectors
[Wee20, §2.1, p. 4].

**Proof sketch.** Apply the published source-group additive exponent law coordinatewise. -/
theorem expVec_add (g : B.G) (a b : ι → ZMod B.order) :
    B.expVec g (a + b) = B.expVec g a * B.expVec g b :=
  funext fun i =>
    (B.expVec_apply g (a + b) i).trans
      ((B.pow_val_add g (a i) (b i)).trans
        (congrArg₂ (fun x y : B.G => x * y)
          (B.expVec_apply g a i).symm (B.expVec_apply g b i).symm))
