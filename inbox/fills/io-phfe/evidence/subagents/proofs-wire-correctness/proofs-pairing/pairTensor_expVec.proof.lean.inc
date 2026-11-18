/-- Tensor pairings expose the product of their scalar coordinates in the target group
[Wee20, §3.1, p. 6].

**Proof sketch.** At each index pair apply `bilinear_pow` and `pow_val_mul_GT`. -/
theorem pairTensor_expVec (g h : B.G) (a : ι → ZMod B.order) (b : κ → ZMod B.order) :
    B.pairTensor (B.expVec g a) (B.expVec h b) =
      B.expVecT (B.pair g h) (fun ij : ι × κ => a ij.1 * b ij.2) :=
  funext fun ij =>
    (B.pairTensor_apply (B.expVec g a) (B.expVec h b) ij).trans
      ((congrArg₂ (fun u v : B.G => B.pair u v) (B.expVec_apply g a ij.1) (B.expVec_apply h b ij.2)).trans
        ((B.bilinear_pow g h (a ij.1).val (b ij.2).val).trans
          ((B.pow_val_mul_GT (B.pair g h) (a ij.1) (b ij.2)).symm.trans
            (B.expVecT_apply (B.pair g h)
              (fun ij : ι × κ => a ij.1 * b ij.2) ij).symm)))
