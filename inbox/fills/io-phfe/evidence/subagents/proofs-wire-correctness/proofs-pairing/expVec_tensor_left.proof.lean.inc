/-- A tensor product with its right scalar factor known is computable in the source group
[Wee20, §3.3, p. 8, Game 3].

**Proof sketch.** Apply `pow_val_mul` and `pow_mul` at every index pair. -/
theorem expVec_tensor_left (g : B.G) (a : ι → ZMod B.order) (b : κ → ZMod B.order) :
    (fun ij : ι × κ => B.expVec g a ij.1 ^ (b ij.2).val) =
      B.expVec g (fun ij : ι × κ => a ij.1 * b ij.2) :=
  funext fun ij =>
    (congrArg (fun x : B.G => x ^ (b ij.2).val) (B.expVec_apply g a ij.1)).trans
      ((pow_mul g (a ij.1).val (b ij.2).val).symm.trans
        ((B.pow_val_mul g (a ij.1) (b ij.2)).symm.trans
          (B.expVec_apply g (fun ij : ι × κ => a ij.1 * b ij.2) ij).symm))
