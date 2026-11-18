/-- A tensor product with its left scalar factor known is computable in the source group
[Wee20, §3.3, p. 8, Game 4].

**Proof sketch.** Apply `pow_val_mul`, `pow_mul` and scalar commutativity coordinatewise. -/
theorem expVec_tensor_right (g : B.G) (a : ι → ZMod B.order) (b : κ → ZMod B.order) :
    (fun ij : ι × κ => B.expVec g b ij.2 ^ (a ij.1).val) =
      B.expVec g (fun ij : ι × κ => a ij.1 * b ij.2) :=
  funext fun ij =>
    (congrArg (fun x : B.G => x ^ (a ij.1).val) (B.expVec_apply g b ij.2)).trans
      ((pow_mul g (b ij.2).val (a ij.1).val).symm.trans
        ((B.pow_val_mul g (b ij.2) (a ij.1)).symm.trans
          ((congrArg (fun z : ZMod B.order => g ^ z.val) (mul_comm (b ij.2) (a ij.1))).trans
            (B.expVec_apply g (fun ij : ι × κ => a ij.1 * b ij.2) ij).symm)))
