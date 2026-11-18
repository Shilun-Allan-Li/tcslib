/-- Scalar multiplication acts on the implicit vector by known powers
[Wee20, §2.1, p. 4].

**Proof sketch.** Use `pow_val_mul` and `pow_mul` at every coordinate. -/
theorem expVec_smul (g : B.G) (c : ZMod B.order) (a : ι → ZMod B.order) :
    B.expVec g (c • a) = fun i => (B.expVec g a i) ^ c.val :=
  funext fun i =>
    (show B.expVec g (c • a) i = g ^ (c * a i).val from
      B.expVec_apply g (c • a) i).trans
      ((B.pow_val_mul g c (a i)).trans
        ((congrArg (fun n : ℕ => g ^ n) (Nat.mul_comm c.val (a i).val)).trans
          ((pow_mul g (a i).val c.val).trans
            (congrArg (fun x : B.G => x ^ c.val) (B.expVec_apply g a i).symm))))
