/-- A known scalar multiplies target-group exponents through known powers
[Wee20, §2.1, p. 4].

**Proof sketch.** Use `pow_val_mul_GT` and `pow_mul` coordinatewise. -/
theorem expVecT_smul (gT : B.GT) (c : ZMod B.order) (a : ι → ZMod B.order) :
    B.expVecT gT (c • a) = fun i => (B.expVecT gT a i) ^ c.val :=
  funext fun i =>
    (show B.expVecT gT (c • a) i = gT ^ (c * a i).val from
      B.expVecT_apply gT (c • a) i).trans
      ((B.pow_val_mul_GT gT c (a i)).trans
        ((congrArg (fun n : ℕ => gT ^ n) (Nat.mul_comm c.val (a i).val)).trans
          ((pow_mul gT (a i).val c.val).trans
            (congrArg (fun x : B.GT => x ^ c.val) (B.expVecT_apply gT a i).symm))))
