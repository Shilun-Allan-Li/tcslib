/-- Negating a target-group exponent inverts the group element. Technical glue parallel to
`BilinearGroup.pow_val_neg` for the source group.

**Proof sketch.** Apply `pow_val_add_GT` to `-a` and `a`, whose sum is zero. -/
theorem pow_val_neg_GT (gT : B.GT) (a : ZMod B.order) :
    gT ^ (-a).val = (gT ^ a.val)⁻¹ :=
  eq_inv_iff_mul_eq_one.mpr
    ((B.pow_val_add_GT gT (-a) a).symm.trans
      ((congrArg (fun z : ZMod B.order => gT ^ z.val) (neg_add_cancel a)).trans
        ((congrArg (fun n : ℕ => gT ^ n) (ZMod.val_zero (n := B.order))).trans
          (pow_zero gT))))
