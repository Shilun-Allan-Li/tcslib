/-- Target-group exponents add modulo the group order. Technical glue parallel to
`BilinearGroup.pow_val_add` for the source group; no target-group version is in that API.

**Proof sketch.** Use `ZMod.val_add`, `pow_add`, `pow_mod_card` and `B.card_GT`. -/
theorem pow_val_add_GT (gT : B.GT) (a b : ZMod B.order) :
    gT ^ (a + b).val = gT ^ a.val * gT ^ b.val :=
  (congrArg (fun n : ℕ => gT ^ n) (ZMod.val_add a b)).trans
    ((congrArg (fun n : ℕ => gT ^ ((a.val + b.val) % n)) B.card_GT).symm.trans
      ((pow_mod_card gT (a.val + b.val)).trans (pow_add gT a.val b.val)))
