/-- A target-group scalar dot product is a product of known powers
[Wee20, §4.2, p. 9, (8)].

**Proof sketch.** Combine `pow_val_add_GT` and `pow_val_mul_GT` over the finite index sum. -/
theorem groupDot_expVecT [Fintype ι] (gT : B.GT) (a b : ι → ZMod B.order) :
    groupDot (B.expVecT gT a) b = gT ^ (dotProduct a b).val :=
  let exponentMap : ZMod B.order →+ Additive B.GT :=
    { toFun := fun x => Additive.ofMul (gT ^ x.val)
      map_zero' :=
        (show Additive.ofMul (gT ^ (0 : ZMod B.order).val) = (0 : Additive B.GT) from
          congrArg Additive.ofMul
            ((congrArg (fun n : ℕ => gT ^ n) (ZMod.val_zero (n := B.order))).trans
              (pow_zero gT)))
      map_add' := fun x y =>
        (show Additive.ofMul (gT ^ (x + y).val) =
            Additive.ofMul (gT ^ x.val) + Additive.ofMul (gT ^ y.val) from
          congrArg Additive.ofMul (B.pow_val_add_GT gT x y)) }
  have hSum : gT ^ (dotProduct a b).val = ∏ i, gT ^ (a i * b i).val :=
    (show gT ^ (dotProduct a b).val = (∑ i, exponentMap (a i * b i)).toMul from
      congrArg Additive.toMul (map_sum exponentMap (fun i => a i * b i) Finset.univ)).trans
      (show (∑ i, exponentMap (a i * b i)).toMul = ∏ i, gT ^ (a i * b i).val from
        toMul_sum Finset.univ (fun i => exponentMap (a i * b i)))
  have hCoordinate : ∀ i, (B.expVecT gT a i) ^ (b i).val =
      gT ^ (a i * b i).val :=
    fun i => (congrArg (fun x : B.GT => x ^ (b i).val) (B.expVecT_apply gT a i)).trans
      ((pow_mul gT (a i).val (b i).val).symm.trans (B.pow_val_mul_GT gT (a i) (b i)).symm)
  (groupDot_eq (B.expVecT gT a) b).trans
    ((Finset.prod_congr rfl (fun i _ => hCoordinate i)).trans hSum.symm)
