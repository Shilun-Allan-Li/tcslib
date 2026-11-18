/-- An implicit scalar dot product is a product of known powers of source-group elements
[Wee20, §2.1, p. 4; §4.2, p. 9, (8)].

**Proof sketch.** Induct over the finite index sum, using `pow_val_add`, `pow_val_mul` and
`Finset.prod_pow_eq_pow_sum` to combine the powers. -/
theorem groupDot_expVec [Fintype ι] (g : B.G) (a b : ι → ZMod B.order) :
    groupDot (B.expVec g a) b = g ^ (dotProduct a b).val :=
  let exponentMap : ZMod B.order →+ Additive B.G :=
    { toFun := fun x => Additive.ofMul (g ^ x.val)
      map_zero' :=
        (show Additive.ofMul (g ^ (0 : ZMod B.order).val) = (0 : Additive B.G) from
          congrArg Additive.ofMul
            ((congrArg (fun n : ℕ => g ^ n) (ZMod.val_zero (n := B.order))).trans
              (pow_zero g)))
      map_add' := fun x y =>
        (show Additive.ofMul (g ^ (x + y).val) =
            Additive.ofMul (g ^ x.val) + Additive.ofMul (g ^ y.val) from
          congrArg Additive.ofMul (B.pow_val_add g x y)) }
  have hSum : g ^ (dotProduct a b).val = ∏ i, g ^ (a i * b i).val :=
    (show g ^ (dotProduct a b).val = (∑ i, exponentMap (a i * b i)).toMul from
      congrArg Additive.toMul (map_sum exponentMap (fun i => a i * b i) Finset.univ)).trans
      (show (∑ i, exponentMap (a i * b i)).toMul = ∏ i, g ^ (a i * b i).val from
        toMul_sum Finset.univ (fun i => exponentMap (a i * b i)))
  have hCoordinate : ∀ i, (B.expVec g a i) ^ (b i).val =
      g ^ (a i * b i).val :=
    fun i => (congrArg (fun x : B.G => x ^ (b i).val) (B.expVec_apply g a i)).trans
      ((pow_mul g (a i).val (b i).val).symm.trans (B.pow_val_mul g (a i) (b i)).symm)
  (groupDot_eq (B.expVec g a) b).trans
    ((Finset.prod_congr rfl (fun i _ => hCoordinate i)).trans hSum.symm)
