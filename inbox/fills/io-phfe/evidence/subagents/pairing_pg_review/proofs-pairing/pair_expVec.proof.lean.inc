/-- Pairing corresponding implicit coordinates evaluates their scalar dot product
[Wee20, §2.1, p. 4; §4.2, p. 9, (6)–(8)].

**Proof sketch.** Apply `bilinear_pow` coordinatewise, reduce products of exponents with
`pow_val_mul_GT`, and combine powers with `pow_val_add_GT`. -/
theorem pair_expVec [Fintype ι] (g h : B.G) (a b : ι → ZMod B.order) :
    B.pairVec (B.expVec g a) (B.expVec h b) = B.pair g h ^ (dotProduct a b).val :=
  (B.pairVec_eq (B.expVec g a) (B.expVec h b)).trans
    ((Finset.prod_congr rfl (fun i _ =>
      (congrArg₂ B.pair (B.expVec_apply g a i) (B.expVec_apply h b i)).trans
        ((B.bilinear_pow g h (a i).val (b i).val).trans
          ((pow_mul (B.pair g h) (a i).val (b i).val).trans
            (congrArg (fun x : B.GT => x ^ (b i).val)
              (B.expVecT_apply (B.pair g h) a i).symm))))).trans
      ((groupDot_eq (B.expVecT (B.pair g h) a) b).symm.trans
        (B.groupDot_expVecT (B.pair g h) a b)))
