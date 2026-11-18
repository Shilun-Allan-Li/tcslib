/-- Function-key encoding is injective, including across different original function words.

**Proof sketch.** Equal padded words first have equal fixed-length original function blocks.
That fixes their coordinate dimensions, hence their unpadded lengths. Recover the complete
key words and use pair and element-encoding injectivity in each block. -/
theorem encSK_injective (G : BilinearGen) {ℓ n : PolyExpr} {d : ℕ}
    (PG : PartialGarbling.Raw ℓ (n.mul n) (TensorFn ℓ n d)) (κ : ℕ)
    (pp : PublicParams G κ) : Function.Injective (encSK G PG κ pp) := by
  let L := (skLen G PG).eval κ
  have hPadded : ∀ k : Key G PG κ pp,
      List.ofFn (encSK G PG κ pp k) = keyWord G PG κ pp k ++
        List.replicate (L - (keyWord G PG κ pp k).length) false := ?_
  swap
  · intro k
    rw [encSK_eq, ofFn_padFin_eq_take, List.take_append,
      List.take_of_length_le (keyWord_length_le G PG κ pp k), List.take_replicate,
      Nat.min_eq_left (Nat.sub_le L _)]
  intro a b h
  have hw := congrArg List.ofFn h
  rw [hPadded a, hPadded b] at hw
  let aTail := Wire.quadraticKey pp PG a.quadratic ++
    List.replicate (L - (keyWord G PG κ pp a).length) false
  let bTail := Wire.quadraticKey pp PG b.quadratic ++
    List.replicate (L - (keyWord G PG κ pp b).length) false
  have hPair : pairEncode (List.ofFn a.function) aTail =
      pairEncode (List.ofFn b.function) bTail := ?_
  swap
  · simpa only [aTail, bTail, keyWord_eq, GGMRed.pairEncode_append_right] using hw
  have hPrefix := @pairEncode_injective
    (List.ofFn a.function, aTail) (List.ofFn b.function, bTail) hPair
  have hf := List.ofFn_injective (congrArg Prod.fst hPrefix)
  rcases a with ⟨fa, ka⟩
  rcases b with ⟨fb, kb⟩
  change fa = fb at hf
  cases hf
  have hLen : (keyWord G PG κ pp ⟨fa, ka⟩).length =
      (keyWord G PG κ pp ⟨fa, kb⟩).length := ?_
  swap
  · simp only [keyWord_eq, Wire.quadraticKey_eq, Wire.linearKey_eq,
      length_pairEncode, List.length_ofFn, Wire.groupMatrix_length]
  rw [← hLen] at hw
  have hWord := List.append_cancel_right hw
  simp only [keyWord_eq] at hWord
  have hQ := congrArg Prod.snd
    (@pairEncode_injective
      (List.ofFn fa, Wire.quadraticKey pp PG ka)
      (List.ofFn fa, Wire.quadraticKey pp PG kb) hWord)
  let aLin := Wire.linearKey pp PG ka.linear
  let bLin := Wire.linearKey pp PG kb.linear
  simp only [Wire.quadraticKey_eq] at hQ
  change pairEncode (Wire.groupMatrix pp ka.matrix) aLin =
    pairEncode (Wire.groupMatrix pp kb.matrix) bLin at hQ
  obtain ⟨hM, hLin⟩ := Prod.mk.inj
    (@pairEncode_injective (Wire.groupMatrix pp ka.matrix, aLin)
      (Wire.groupMatrix pp kb.matrix, bLin) hQ)
  let f := decodeFunction G ℓ n d κ pp fa
  let coord := PG.mCoord κ pp.orderParam f
  let a2 : Matrix (Fin 3) (Fin (ℓ.eval κ * PG.mCount κ pp.orderParam f)) pp.group.G :=
    fun i j => let u := finProdFinEquiv.symm j
      ka.linear.K2 i (u.1, coord.symm u.2)
  let b2 : Matrix (Fin 3) (Fin (ℓ.eval κ * PG.mCount κ pp.orderParam f)) pp.group.G :=
    fun i j => let u := finProdFinEquiv.symm j
      kb.linear.K2 i (u.1, coord.symm u.2)
  let a3 : Matrix (Fin 3) (Fin (PG.mCount κ pp.orderParam f)) pp.group.G :=
    fun i j => ka.linear.K3 i (coord.symm j)
  let b3 : Matrix (Fin 3) (Fin (PG.mCount κ pp.orderParam f)) pp.group.G :=
    fun i j => kb.linear.K3 i (coord.symm j)
  let ar : Matrix (Fin 2) (Fin (PG.mCount κ pp.orderParam f)) pp.group.G :=
    fun i j => ka.linear.R i (coord.symm j)
  let br : Matrix (Fin 2) (Fin (PG.mCount κ pp.orderParam f)) pp.group.G :=
    fun i j => kb.linear.R i (coord.symm j)
  let aTail0 := pairEncode (Wire.groupMatrix pp a3) (Wire.groupMatrix pp ar)
  let bTail0 := pairEncode (Wire.groupMatrix pp b3) (Wire.groupMatrix pp br)
  let aTail1 := pairEncode (Wire.groupMatrix pp a2) aTail0
  let bTail1 := pairEncode (Wire.groupMatrix pp b2) bTail0
  change Wire.linearKey pp PG ka.linear = Wire.linearKey pp PG kb.linear at hLin
  simp only [Wire.linearKey_eq] at hLin
  change pairEncode (Wire.groupMatrix pp ka.linear.K1) aTail1 =
    pairEncode (Wire.groupMatrix pp kb.linear.K1) bTail1 at hLin
  obtain ⟨h1, hTail1⟩ := Prod.mk.inj
    (@pairEncode_injective (Wire.groupMatrix pp ka.linear.K1, aTail1)
      (Wire.groupMatrix pp kb.linear.K1, bTail1) hLin)
  obtain ⟨h2, hTail0⟩ := Prod.mk.inj
    (@pairEncode_injective (Wire.groupMatrix pp a2, aTail0)
      (Wire.groupMatrix pp b2, bTail0) hTail1)
  obtain ⟨h3, hr⟩ := Prod.mk.inj
    (@pairEncode_injective (Wire.groupMatrix pp a3, Wire.groupMatrix pp ar)
      (Wire.groupMatrix pp b3, Wire.groupMatrix pp br) hTail0)
  have hM' := Wire.groupMatrix_injective pp hM
  have h1' := Wire.groupMatrix_injective pp h1
  have h2flat : a2 = b2 := Wire.groupMatrix_injective pp h2
  have h3flat : a3 = b3 := Wire.groupMatrix_injective pp h3
  have hrflat : ar = br := Wire.groupMatrix_injective pp hr
  have h2' : ka.linear.K2 = kb.linear.K2 := ?_
  swap
  · funext i j
    have hh := congrFun (congrFun h2flat i) (finProdFinEquiv (j.1, coord j.2))
    simpa only [a2, b2, Equiv.symm_apply_apply] using hh
  have h3' : ka.linear.K3 = kb.linear.K3 := ?_
  swap
  · funext i j
    have hh := congrFun (congrFun h3flat i) (coord j)
    simpa only [a3, b3, Equiv.symm_apply_apply] using hh
  have hr' : ka.linear.R = kb.linear.R := ?_
  swap
  · funext i j
    have hh := congrFun (congrFun hrflat i) (coord j)
    simpa only [ar, br, Equiv.symm_apply_apply] using hh
  rcases ka with ⟨aM, ⟨aK1, aK2, aK3, aR⟩⟩
  rcases kb with ⟨bM, ⟨bK1, bK2, bK3, bR⟩⟩
  cases hM'
  cases h1'
  cases h2'
  cases h3'
  cases hr'
  rfl
