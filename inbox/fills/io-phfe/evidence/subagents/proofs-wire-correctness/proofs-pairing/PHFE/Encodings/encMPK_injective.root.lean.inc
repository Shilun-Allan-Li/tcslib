theorem encMPK_injective (G : BilinearGen) (ℓ n : PolyExpr) (κ : ℕ)
    (pp : PublicParams G κ) : Function.Injective (encMPK G ℓ n κ pp)  := by
  intro a b h
  have hw := congrArg List.ofFn h
  simp only [encMPK_eq] at hw
  rw [ofFn_padFin_of_length (quadraticMPK_length G ℓ n κ pp a),
    ofFn_padFin_of_length (quadraticMPK_length G ℓ n κ pp b)] at hw
  simp only [Wire.quadraticMPK_eq, Wire.linearMPK_eq] at hw
  let aTail0 := pairEncode
    (Wire.groupMatrix pp (fun i j => a.linear.AU i (finProdFinEquiv.symm j)))
    (Wire.groupMatrix pp a.linear.AV)
  let aTail1 := pairEncode (Wire.groupMatrix pp a.linear.AW) aTail0
  let aTail2 := pairEncode (Wire.groupMatrix pp a.linear.A) aTail1
  let aTail3 := pairEncode (Wire.groupMatrix pp a.A2) aTail2
  let bTail0 := pairEncode
    (Wire.groupMatrix pp (fun i j => b.linear.AU i (finProdFinEquiv.symm j)))
    (Wire.groupMatrix pp b.linear.AV)
  let bTail1 := pairEncode (Wire.groupMatrix pp b.linear.AW) bTail0
  let bTail2 := pairEncode (Wire.groupMatrix pp b.linear.A) bTail1
  let bTail3 := pairEncode (Wire.groupMatrix pp b.A2) bTail2
  change pairEncode (Wire.groupMatrix pp a.A1) aTail3 =
    pairEncode (Wire.groupMatrix pp b.A1) bTail3 at hw
  obtain ⟨h1, ht⟩ := Prod.mk.inj
    (@pairEncode_injective (Wire.groupMatrix pp a.A1, aTail3)
      (Wire.groupMatrix pp b.A1, bTail3) hw)
  obtain ⟨h2, hl⟩ := Prod.mk.inj
    (@pairEncode_injective (Wire.groupMatrix pp a.A2, aTail2)
      (Wire.groupMatrix pp b.A2, bTail2) ht)
  obtain ⟨hA, hl⟩ := Prod.mk.inj
    (@pairEncode_injective (Wire.groupMatrix pp a.linear.A, aTail1)
      (Wire.groupMatrix pp b.linear.A, bTail1) hl)
  obtain ⟨hW, hl⟩ := Prod.mk.inj
    (@pairEncode_injective (Wire.groupMatrix pp a.linear.AW, aTail0)
      (Wire.groupMatrix pp b.linear.AW, bTail0) hl)
  obtain ⟨hU, hV⟩ := Prod.mk.inj
    (@pairEncode_injective
      (Wire.groupMatrix pp (fun i j => a.linear.AU i (finProdFinEquiv.symm j)),
        Wire.groupMatrix pp a.linear.AV)
      (Wire.groupMatrix pp (fun i j => b.linear.AU i (finProdFinEquiv.symm j)),
        Wire.groupMatrix pp b.linear.AV) hl)
  have hu : a.linear.AU = b.linear.AU := ?_
  swap
  · funext i j
    have hh := congrFun (congrFun (Wire.groupMatrix_injective pp hU) i)
      (finProdFinEquiv j)
    simpa only [Equiv.symm_apply_apply] using hh
  have h1' := Wire.groupMatrix_injective pp h1
  have h2' := Wire.groupMatrix_injective pp h2
  have hA' := Wire.groupMatrix_injective pp hA
  have hW' := Wire.groupMatrix_injective pp hW
  have hV' := Wire.groupMatrix_injective pp hV
  rcases a with ⟨a1, a2, ⟨aA, aW, aU, aV⟩⟩
  rcases b with ⟨b1, b2, ⟨bA, bW, bU, bV⟩⟩
  cases h1'
  cases h2'
  cases hA'
  cases hW'
  cases hu
  cases hV'
  rfl
