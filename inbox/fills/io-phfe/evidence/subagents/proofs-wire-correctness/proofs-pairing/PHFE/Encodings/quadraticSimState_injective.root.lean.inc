/-- The complete private simulator-state word is injective on all typed states.

**Proof sketch.** Separate the fixed number of nested blocks. Read the public group matrix
and all scalar matrices/vectors with their public encoding injectivity theorems. The scalar
modulus fits the source-group width by the existing order-width theorem. -/
theorem quadraticSimState_injective (G : BilinearGen) (ℓ n : PolyExpr) (κ : ℕ)
    (pp : PublicParams G κ) :
    Function.Injective (Wire.quadraticSimState pp (ℓ := ℓ) (n1 := n) (n2 := n)) := by
  intro a b h
  simp only [Wire.quadraticSimState_eq, Wire.linearSimState_eq,
    List.foldr_cons, List.foldr_nil, pairEncode_eq_iff, eq_self_iff_true,
    and_true] at h
  rcases h with ⟨hM, ⟨hA, hW, hU, hV, hc, hw, hv, hInv⟩, hy1, hy2⟩
  have hwidth : pp.group.order ≤ 2 ^ G.wG.eval κ := ?_
  swap
  · simpa only [PublicParams.group_eq] using
      (IdentityBased.BB1Machine.order_le_two_pow G κ pp.description.val)
  have hM' := Wire.groupMatrix_injective pp hM
  simp only [Wire.scalarMatrix_eq, Wire.scalarVector_eq] at hA hW hU hV hc hw hv hInv hy1 hy2
  have hA' := Encoding.Modular.encodeMatrix_injective (q := pp.group.order)
    (G.wG.eval κ) hwidth hA
  have hW' := Encoding.Modular.encodeMatrix_injective (q := pp.group.order)
    (G.wG.eval κ) hwidth hW
  have hUflat :
      (fun (i : Fin 3) (j : Fin (ℓ.eval κ * 2)) =>
        a.linear.U i (finProdFinEquiv.symm j)) =
      (fun (i : Fin 3) (j : Fin (ℓ.eval κ * 2)) =>
        b.linear.U i (finProdFinEquiv.symm j)) :=
    Encoding.Modular.encodeMatrix_injective (q := pp.group.order)
      (G.wG.eval κ) hwidth hU
  have hU' : a.linear.U = b.linear.U := ?_
  swap
  · funext i j
    simpa only [Equiv.symm_apply_apply] using
      (congrFun (congrFun hUflat i) (finProdFinEquiv j))
  have hV' := Encoding.Modular.encodeMatrix_injective (q := pp.group.order)
    (G.wG.eval κ) hwidth hV
  have hc' := Encoding.Modular.encodeVector_injective (q := pp.group.order)
    (G.wG.eval κ) hwidth hc
  have hw' := Encoding.Modular.encodeVector_injective (q := pp.group.order)
    (G.wG.eval κ) hwidth hw
  have hv' := Encoding.Modular.encodeVector_injective (q := pp.group.order)
    (G.wG.eval κ) hwidth hv
  have hInv' := Encoding.Modular.encodeMatrix_injective (q := pp.group.order)
    (G.wG.eval κ) hwidth hInv
  have hy1' := Encoding.Modular.encodeVector_injective (q := pp.group.order)
    (G.wG.eval κ) hwidth hy1
  have hy2' := Encoding.Modular.encodeVector_injective (q := pp.group.order)
    (G.wG.eval κ) hwidth hy2
  rcases a with ⟨aM, ⟨aA, aW, aU, aV, ac, aw, av, aInv⟩, ay1, ay2⟩
  rcases b with ⟨bM, ⟨bA, bW, bU, bV, bc, bw, bv, bInv⟩, by1, by2⟩
  cases hM'
  cases hA'
  cases hW'
  cases hU'
  cases hV'
  cases hc'
  cases hw'
  cases hv'
  cases hInv'
  cases hy1'
  cases hy2'
  rfl
