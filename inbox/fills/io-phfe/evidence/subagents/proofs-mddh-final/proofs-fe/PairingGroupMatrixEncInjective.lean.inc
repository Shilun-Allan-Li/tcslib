/-- Group-matrix serialization is injective, including empty dimensions. Serialization glue.

**Proof sketch.** Split equal concatenations into fixed-width rows and then point blocks,
using their known lengths. Apply `List.ofFn_injective` and `B.encG_injective` entrywise. -/
theorem groupMatrixEnc_injective :
    Function.Injective (B.groupMatrixEnc (rows := rows) (cols := cols)) := by
  intro M N h
  have hRows :
      List.ofFn (fun i => (List.ofFn fun j => List.ofFn (B.encG (M i j))).flatten) =
        List.ofFn (fun i => (List.ofFn fun j => List.ofFn (B.encG (N i j))).flatten) := ?_
  swap
  · apply List.eq_iff_flatten_eq.mpr
    refine ⟨?_, ?_⟩
    · simpa only [groupMatrixEnc_eq] using h
    · rw [List.map_ofFn, List.map_ofFn]
      apply congrArg List.ofFn
      funext i
      change (List.ofFn (fun j => List.ofFn (B.encG (M i j)))).flatten.length =
        (List.ofFn (fun j => List.ofFn (B.encG (N i j)))).flatten.length
      rw [List.length_flatten, List.length_flatten, List.map_ofFn, List.map_ofFn]
      apply congrArg List.sum
      apply congrArg List.ofFn
      funext j
      change (List.ofFn (B.encG (M i j))).length = (List.ofFn (B.encG (N i j))).length
      rw [List.length_ofFn, List.length_ofFn]
  have hRow := List.ofFn_injective hRows
  funext i j
  have hBlocks :
      List.ofFn (fun k => List.ofFn (B.encG (M i k))) =
        List.ofFn (fun k => List.ofFn (B.encG (N i k))) := ?_
  swap
  · apply List.eq_iff_flatten_eq.mpr
    refine ⟨congrFun hRow i, ?_⟩
    rw [List.map_ofFn, List.map_ofFn]
    apply congrArg List.ofFn
    funext k
    change (List.ofFn (B.encG (M i k))).length = (List.ofFn (B.encG (N i k))).length
    rw [List.length_ofFn, List.length_ofFn]
  exact B.encG_injective
    (List.ofFn_injective (congrFun (List.ofFn_injective hBlocks) j))
