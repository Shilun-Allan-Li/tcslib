theorem exists_padded_tuple {R : Type*} [CommMonoid R] (m d : ℕ) (e : Fin m → ℕ)
    (he : ∑ i : Fin m, e i ≤ d) :
    ∃ tau : Fin d → Fin (m + 1), ∀ x : Fin m → R,
      (∏ j : Fin d, Fin.snoc (α := fun _ => R) x 1 (tau j)) =
        ∏ i : Fin m, x i ^ e i := by
  let labels : List (Fin (m + 1)) :=
    (List.ofFn (fun i : Fin m => List.replicate (e i) i.castSucc)).flatten
  have hlength : labels.length = ∑ i : Fin m, e i := by
    simp only [labels, List.length_flatten, ← List.ofFn_comp',
      List.length_replicate, List.sum_ofFn]
  let padded := labels ++ List.replicate (d - labels.length) (Fin.last m)
  have hpadded : padded.length = d := by
    simp only [padded, List.length_append, List.length_replicate]
    exact Nat.add_sub_of_le (hlength.le.trans he)
  rw [← hpadded]
  refine ⟨padded.get, fun x => ?_⟩
  rw [← Fin.prod_ofFn, List.ofFn_comp', List.ofFn_get]
  change ((labels ++ List.replicate (d - labels.length) (Fin.last m)).map
    (Fin.snoc (α := fun _ => R) x 1)).prod = _
  rw [List.map_append, List.prod_append, List.map_replicate, Fin.snoc_last,
    List.prod_replicate, one_pow, mul_one]
  simp only [labels, List.map_flatten, List.prod_flatten,
    ← List.ofFn_comp', List.map_replicate, Fin.snoc_castSucc,
    List.prod_replicate, List.prod_ofFn]
