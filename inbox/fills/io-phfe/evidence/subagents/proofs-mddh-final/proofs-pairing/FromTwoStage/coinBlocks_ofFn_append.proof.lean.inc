/-- Concatenating the original machine coin words recovers both typed tapes.

**Proof sketch.** Use the two published coin-block readers. Each first-block index
lies in the first ofFn word; each shifted second-block index lies after that word.
The published append/getD/ofFn laws return the original coordinates. -/
theorem coinBlocks_ofFn_append (A : TwoStage) (kappa : ℕ)
    (r1 : A.first.Coins kappa) (r2 : A.second.Coins kappa) :
    (A.firstCoins kappa (List.ofFn r1 ++ List.ofFn r2),
      A.secondCoins kappa (List.ofFn r1 ++ List.ofFn r2)) = (r1, r2) := by
  have h1 : (List.ofFn r1).length = A.first.coinLen kappa := List.length_ofFn
  have h2 : (List.ofFn r2).length = A.second.coinLen kappa := List.length_ofFn
  apply Prod.ext
  · change A.firstCoins kappa (List.ofFn r1 ++ List.ofFn r2) = r1
    rw [firstCoins_eq]
    funext i
    change (List.ofFn r1 ++ List.ofFn r2).getD i.val false = r1 i
    have hi := lt_of_lt_of_eq i.isLt h1.symm
    rw [List.getD_append _ _ _ _ hi, List.getD_eq_getElem _ _ hi,
      List.getElem_ofFn]
  · change A.secondCoins kappa (List.ofFn r1 ++ List.ofFn r2) = r2
    rw [secondCoins_eq]
    funext i
    change (List.ofFn r1 ++ List.ofFn r2).getD (A.first.coinLen kappa + i.val) false = r2 i
    have hi := lt_of_lt_of_eq i.isLt h2.symm
    rw [List.getD_append_right _ _ _ _
      (le_trans (le_of_eq h1) (Nat.le_add_right _ _)), h1,
      Nat.add_sub_cancel_left, List.getD_eq_getElem _ _ hi, List.getElem_ofFn]
