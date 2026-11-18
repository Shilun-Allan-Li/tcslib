/-- A source-group matrix has one fixed-width block per entry. Serialization glue.

**Proof sketch.** Apply `List.length_flatten` and `List.length_ofFn` to both concatenations;
every point block has length `wG`. -/
theorem length_groupMatrixEnc (M : Matrix (Fin rows) (Fin cols) B.G) :
    (B.groupMatrixEnc M).length = rows * cols * wG := by
  have hrow (i : Fin rows) :
      (List.ofFn (fun j : Fin cols => List.ofFn (B.encG (M i j)))).flatten.length =
        cols * wG := by
    rw [List.length_flatten, List.map_ofFn]
    change (List.ofFn (fun j : Fin cols => (List.ofFn (B.encG (M i j))).length)).sum = _
    simp only [List.length_ofFn, List.ofFn_const, List.sum_replicate_nat]
  rw [groupMatrixEnc_eq, List.length_flatten, List.map_ofFn]
  change (List.ofFn (fun i : Fin rows =>
    (List.ofFn (fun j : Fin cols => List.ofFn (B.encG (M i j)))).flatten.length)).sum = _
  simp only [hrow, List.ofFn_const, List.sum_replicate_nat, Nat.mul_assoc]
