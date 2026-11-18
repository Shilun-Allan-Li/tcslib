by
    intro ab rs t
    rw [Matrix.det_fin_three]
    simp only [C, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, mul_zero, zero_mul,
      mul_one, one_mul, sub_zero, add_zero, zero_add]
    ring
