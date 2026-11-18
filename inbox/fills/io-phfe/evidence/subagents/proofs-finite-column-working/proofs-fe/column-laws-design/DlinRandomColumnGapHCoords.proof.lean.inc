by
    intro ab rs t L
    apply Prod.ext
    · funext i j
      refine (show (L * C ab rs t) i (Fin.castAdd 1 j) = (L * A ab) i j from ?_)
      rw [Matrix.mul_apply, Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro k _
      apply congrArg (fun z : K => L i k * z)
      fin_cases k <;> fin_cases j <;> rfl
    · funext i
      refine (show (L * C ab rs t) i (2 : Fin 3) =
        L i ⬝ᵥ ![ab 0 * rs 0, ab 1 * rs 1, t] from ?_)
      rw [Matrix.mul_apply']
      apply congrArg (fun v : Fin 3 → K => L i ⬝ᵥ v)
      funext k
      fin_cases k <;> rfl
