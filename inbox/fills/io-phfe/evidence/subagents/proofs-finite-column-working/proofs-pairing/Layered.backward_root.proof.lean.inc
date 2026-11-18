/-- The backward value at the source is the allowed scalar z·f(x).

**Proof sketch.** At the empty prefix the suffix is the full monomial tuple.
Its extension is itself. Exchange the finite output/tuple sums and regroup the
coefficient products into polyTensorEval. -/
theorem backward_root (C : PolyTensor p l n d) (x : Fin l → ZMod (p : ℕ))
    (z : Fin n → ZMod (p : ℕ)) :
    backward C x z (root l d) = dotProduct z (polyTensorEval C x) :=
  let u0 : MIdx l d := ⟨⟨0, Nat.zero_lt_succ d⟩, Fin.elim0⟩
  let hCast : d = 0 + d := (Nat.zero_add d).symm
  let monomial := fun sigma : Fin d → Fin (l + 1) => ∏ i : Fin d, xhat x (sigma i)
  have hExtend : ∀ sigma : Fin d → Fin (l + 1), extend u0 sigma = sigma :=
    fun sigma => (extend_eq u0 sigma).trans
      (funext fun i =>
        (show Fin.append Fin.elim0 sigma (Fin.cast hCast i) = sigma i from
          (congrFun (Fin.elim0_append sigma) (Fin.cast hCast i)).trans
            (congrArg sigma
              ((Fin.cast_cast hCast (Nat.zero_add d) (i := i)).trans
                (congrFun (Fin.cast_refl d (hCast.trans (Nat.zero_add d))) i)))))
  have hWeight : ∀ (sigma : Fin d → Fin (l + 1)) (j : Fin n),
      (C j sigma * z j) * monomial sigma = z j * (C j sigma * monomial sigma) :=
    fun sigma j =>
      (congrArg (fun v : ZMod (p : ℕ) => v * monomial sigma)
        (mul_comm (C j sigma) (z j))).trans (mul_assoc (z j) (C j sigma) (monomial sigma))
  have hSum : (∑ sigma : Fin d → Fin (l + 1),
      (∑ j : Fin n, C j sigma * z j) * monomial sigma) =
        dotProduct z (polyTensorEval C x) :=
    (Finset.sum_congr rfl (fun sigma _ =>
      Finset.sum_mul Finset.univ (fun j : Fin n => C j sigma * z j) (monomial sigma))).trans
      ((Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
        (f := fun (sigma : Fin d → Fin (l + 1)) (j : Fin n) =>
          (C j sigma * z j) * monomial sigma)).trans
        ((Finset.sum_congr rfl (fun j _ =>
          ((Finset.sum_congr rfl (fun sigma _ => hWeight sigma j)).trans
            (Finset.mul_sum Finset.univ
              (fun sigma : Fin d → Fin (l + 1) => C j sigma * monomial sigma) (z j)).symm).trans
            (congrArg (fun v : ZMod (p : ℕ) => z j * v)
              (polyTensorEval_eq C x j).symm))).trans
          (show (∑ j : Fin n, z j * polyTensorEval C x j) =
              dotProduct z (polyTensorEval C x) from rfl)))
  (congrArg (backward C x z) (root_eq l d)).trans
    ((backward_eq C x z u0).trans
      ((Finset.sum_congr rfl (fun sigma _ =>
        congrArg (fun tau : Fin d → Fin (l + 1) =>
          (∑ j : Fin n, C j tau * z j) * monomial sigma) (hExtend sigma))).trans hSum))
