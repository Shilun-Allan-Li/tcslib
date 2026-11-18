-- Replace only the existing `cast k` branch of prefixFlow_balance.
-- Context: the proof's original local value, k : Fin d, tau : Fin k.val → I.
  | cast k =>
    have hterminal : ∀ sigma : Fin d → I,
        (⟨k.castSucc, tau⟩ : Σ j : Fin (d + 1), Fin j.val → I) ≠
          ⟨Fin.last d, sigma⟩ :=
      fun sigma h => Fin.castSucc_ne_last k (congrArg Sigma.fst h)
    simp only [hterminal, if_false, Finset.sum_const_zero, add_zero]
    rw [prefixOutgoing_sum d,
      dif_pos (show (⟨k.castSucc, tau⟩ :
        Σ j : Fin (d + 1), Fin j.val → I).1.val < d from k.isLt)]
    simp only [Fin.snoc_last]
    change (∑ a : I,
      value ⟨k.succ, Fin.snoc (α := fun _ => I) tau a⟩ * weight a) =
        value ⟨k.castSucc, tau⟩
    -- Keep both suffix index types fixed and relate them by an equivalence.
    let r : ℕ := d - (k.val + 1)
    have hlen : r + 1 = d - k.val :=
      (congrArg Nat.succ (Nat.sub_succ d k.val)).trans
        (Nat.succ_pred_eq_of_pos (Nat.sub_pos_of_lt k.isLt))
    have hParent : d = k.val + (d - k.val) :=
      (Nat.add_sub_of_le (Nat.le_of_lt k.isLt)).symm
    have hChild : d = (k.val + 1) + r :=
      (Nat.add_sub_of_le (Nat.succ_le_of_lt k.isLt)).symm
    let suffixEquiv : (I × (Fin r → I)) ≃ (Fin (d - k.val) → I) :=
      (Fin.consEquiv (fun _ : Fin (r + 1) => I)).trans
        (Equiv.arrowCongr (finCongr hlen) (Equiv.refl I))
    change (∑ a : I,
      (∑ sigma : Fin r → I,
        c (fun i => Fin.append (Fin.snoc (α := fun _ => I) tau a) sigma
          (Fin.cast hChild i)) * ∏ i : Fin r, weight (sigma i)) * weight a) =
      ∑ sigma : Fin (d - k.val) → I,
        c (fun i => Fin.append tau sigma (Fin.cast hParent i)) *
          ∏ i : Fin (d - k.val), weight (sigma i)
    rw [← suffixEquiv.sum_comp (fun sigma : Fin (d - k.val) → I =>
      c (fun i => Fin.append tau sigma (Fin.cast hParent i)) *
        ∏ i : Fin (d - k.val), weight (sigma i)), Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro sigma _
    -- Reuse product reindexing and the first-coordinate product recurrence.
    have hProduct := (finCongr hlen.symm).prod_comp
      (fun i : Fin (r + 1) => weight (Fin.cons (α := fun _ => I) a sigma i))
    change (∏ i : Fin (d - k.val), weight (suffixEquiv (a, sigma) i)) =
      ∏ i : Fin (r + 1), weight (Fin.cons (α := fun _ => I) a sigma i) at hProduct
    rw [Fin.prod_univ_succ] at hProduct
    simp only [Fin.cons_zero, Fin.cons_succ] at hProduct
    -- The two complete tuples agree by the published append and cast identities.
    have hExtend :
        (fun i : Fin d => Fin.append tau (suffixEquiv (a, sigma))
          (Fin.cast hParent i)) =
        (fun i : Fin d => Fin.append (Fin.snoc (α := fun _ => I) tau a) sigma
          (Fin.cast hChild i)) := ?_
    swap
    · funext i
      change Fin.append tau ((Fin.cons (α := fun _ => I) a sigma) ∘ Fin.cast hlen.symm)
        (Fin.cast hParent i) =
        Fin.append (Fin.snoc (α := fun _ => I) tau a) sigma (Fin.cast hChild i)
      rw [Fin.append_cast_right tau
        (Fin.cons (α := fun _ => I) a sigma) (d - k.val) hlen.symm,
        Fin.append_right_cons tau a sigma]
      simp only [Function.comp_apply, Fin.cast_cast]
    rw [hExtend, hProduct]
    exact (mul_right_comm _ _ _).trans (mul_assoc _ _ _)
