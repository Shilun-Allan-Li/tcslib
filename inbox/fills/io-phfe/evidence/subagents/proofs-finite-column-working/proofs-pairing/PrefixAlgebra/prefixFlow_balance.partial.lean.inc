/-- Weighted suffix sums satisfy conservation at every prefix: weighted values
of its children, plus its terminal coefficient when its depth is maximal, equal
its own suffix value. This is the path-sum version of the translation calculation
in [AGW20, Appendix A, (28)–(32), pp.37–38], abstracted to a commutative semiring.

**Proof sketch.** For a nonterminal prefix, split each nonempty suffix into its
first label and remaining tuple using the published tuple equivalence, and split
the label product with Fin.prod_univ_succ. Reassociate prefix extension using
Fin.append_right_cons and its canonical casts. At maximal depth the only suffix
is empty and the only matching terminal coefficient is its own full tuple. -/
theorem prefixFlow_balance {I R : Type*} [Fintype I] [DecidableEq I]
    [CommSemiring R] (d : ℕ) (c : (Fin d → I) → R) (weight : I → R)
    (u : Σ k : Fin (d + 1), Fin k.val → I) :
    let value : (Σ k : Fin (d + 1), Fin k.val → I) → R :=
      fun v => ∑ sigma : Fin (d - v.1.val) → I,
        c (fun i => Fin.append v.2 sigma
          (Fin.cast (Nat.add_sub_of_le (Nat.le_of_lt_succ v.1.isLt)).symm i)) *
            ∏ i : Fin (d - v.1.val), weight (sigma i)
    (∑ e : (Σ k : Fin d, Fin (k.val + 1) → I),
      if (⟨e.1.castSucc, Fin.init e.2⟩ :
          Σ k : Fin (d + 1), Fin k.val → I) = u then
        value ⟨e.1.succ, e.2⟩ * weight (e.2 (Fin.last e.1.val)) else 0) +
      (∑ tau : Fin d → I,
        if u = (⟨Fin.last d, tau⟩ : Σ k : Fin (d + 1), Fin k.val → I) then
          c tau else 0) = value u := by
  let value : (Σ k : Fin (d + 1), Fin k.val → I) → R :=
    fun v => ∑ sigma : Fin (d - v.1.val) → I,
      c (fun i => Fin.append v.2 sigma
        (Fin.cast (Nat.add_sub_of_le (Nat.le_of_lt_succ v.1.isLt)).symm i)) *
          ∏ i : Fin (d - v.1.val), weight (sigma i)
  change
    (∑ e : (Σ k : Fin d, Fin (k.val + 1) → I),
      if (⟨e.1.castSucc, Fin.init e.2⟩ :
          Σ k : Fin (d + 1), Fin k.val → I) = u then
        value ⟨e.1.succ, e.2⟩ * weight (e.2 (Fin.last e.1.val)) else 0) +
      (∑ sigma : Fin d → I,
        if u = (⟨Fin.last d, sigma⟩ : Σ k : Fin (d + 1), Fin k.val → I) then
          c sigma else 0) = value u
  rcases u with ⟨k, tau⟩
  cases k using Fin.lastCases with
  | last =>
    -- No parent edge has terminal depth; the terminal tuple is unique.
    have hparent : ∀ e : (Σ k : Fin d, Fin (k.val + 1) → I),
        (⟨e.1.castSucc, Fin.init e.2⟩ :
          Σ k : Fin (d + 1), Fin k.val → I) ≠ ⟨Fin.last d, tau⟩ :=
      fun e h => Fin.castSucc_ne_last e.1 (congrArg Sigma.fst h)
    have hleaf : Function.Injective
        (fun sigma : Fin d → I =>
          (⟨Fin.last d, sigma⟩ : Σ k : Fin (d + 1), Fin k.val → I)) :=
      @sigma_mk_injective (Fin (d + 1)) (fun k => Fin k.val → I) (Fin.last d)
    simp only [hparent, if_false, Finset.sum_const_zero, zero_add,
      hleaf.eq_iff, Fintype.sum_ite_eq]
    -- Remove the empty suffix before transporting its dependent index type.
    simp only [value, Fin.val_last]
    simp only [Fin.append_right_nil _ _ (Nat.sub_self d), Function.comp_apply,
      Fin.cast_cast, Fin.cast_refl, id_eq]
    rw [Nat.sub_self]
    simp only [Fin.prod_univ_zero, mul_one]
    exact (Fintype.sum_subsingleton (fun _ : Fin 0 → I => c tau) Fin.elim0).symm
  | cast k =>
    -- No terminal tuple has the current strictly smaller depth.
    have hterminal : ∀ sigma : Fin d → I,
        (⟨k.castSucc, tau⟩ : Σ k : Fin (d + 1), Fin k.val → I) ≠
          ⟨Fin.last d, sigma⟩ :=
      fun sigma h => Fin.castSucc_ne_last k (congrArg Sigma.fst h)
    simp only [hterminal, if_false, Finset.sum_const_zero, add_zero]
    -- Remaining: classify the parent fiber, then split the nonempty suffix sum.
    exact sorry
