
/-! ### Expectations and probabilities under a pushforward -/

section Pushforward

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

/-- **Expectation under a pushforward composes the function**: the expectation of `g` under the
pushforward of `p` along `f` is the expectation of `g ∘ f` under `p`,
`E_{map f p}[g] = E_p[g ∘ f]`. Framework glue, no textbook counterpart. -/
protected theorem FinDist.expect_map [DecidableEq β] (p : FinDist α) (f : α → β) (g : β → ℝ) :
    (p.map f).expect g = p.expect (fun a => g (f a)) := by
  rw [FinDist.expect_eq, FinDist.expect_eq]
  exact FinDist.sum_map p f g

/-- **Acceptance under a pushforward composes the test**: the probability that `D` accepts a
sample of the pushforward of `p` along `f` is the probability that `D ∘ f` accepts a sample of
`p`, `Pr_{map f p}[D = 1] = Pr_p[D ∘ f = 1]`. Framework glue, no textbook counterpart. -/
protected theorem FinDist.probTrue_map [DecidableEq β] (p : FinDist α) (f : α → β) (D : β → Bool) :
    (p.map f).probTrue D = p.probTrue (fun a => D (f a)) := by
  rw [FinDist.probTrue_eq_expect, FinDist.expect_map, FinDist.probTrue_eq_expect]

/-- **A pushforward's mass is the expectation of an indicator**: the pushforward of `p` along
`f` gives `b` the expectation under `p` of the indicator of `f a = b`,
`map f p b = E_p[1_{f a = b}]`. Framework glue, no textbook counterpart. -/
protected theorem FinDist.map_apply_expect [DecidableEq β] (p : FinDist α) (f : α → β) (b : β) :
    (p.map f) b = p.expect (fun a => if f a = b then 1 else 0) := by
  classical
  rw [FinDist.map_apply, FinDist.expect_eq, sum_filter]
  apply sum_congr rfl
  intro a _
  split_ifs <;> simp

/-- **Successive pushforwards compose**: pushing `p` forward along `f` and then along `g` is
pushing it forward along `g ∘ f`, `map g (map f p) = map (g ∘ f) p`.
Framework glue, no textbook counterpart. -/
protected theorem FinDist.map_map [DecidableEq β] [DecidableEq γ] (p : FinDist α) (f : α → β)
    (g : β → γ) : (p.map f).map g = p.map (fun a => g (f a)) := by
  classical
  apply FinDist.ext
  intro c
  rw [FinDist.map_apply_expect, FinDist.expect_map, FinDist.map_apply_expect]

/-- **A pushforward of the second coordinate commutes with pairing**: mapping the second
coordinate of an independent pair by `f` before pairing, and then mapping the pair by `g`, is
mapping the pair by `(x, y) ↦ g (x, f y)`,
`map g (p × map f q) = map (fun z => g (z.1, f z.2)) (p × q)`.
Framework glue, no textbook counterpart. -/
protected theorem FinDist.map_prod_snd [DecidableEq β] [DecidableEq γ] {δ : Type*} [Fintype δ]
    [DecidableEq δ] (p : FinDist α) (q : FinDist β) (f : β → γ) (g : α × γ → δ) :
    (p.prod (q.map f)).map g = (p.prod q).map (fun z => g (z.1, f z.2)) := by
  classical
  apply FinDist.ext
  intro d
  rw [FinDist.map_apply_expect, FinDist.map_apply_expect, FinDist.expect_prod,
    FinDist.expect_prod]
  congr 1
  funext a
  exact FinDist.expect_map q f (fun c => if g (a, c) = d then 1 else 0)

end Pushforward
