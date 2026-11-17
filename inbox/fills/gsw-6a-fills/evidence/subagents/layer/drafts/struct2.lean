/-- The chain only extends the gate list: `gs <+: (layerChain N gs a b s).1`.  Glue. -/
private theorem layerChain_isPrefix {N : ℕ} :
    ∀ {s : ℕ} {gs : List DAGGate} {a b : ℕ}, gs <+: (layerChain N gs a b s).1
  | 0, gs, a, b => by rw [layerChain_zero]
  | s + 1, gs, a, b => by
    rw [layerChain_succ]; exact (List.prefix_append _ _).trans layerChain_isPrefix

/-- The chain appends two gates per link:
`(layerChain N gs a b s).1.length = gs.length + 2 * s`.  Glue. -/
private theorem length_layerChain_fst {N : ℕ} :
    ∀ {s : ℕ} {gs : List DAGGate} {a b : ℕ}, (layerChain N gs a b s).1.length = gs.length + 2 * s
  | 0, gs, a, b => by rw [layerChain_zero]; rfl
  | s + 1, gs, a, b => by
    rw [layerChain_succ, length_layerChain_fst, List.length_append]; simp; omega

/-- Every gate the chain appends reads one vertex: `g ∈ (layerChain N gs a b s).1 →
g ∈ gs ∨ ∃ w, g = ⟨.not, [w]⟩`.  Glue. -/
private theorem mem_layerChain_fst {N : ℕ} :
    ∀ {s : ℕ} {gs : List DAGGate} {a b : ℕ} {g : DAGGate}, g ∈ (layerChain N gs a b s).1 →
      g ∈ gs ∨ ∃ w, g = ⟨.not, [w]⟩
  | 0, gs, a, b, g, hg => by rw [layerChain_zero] at hg; exact Or.inl hg
  | s + 1, gs, a, b, g, hg => by
    rw [layerChain_succ] at hg
    rcases mem_layerChain_fst hg with hg | hg
    · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with hg | rfl | rfl
      exacts [Or.inl hg, Or.inr ⟨_, rfl⟩, Or.inr ⟨_, rfl⟩]
    · exact Or.inr hg

/-- The chain keeps a gate list acyclic, and its column `a :: b :: (outer vertices)` lies below
the vertex count, when `a` and `b` exist: `GatesAcyclic N gs → a < N + |gs| → b < N + |gs| →
GatesAcyclic N (layerChain N gs a b s).1 ∧
∀ w ∈ a :: b :: (layerChain N gs a b s).2, w < N + (layerChain N gs a b s).1.length`.  Glue. -/
private theorem layerChain_acyclic {N : ℕ} :
    ∀ {s : ℕ} {gs : List DAGGate} {a b : ℕ}, GatesAcyclic N gs → a < N + gs.length →
      b < N + gs.length → GatesAcyclic N (layerChain N gs a b s).1 ∧
        ∀ w ∈ a :: b :: (layerChain N gs a b s).2, w < N + (layerChain N gs a b s).1.length
  | 0, gs, a, b, h, ha, hb => by rw [layerChain_zero]; exact ⟨h, by simp [ha, hb]⟩
  | s + 1, gs, a, b, h, ha, hb => by
    have h2 := (h.snoc (g := ⟨.not, [a]⟩) (by simpa using ha)).snoc
      (g := ⟨.not, [N + gs.length]⟩) (by simp)
    rw [List.append_assoc] at h2
    have hl := (layerChain_isPrefix (N := N) (s := s + 1) (gs := gs) (a := a) (b := b)).length_le
    rw [layerChain_succ] at hl ⊢
    obtain ⟨h3, h4⟩ := layerChain_acyclic (s := s) h2 (by simp; omega) (by simp; omega)
    refine ⟨h3, fun w hw => ?_⟩
    rcases List.mem_cons.mp hw with rfl | hw
    exacts [by omega, h4 w hw]

/-- A recorded copy is below any positive bound `B` of all column entries:
`0 < B → (∀ col ∈ cols, ∀ w ∈ col, w < B) → C.layerAt cols v k < B` (a missing copy reads as
`0`).  Glue. -/
private theorem DAGCircuit.layerAt_lt (C : DAGCircuit n) {cols : List (List ℕ)} {B : ℕ}
    (hB : 0 < B) (h : ∀ col ∈ cols, ∀ w ∈ col, w < B) (v k : ℕ) : C.layerAt cols v k < B := by
  rw [layerAt_eq, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  rcases hc : cols[v]? with _ | col
  · simpa using hB
  · rcases hw : col[k - C.depthAt v]? with _ | w
    · simpa [hw] using hB
    · simpa [hw] using h col (List.mem_of_getElem? hc) w (List.mem_of_getElem? hw)

/-- One fold step, structurally: if the gates `s.1` are acyclic over the `n + n` literal inputs
and every column entry of `s.2` lies below `n + n + |s.1|`, then `C.layerColumn s v` appends one
column with entries below its new vertex count, extends `s.1` (`s.1 <+: _`) acyclically by at
most `2 * C.depth + 1` gates, and keeps every gate a NAND gate when `C.IsNANDForm`.  Glue.

**Proof sketch.** Case split along `layerColumn_eq`.  Step 1: a column `a :: b :: chain` after
`p` new gates `pre` (`layerChain_acyclic`, `length_layerChain_fst`, `mem_layerChain_fst`).
A dead vertex and an input with `D = 0` add no gate; an input adds the twin `NAND[n + v]`; a
gate adds the base, reading recorded copies (`layerAt_lt`), and, below the top, the twin, reading
copies or `NAND[0, n]` then `NAND[m + 1]`.  The new gates are NAND gates by `isNAND_iff` (the
copies keep the old fan-in; the old gate is a NAND gate or the default `⟨.not, []⟩`). -/
private theorem DAGCircuit.layerColumn_struct [NeZero n] (C : DAGCircuit n)
    (s : List DAGGate × List (List ℕ)) (v : ℕ) (hacy : GatesAcyclic (n + n) s.1)
    (hcol : ∀ col ∈ s.2, ∀ w ∈ col, w < n + n + s.1.length)
    (hnand : C.IsNANDForm → ∀ g ∈ s.1, g.IsNAND) :
    (∃ col, (C.layerColumn s v).2 = s.2 ++ [col] ∧
      ∀ w ∈ col, w < n + n + (C.layerColumn s v).1.length) ∧
    s.1 <+: (C.layerColumn s v).1 ∧ GatesAcyclic (n + n) (C.layerColumn s v).1 ∧
    (C.IsNANDForm → ∀ g ∈ (C.layerColumn s v).1, g.IsNAND) ∧
    (C.layerColumn s v).1.length ≤ s.1.length + (2 * C.depth + 1) := by
  have hn : 0 < n := Nat.pos_of_neZero n
  have h1 : ∀ w : ℕ, (⟨.not, [w]⟩ : DAGGate).IsNAND := fun w =>
    (DAGGate.isNAND_iff _).mpr ⟨rfl, by simp⟩
  -- Step 1: a column `a :: b :: chain` after the `p` gates `pre`
  have hch : ∀ (pre : List DAGGate) (p a b t : ℕ), pre.length = p →
      GatesAcyclic (n + n) (s.1 ++ pre) → (C.IsNANDForm → ∀ g ∈ pre, g.IsNAND) →
      a < n + n + s.1.length + p → b < n + n + s.1.length + p → p + 2 * t ≤ 2 * C.depth + 1 →
      (∃ col, s.2 ++ [a :: b :: (layerChain (n + n) (s.1 ++ pre) a b t).2] = s.2 ++ [col] ∧
        ∀ w ∈ col, w < n + n + (layerChain (n + n) (s.1 ++ pre) a b t).1.length) ∧
      s.1 <+: (layerChain (n + n) (s.1 ++ pre) a b t).1 ∧
      GatesAcyclic (n + n) (layerChain (n + n) (s.1 ++ pre) a b t).1 ∧
      (C.IsNANDForm → ∀ g ∈ (layerChain (n + n) (s.1 ++ pre) a b t).1, g.IsNAND) ∧
      (layerChain (n + n) (s.1 ++ pre) a b t).1.length ≤ s.1.length + (2 * C.depth + 1) := by
    intro pre p a b t hp hacy' hpre ha hb ht
    obtain ⟨h3, h4⟩ := layerChain_acyclic (s := t) hacy' (by simp; omega) (by simp; omega)
    refine ⟨⟨_, rfl, h4⟩, (List.prefix_append _ _).trans layerChain_isPrefix, h3,
      fun hC g hg => ?_, by rw [length_layerChain_fst, List.length_append]; omega⟩
    rcases mem_layerChain_fst hg with hg | ⟨w, rfl⟩
    · rcases List.mem_append.mp hg with hg | hg
      exacts [hnand hC g hg, hpre hC g hg]
    · exact h1 w
  rw [layerColumn_eq]
  by_cases hd : C.depth < C.depthAt v
  · rw [if_pos hd]; exact ⟨⟨[], rfl, by simp⟩, List.prefix_refl _, hacy, hnand, by simp⟩
  rw [if_neg hd]
  by_cases hv : v < n
  · rw [if_pos hv]
    by_cases h3 : C.depth = 0
    · rw [if_pos h3]
      exact ⟨⟨[v], rfl, by simp; omega⟩, List.prefix_refl _, hacy, hnand, by simp⟩
    rw [if_neg h3]
    exact hch _ 1 _ _ _ rfl (hacy.snoc (by simp; omega))
      (fun _ g hg => by rw [List.mem_singleton.mp hg]; exact h1 _) (by omega) (by omega)
      (by omega)
  rw [if_neg hv]
  have hgN : C.IsNANDForm → (C.gates.getD (v - n) ⟨.not, []⟩).IsNAND := by
    intro hC
    rw [List.getD_eq_getElem?_getD]
    rcases hg : C.gates[v - n]? with _ | g
    · exact (DAGGate.isNAND_iff _).mpr ⟨rfl, by simp⟩
    · exact (DAGCircuit.isNANDForm_iff C).mp hC g (List.mem_of_getElem? hg)
  generalize C.gates.getD (v - n) ⟨.not, []⟩ = g at hgN ⊢
  -- the base and the twin read recorded copies, below the vertex count, and keep the fan-in
  have hb : ∀ k, (∀ w ∈ (⟨.not, g.args.map fun a => C.layerAt s.2 a k⟩ : DAGGate).args,
      w < n + n + s.1.length) ∧
        (C.IsNANDForm → (⟨.not, g.args.map fun a => C.layerAt s.2 a k⟩ : DAGGate).IsNAND) :=
    fun k => ⟨by
      simp only [List.mem_map]; rintro _ ⟨a, -, rfl⟩; exact C.layerAt_lt (by omega) hcol a k,
      fun hC => (DAGGate.isNAND_iff _).mpr
        ⟨rfl, by simpa using ((DAGGate.isNAND_iff g).mp (hgN hC)).2⟩⟩
  have hacy1 := hacy.snoc (hb (C.depthAt v - 1)).1
  by_cases h4 : C.depth = C.depthAt v
  · rw [if_pos h4]
    refine ⟨⟨_, rfl, by simp⟩, List.prefix_append _ _, hacy1, fun hC g' hg' => ?_, by simp⟩
    rcases List.mem_append.mp hg' with hg' | hg'
    exacts [hnand hC g' hg', (List.mem_singleton.mp hg') ▸ (hb _).2 hC]
  rw [if_neg h4]
  dsimp only
  by_cases h5 : g.args = []
  · rw [if_pos h5]
    dsimp only
    rw [List.append_assoc]
    have h2 := (hacy1.snoc (g := ⟨.not, [0, n]⟩) (by simp; omega)).snoc
      (g := ⟨.not, [n + n + s.1.length + 1]⟩) (by simp; omega)
    exact hch _ 3 _ _ _ rfl (by simpa using h2) (fun hC g' hg' => by
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg'
        rcases hg' with rfl | rfl | rfl
        exacts [(hb _).2 hC, (DAGGate.isNAND_iff _).mpr ⟨rfl, by simp⟩, h1 _])
      (by omega) (by omega) (by omega)
  · rw [if_neg h5]
    dsimp only
    rw [List.append_assoc]
    have h2 := hacy1.snoc (g := ⟨.not, g.args.map fun a => C.layerAt s.2 a (C.depthAt v)⟩)
      (fun w hw => by have := (hb _).1 w hw; simp; omega)
    exact hch _ 2 _ _ _ rfl (by simpa using h2) (fun hC g' hg' => by
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg'
        rcases hg' with rfl | rfl
        exacts [(hb _).2 hC, (hb _).2 hC])
      (by omega) (by omega) (by omega)

/-- The column fold, structurally, after the old vertices `0, …, v - 1`: with
`s = (List.range v).foldl C.layerColumn ([], [])`, `s.2.length = v`, `s.1` is acyclic over the
`n + n` inputs, every column entry lies below `n + n + |s.1|`, every gate is a NAND gate when
`C.IsNANDForm`, and `s.1.length ≤ (2 * C.depth + 1) * v`.  Glue (induction on `v` with
`List.range_succ` and `layerColumn_struct`). -/
private theorem DAGCircuit.layerFold_struct [NeZero n] (C : DAGCircuit n) (v : ℕ) :
    ((List.range v).foldl C.layerColumn ([], [])).2.length = v ∧
    GatesAcyclic (n + n) ((List.range v).foldl C.layerColumn ([], [])).1 ∧
    (∀ col ∈ ((List.range v).foldl C.layerColumn ([], [])).2, ∀ w ∈ col,
      w < n + n + ((List.range v).foldl C.layerColumn ([], [])).1.length) ∧
    (C.IsNANDForm → ∀ g ∈ ((List.range v).foldl C.layerColumn ([], [])).1, g.IsNAND) ∧
    ((List.range v).foldl C.layerColumn ([], [])).1.length ≤ (2 * C.depth + 1) * v := by
  induction v with
  | zero => exact ⟨rfl, GatesAcyclic.nil, by simp, by simp, by simp⟩
  | succ v ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize (List.range v).foldl C.layerColumn ([], []) = s at ih ⊢
    obtain ⟨h1, h2, h3, h4, h5⟩ := ih
    obtain ⟨⟨col, hc, hcw⟩, hp, ha, hn, hl⟩ := C.layerColumn_struct s v h2 h3 h4
    refine ⟨by rw [hc, List.length_append, h1]; rfl, ha, fun c hc' w hw => ?_, hn,
      by rw [Nat.mul_succ]; omega⟩
    rw [hc, List.mem_append, List.mem_singleton] at hc'
    rcases hc' with hc' | rfl
    · have := h3 c hc' w hw; have := hp.length_le; omega
    · exact hcw w hw

