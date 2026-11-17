/-- The chain only extends the gate list: `gs <+: (layerChain N gs a b s).1`.  Glue. -/
private theorem layerChain_isPrefix {N : ℕ} :
    ∀ {s : ℕ} {gs : List DAGGate} {a b : ℕ}, gs <+: (layerChain N gs a b s).1
  | 0, gs, a, b => by rw [layerChain_zero]; exact List.prefix_refl gs
  | s + 1, gs, a, b => by
    rw [layerChain_succ]
    exact (List.prefix_append _ _).trans layerChain_isPrefix

/-- The chain appends two gates per link:
`(layerChain N gs a b s).1.length = gs.length + 2 * s`.  Glue. -/
private theorem length_layerChain_fst {N : ℕ} :
    ∀ {s : ℕ} {gs : List DAGGate} {a b : ℕ}, (layerChain N gs a b s).1.length = gs.length + 2 * s
  | 0, gs, a, b => by rw [layerChain_zero]; rfl
  | s + 1, gs, a, b => by
    rw [layerChain_succ, length_layerChain_fst, List.length_append]
    simp only [List.length_cons, List.length_nil]
    omega

/-- Every gate the chain appends reads one vertex: `g ∈ (layerChain N gs a b s).1 →
g ∈ gs ∨ ∃ w, g = ⟨.not, [w]⟩`.  Glue. -/
private theorem mem_layerChain_fst {N : ℕ} :
    ∀ {s : ℕ} {gs : List DAGGate} {a b : ℕ} {g : DAGGate}, g ∈ (layerChain N gs a b s).1 →
      g ∈ gs ∨ ∃ w, g = ⟨.not, [w]⟩
  | 0, gs, a, b, g, hg => by rw [layerChain_zero] at hg; exact Or.inl hg
  | s + 1, gs, a, b, g, hg => by
    rw [layerChain_succ] at hg
    rcases mem_layerChain_fst hg with hg | hg
    · rcases List.mem_append.mp hg with hg | hg
      · exact Or.inl hg
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl
        · exact Or.inr ⟨_, rfl⟩
        · exact Or.inr ⟨_, rfl⟩
    · exact Or.inr hg

/-- Every outer vertex the chain records lies below the final vertex count:
`w ∈ (layerChain N gs a b s).2 → w < N + gs.length + 2 * s`.  Glue. -/
private theorem layerChain_snd_lt {N : ℕ} :
    ∀ {s : ℕ} {gs : List DAGGate} {a b w : ℕ}, w ∈ (layerChain N gs a b s).2 →
      w < N + gs.length + 2 * s
  | 0, gs, a, b, w, hw => by rw [layerChain_zero] at hw; exact absurd hw List.not_mem_nil
  | s + 1, gs, a, b, w, hw => by
    rw [layerChain_succ] at hw
    rcases List.mem_cons.mp hw with rfl | hw
    · omega
    · have := layerChain_snd_lt hw
      simp only [List.length_append, List.length_cons, List.length_nil] at this
      omega

/-- The chain keeps a gate list acyclic when its two start vertices exist:
`GatesAcyclic N gs → a < N + gs.length → b < N + gs.length →
GatesAcyclic N (layerChain N gs a b s).1`.  Glue. -/
private theorem layerChain_acyclic {N : ℕ} :
    ∀ {s : ℕ} {gs : List DAGGate} {a b : ℕ}, GatesAcyclic N gs → a < N + gs.length →
      b < N + gs.length → GatesAcyclic N (layerChain N gs a b s).1
  | 0, gs, a, b, h, _, _ => by rw [layerChain_zero]; exact h
  | s + 1, gs, a, b, h, ha, hb => by
    rw [layerChain_succ]
    have h1 := h.snoc (g := ⟨.not, [a]⟩) (by simpa using ha)
    have h2 := h1.snoc (g := ⟨.not, [N + gs.length]⟩) (by simp)
    rw [List.append_assoc] at h2
    exact layerChain_acyclic h2 (by simp; omega) (by simp; omega)

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
column `col` with entries below its new vertex count, extends `s.1` (`s.1 <+: _`) acyclically by
at most `2 * C.depth + 1` gates, and keeps every gate a NAND gate when `C.IsNANDForm`.  Glue.

**Proof sketch.** Case split along `layerColumn_eq`.  Dead vertex and input with `D = 0`: no
gate.  Input: the twin `NAND[n + v]` reads an input, then `D - 1` chain links
(`layerChain_acyclic`, `length_layerChain_fst`, `layerChain_snd_lt`).  Gate: the base reads
recorded copies (`layerAt_lt`); the twin reads copies, or `NAND[0, n]` then `NAND[m + 1]`; then
`D - δ - 1` links.  The NAND-gate property comes from `isNAND_iff` (the copies keep the old
fan-in, the old gate is a NAND gate or the default `⟨.not, []⟩`) and `mem_layerChain_fst`. -/
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
  have hL : ∀ u k, C.layerAt s.2 u k < n + n + s.1.length := fun u k =>
    C.layerAt_lt (by omega) hcol u k
  have h1 : ∀ w : ℕ, (⟨.not, [w]⟩ : DAGGate).IsNAND := fun w =>
    (DAGGate.isNAND_iff _).mpr ⟨rfl, by simp⟩
  -- the NAND property of a gate list `s.1 ++ pre` followed by a chain
  have hch : ∀ (pre : List DAGGate) (g : DAGGate), C.IsNANDForm → (∀ g ∈ pre, g.IsNAND) →
      ∀ {t a b : ℕ}, g ∈ (layerChain (n + n) (s.1 ++ pre) a b t).1 → g.IsNAND := by
    intro pre g hC hpre t a b hg
    rcases mem_layerChain_fst hg with hg | ⟨w, rfl⟩
    · rcases List.mem_append.mp hg with hg | hg
      · exact hnand hC g hg
      · exact hpre g hg
    · exact h1 w
  rw [layerColumn_eq]
  by_cases hd : C.depth < C.depthAt v
  · rw [if_pos hd]
    exact ⟨⟨[], rfl, by simp⟩, List.prefix_refl _, hacy, hnand, by simp⟩
  rw [if_neg hd]
  by_cases hv : v < n
  · rw [if_pos hv]
    by_cases h3 : C.depth = 0
    · rw [if_pos h3]
      exact ⟨⟨[v], rfl, by simp; omega⟩, List.prefix_refl _, hacy, hnand, by simp⟩
    rw [if_neg h3]
    have hacy0 : GatesAcyclic (n + n) (s.1 ++ [⟨.not, [n + v]⟩]) := hacy.snoc (by simp; omega)
    refine ⟨⟨_, rfl, ?_⟩, (List.prefix_append _ _).trans layerChain_isPrefix,
      layerChain_acyclic hacy0 (by simp; omega) (by simp), fun hC g hg =>
        hch _ g hC (by simp only [List.mem_singleton]; rintro _ rfl; exact h1 _) hg, ?_⟩
    · intro w hw
      rw [length_layerChain_fst]
      simp only [List.mem_cons] at hw
      rcases hw with rfl | rfl | hw
      · simp; omega
      · simp; omega
      · have := layerChain_snd_lt hw
        simp only [List.length_append, List.length_cons, List.length_nil] at this ⊢
        omega
    · rw [length_layerChain_fst]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
  rw [if_neg hv]
  have hgN : C.IsNANDForm → (C.gates.getD (v - n) ⟨.not, []⟩).IsNAND := by
    intro hC
    rw [List.getD_eq_getElem?_getD]
    rcases hg : C.gates[v - n]? with _ | g
    · exact (DAGGate.isNAND_iff _).mpr ⟨rfl, by simp⟩
    · exact (DAGCircuit.isNANDForm_iff C).mp hC g (List.mem_of_getElem? hg)
  generalize C.gates.getD (v - n) ⟨.not, []⟩ = g at hgN ⊢
  have hb0 : ∀ k, GatesAcyclic (n + n)
      (s.1 ++ [⟨.not, g.args.map fun a => C.layerAt s.2 a k⟩]) := fun k =>
    hacy.snoc (by simp only [List.mem_map]; rintro _ ⟨a, -, rfl⟩; exact hL a k)
  have hbN : ∀ k, C.IsNANDForm →
      (⟨.not, g.args.map fun a => C.layerAt s.2 a k⟩ : DAGGate).IsNAND := fun k hC =>
    (DAGGate.isNAND_iff _).mpr ⟨rfl, by simpa using ((DAGGate.isNAND_iff g).mp (hgN hC)).2⟩
  by_cases h4 : C.depth = C.depthAt v
  · rw [if_pos h4]
    refine ⟨⟨_, rfl, by simp⟩, List.prefix_append _ _, hb0 _, ?_, by simp⟩
    intro hC g' hg'
    rcases List.mem_append.mp hg' with hg' | hg'
    · exact hnand hC g' hg'
    · rw [List.mem_singleton.mp hg']; exact hbN _ hC
  rw [if_neg h4]
  by_cases h5 : g.args = []
  · rw [if_pos h5]
    have hacy1 : GatesAcyclic (n + n) (s.1 ++ [⟨.not, g.args.map fun a =>
        C.layerAt s.2 a (C.depthAt v - 1)⟩] ++
          [⟨.not, [0, n]⟩, ⟨.not, [n + n + s.1.length + 1]⟩]) := by
      have h2 := (hb0 (C.depthAt v - 1)).snoc (g := ⟨.not, [0, n]⟩) (by simp; omega)
      have h3 := h2.snoc (g := ⟨.not, [n + n + s.1.length + 1]⟩) (by simp)
      simpa using h3
    refine ⟨⟨_, rfl, ?_⟩,
      ((List.prefix_append _ _).trans (List.prefix_append _ _)).trans layerChain_isPrefix,
      layerChain_acyclic hacy1 (by simp) (by simp; omega), fun hC g' hg' =>
        hch _ g' hC ?_ hg', ?_⟩
    · intro w hw
      rw [length_layerChain_fst]
      simp only [List.mem_cons] at hw
      rcases hw with rfl | rfl | hw
      · simp; omega
      · simp; omega
      · have := layerChain_snd_lt hw
        simp only [List.length_append, List.length_cons, List.length_nil] at this ⊢
        omega
    · intro g'' hg''
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg''
      rcases hg'' with rfl | rfl | rfl
      · exact hbN _ hC
      · exact (DAGGate.isNAND_iff _).mpr ⟨rfl, by simp⟩
      · exact h1 _
    · rw [length_layerChain_fst]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
  · rw [if_neg h5]
    have hacy1 : GatesAcyclic (n + n) (s.1 ++ [⟨.not, g.args.map fun a =>
        C.layerAt s.2 a (C.depthAt v - 1)⟩] ++
          [⟨.not, g.args.map fun a => C.layerAt s.2 a (C.depthAt v)⟩]) :=
      (hb0 (C.depthAt v - 1)).snoc (by
        simp only [List.mem_map]; rintro _ ⟨a, -, rfl⟩; have := hL a (C.depthAt v); simp; omega)
    refine ⟨⟨_, rfl, ?_⟩,
      ((List.prefix_append _ _).trans (List.prefix_append _ _)).trans layerChain_isPrefix,
      layerChain_acyclic hacy1 (by simp) (by simp), fun hC g' hg' =>
        hch _ g' hC ?_ hg', ?_⟩
    · intro w hw
      rw [length_layerChain_fst]
      simp only [List.mem_cons] at hw
      rcases hw with rfl | rfl | hw
      · simp; omega
      · simp; omega
      · have := layerChain_snd_lt hw
        simp only [List.length_append, List.length_cons, List.length_nil] at this ⊢
        omega
    · intro g'' hg''
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg''
      rcases hg'' with rfl | rfl
      · exact hbN _ hC
      · exact hbN _ hC
    · rw [length_layerChain_fst]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega

/-- The column fold, structurally, after the old vertices `0, …, v - 1`: with
`s = (List.range v).foldl C.layerColumn ([], [])`, `s.2.length = v`, `s.1` is acyclic over the
`n + n` inputs, every column entry lies below `n + n + |s.1|`, every gate is a NAND gate when
`C.IsNANDForm`, and `s.1.length ≤ (2 * C.depth + 1) * v`.  Glue.

**Proof sketch.** Induction on `v` (`List.range_succ`, `List.foldl_append`), one step being
`layerColumn_struct`; the old columns stay in range because the gate list only grows
(`List.IsPrefix.length_le`). -/
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
    refine ⟨by rw [hc, List.length_append, h1]; rfl, ha, ?_, hn, ?_⟩
    · intro c hc' w hw
      rw [hc, List.mem_append, List.mem_singleton] at hc'
      rcases hc' with hc' | rfl
      · have := h3 c hc' w hw
        have := hp.length_le
        omega
      · exact hcw w hw
    · rw [Nat.mul_succ]
      omega
