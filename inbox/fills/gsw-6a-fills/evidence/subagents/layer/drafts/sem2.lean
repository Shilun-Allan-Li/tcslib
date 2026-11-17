
/-- One fold step, semantically, over the layering `C.layerNAND` (whose gates extend those of
the step, `hpre`): if every recorded copy `u@k` of an earlier live vertex `u < v` has depth `k`
and, under `C.IsNANDForm`, the value of `u` on every literal input, then so has every copy
`v@k` of the new column, for `C.depthAt v ≤ k ≤ C.depth`; and every new gate reads vertices of
one common depth.  Glue.

**Proof sketch.** Case split along `layerColumn_eq`, the copies of `v` read off with
`layerAt_eq` and `List.getD_append_right`.  Input `v` (depth `0`, `depthAt_input`): `v@0` is
input `v`, the twin `NAND[n + v]` has depth `1` and value `!!xᵥ` (`layerNAND_depthAt_snoc`,
`layerNAND_values_snoc`, `layerNAND_values_lit`).  Gate `v = n + j` of depth `δ`
(`depthAt_gate`, `DAGGate.depth_eq`; its arguments are earlier and shallower,
`C.args_lt`, `DAGGate.getD_lt_depth`): the base and the twin read copies of one depth `δ - 1`,
resp. `δ` (`foldr_max_eq_of_forall`), with the gate's value (`values_getD_gate`,
`DAGGate.eval_of_isNAND`, `all_congr_mem`); a fan-in-0 gate has `δ = 1` and twin
`NAND(NAND(x₀, ¬x₀))` of depth `2` and value `false`.  The chain links follow by
`layerChain_col` with `layerNAND_link`; all chain gates read one vertex
(`mem_layerChain_fst`). -/
private theorem DAGCircuit.layerColumn_sem (s : List DAGGate × List (List ℕ)) (v : ℕ)
    (hv : v < n + C.gates.length) (hlen : s.2.length = v)
    (hpre : (C.layerColumn s v).1 <+: C.layerNAND.gates)
    (hsem : ∀ u < v, C.depthAt u ≤ C.depth → ∀ k, C.depthAt u ≤ k → k ≤ C.depth →
      C.layerNAND.depthAt (C.layerAt s.2 u k) = k ∧ (C.IsNANDForm → ∀ x,
        (C.layerNAND.values (litInput x)).getD (C.layerAt s.2 u k) false =
          (C.values x).getD u false)) :
    (C.depthAt v ≤ C.depth → ∀ k, C.depthAt v ≤ k → k ≤ C.depth →
      C.layerNAND.depthAt (C.layerAt (C.layerColumn s v).2 v k) = k ∧ (C.IsNANDForm → ∀ x,
        (C.layerNAND.values (litInput x)).getD (C.layerAt (C.layerColumn s v).2 v k) false =
          (C.values x).getD v false)) ∧
    ∀ g ∈ (C.layerColumn s v).1, g ∈ s.1 ∨ ∃ k, ∀ a ∈ g.args, C.layerNAND.depthAt a = k := by
  have hn : 0 < n := Nat.pos_of_neZero n
  have hcol : ∀ (col : List ℕ) (k : ℕ),
      C.layerAt (s.2 ++ [col]) v k = col.getD (k - C.depthAt v) 0 := by
    intro col k
    rw [layerAt_eq, List.getD_append_right _ _ _ _ hlen.ge, hlen, Nat.sub_self,
      List.getD_cons_zero]
  have hchain := @layerChain_col C.layerNAND.gates (n + n)
    (fun w k => C.layerNAND.depthAt w = k ∧ (C.IsNANDForm → ∀ x,
      (C.layerNAND.values (litInput x)).getD w false = (C.values x).getD v false))
    (fun _ _ _ hp ha => C.layerNAND_link v hp ha)
  have hsingle : ∀ w : ℕ, ∃ k, ∀ a ∈ (⟨.not, [w]⟩ : DAGGate).args, C.layerNAND.depthAt a = k :=
    fun w => ⟨_, fun a ha => by rw [List.mem_singleton.mp ha]⟩
  rw [layerColumn_eq] at hpre ⊢
  by_cases h1 : C.depth < C.depthAt v
  · rw [if_pos h1]
    exact ⟨fun h => absurd h (by omega), fun g hg => Or.inl hg⟩
  rw [if_neg h1] at hpre ⊢
  by_cases h2 : v < n
  · -- Step 1: an input vertex
    rw [if_pos h2] at hpre ⊢
    have hd : C.depthAt v = 0 := C.depthAt_input h2
    have hv0 : C.layerNAND.depthAt v = 0 ∧ (C.IsNANDForm → ∀ x,
        (C.layerNAND.values (litInput x)).getD v false = (C.values x).getD v false) :=
      ⟨C.layerNAND.depthAt_input (by omega), fun _ x => (C.layerNAND_values_lit h2 x).1⟩
    by_cases h3 : C.depth = 0
    · rw [if_pos h3]
      refine ⟨fun _ k hk1 hk2 => ?_, fun g hg => Or.inl hg⟩
      rw [hcol, show k - C.depthAt v = 0 by omega, List.getD_cons_zero, show k = 0 by omega]
      exact hv0
    rw [if_neg h3] at hpre ⊢
    have hp0 : s.1 ++ [⟨.not, [n + v]⟩] <+: C.layerNAND.gates := layerChain_isPrefix.trans hpre
    have hm : C.layerNAND.depthAt (n + n + s.1.length) = 0 + 1 ∧ (C.IsNANDForm → ∀ x,
        (C.layerNAND.values (litInput x)).getD (n + n + s.1.length) false =
          (C.values x).getD v false) := by
      refine ⟨?_, fun hC x => ?_⟩
      · rw [C.layerNAND_depthAt_snoc hp0]
        simp [C.layerNAND.depthAt_input (show n + v < n + n by omega)]
      · rw [C.layerNAND_values_snoc hC hp0]
        simp [(C.layerNAND_values_lit h2 x).2]
    refine ⟨fun _ k hk1 hk2 => ?_, fun g hg => ?_⟩
    · rw [hcol]
      have := hchain hpre hv0 hm (k - C.depthAt v) (by omega)
      rwa [show 0 + (k - C.depthAt v) = k by omega] at this
    · rcases mem_layerChain_fst hg with hg | ⟨w, rfl⟩
      · rcases List.mem_append.mp hg with hg | hg
        · exact Or.inl hg
        · rw [List.mem_singleton.mp hg]; exact Or.inr (hsingle _)
      · exact Or.inr (hsingle w)
  -- Step 2: a gate vertex `v = n + j`, its depth, arguments and value
  rw [if_neg h2] at hpre ⊢
  obtain ⟨j, rfl⟩ : ∃ j, v = n + j := ⟨v - n, by omega⟩
  have hj : j < C.gates.length := by omega
  rw [show n + j - n = j by omega, List.getD_eq_getElem hj] at hpre ⊢
  have hδ : C.depthAt (n + j) =
      1 + ((C.gates[j]).args.map fun a => C.depths.getD a 0).foldr max 0 := by
    rw [C.depthAt_gate hj, DAGGate.depth_eq]
  have harg : ∀ a ∈ (C.gates[j]).args, a < n + j ∧ C.depthAt a < C.depthAt (n + j) :=
    fun a ha => ⟨C.args_lt j hj a ha, by
      rw [C.depthAt_eq a, C.depthAt_gate hj]; exact DAGGate.getD_lt_depth _ _ ha⟩
  have hval : C.IsNANDForm → ∀ x, (C.values x).getD (n + j) false =
      !((C.gates[j]).args.all fun a => (C.values x).getD a false) := fun hC x => by
    rw [C.values_getD_gate x hj,
      DAGGate.eval_of_isNAND ((C.isNANDForm_iff).mp hC _ (List.getElem_mem hj))]
  generalize C.gates[j] = g at hδ harg hval hpre ⊢
  have hδ1 : 1 ≤ C.depthAt (n + j) := by omega
  -- Step 3: a NAND gate over the copies at level `k` of the arguments
  have hgate : ∀ (gs : List DAGGate) (k : ℕ),
      gs ++ [⟨.not, g.args.map fun a => C.layerAt s.2 a k⟩] <+: C.layerNAND.gates →
      g.args ≠ [] → (∀ a ∈ g.args, C.depthAt a ≤ k) → k ≤ C.depth →
      C.layerNAND.depthAt (n + n + gs.length) = k + 1 ∧ (C.IsNANDForm → ∀ x,
        (C.layerNAND.values (litInput x)).getD (n + n + gs.length) false =
          (C.values x).getD (n + j) false) := by
    intro gs k hp hne hk hkD
    have hs := fun a (ha : a ∈ g.args) =>
      hsem a (harg a ha).1 (le_trans (hk a ha) hkD) k (hk a ha) hkD
    refine ⟨?_, fun hC x => ?_⟩
    · obtain ⟨a₀, ha₀⟩ := List.exists_mem_of_ne_nil _ hne
      rw [C.layerNAND_depthAt_snoc hp, List.map_map,
        foldr_max_eq_of_forall (k := k) (fun y hy => ?_) (List.mem_map_of_mem ha₀)]
      · omega
      · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hy
        exact (hs a ha).1
    · rw [C.layerNAND_values_snoc hC hp, List.all_map, hval hC x]
      congr 1
      exact all_congr_mem fun a ha => (hs a ha).2 hC x
  have hbu : ∀ k, (∀ a ∈ g.args, C.depthAt a ≤ k) → k ≤ C.depth →
      ∃ k', ∀ b ∈ (⟨.not, g.args.map fun a => C.layerAt s.2 a k⟩ : DAGGate).args,
        C.layerNAND.depthAt b = k' := fun k hk hkD => ⟨k, fun b hb => by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
    exact (hsem a (harg a ha).1 (le_trans (hk a ha) hkD) k (hk a ha) hkD).1⟩
  -- Step 4: the base copy `v@δ`
  have hbase : s.1 ++ [⟨.not, g.args.map fun a => C.layerAt s.2 a (C.depthAt (n + j) - 1)⟩] <+:
      C.layerNAND.gates → C.depthAt (n + j) ≤ C.depth →
      C.layerNAND.depthAt (n + n + s.1.length) = C.depthAt (n + j) ∧ (C.IsNANDForm → ∀ x,
        (C.layerNAND.values (litInput x)).getD (n + n + s.1.length) false =
          (C.values x).getD (n + j) false) := by
    intro hp hD
    by_cases h5 : g.args = []
    · refine ⟨?_, fun hC x => ?_⟩
      · rw [C.layerNAND_depthAt_snoc hp, hδ, h5]; simp
      · rw [C.layerNAND_values_snoc hC hp, hval hC x, h5]; simp
    · have := hgate s.1 _ hp h5 (fun a ha => by have := (harg a ha).2; omega) (by omega)
      rwa [Nat.sub_add_cancel hδ1] at this
  have hbase_u : ∃ k', ∀ b ∈ (⟨.not, g.args.map fun a =>
      C.layerAt s.2 a (C.depthAt (n + j) - 1)⟩ : DAGGate).args, C.layerNAND.depthAt b = k' :=
    hbu _ (fun a ha => by have := (harg a ha).2; omega) (by omega)
  by_cases h4 : C.depth = C.depthAt (n + j)
  · rw [if_pos h4] at hpre ⊢
    refine ⟨fun _ k hk1 hk2 => ?_, fun g' hg' => ?_⟩
    · rw [hcol, show k - C.depthAt (n + j) = 0 by omega, List.getD_cons_zero,
        show k = C.depthAt (n + j) by omega]
      exact hbase hpre (by omega)
    · rcases List.mem_append.mp hg' with hg' | hg'
      · exact Or.inl hg'
      · rw [List.mem_singleton.mp hg']; exact Or.inr hbase_u
  -- Step 5: the parity twin `v@(δ + 1)` and the chain
  rw [if_neg h4] at hpre ⊢
  dsimp only at hpre ⊢
  have hp1 := ((List.prefix_append _ _).trans layerChain_isPrefix).trans hpre
  have hb := hbase hp1 (by omega)
  by_cases h5 : g.args = []
  · rw [if_pos h5] at hpre ⊢
    dsimp only at hpre ⊢
    have hp3 := layerChain_isPrefix.trans hpre
    have hp2 := (List.prefix_append _ [(⟨.not, [n + n + s.1.length + 1]⟩ : DAGGate)]).trans
      (by simpa using hp3)
    have hp2' : s.1 ++ [⟨.not, g.args.map fun a => C.layerAt s.2 a (C.depthAt (n + j) - 1)⟩] ++
        [⟨.not, [0, n]⟩] ++ [⟨.not, [n + n + s.1.length + 1]⟩] <+: C.layerNAND.gates := by
      simpa using hp3
    have e1 : n + n + (s.1 ++ [(⟨.not, g.args.map fun a =>
        C.layerAt s.2 a (C.depthAt (n + j) - 1)⟩ : DAGGate)]).length =
          n + n + s.1.length + 1 := by simp; omega
    have e2 : n + n + (s.1 ++ [(⟨.not, g.args.map fun a =>
        C.layerAt s.2 a (C.depthAt (n + j) - 1)⟩ : DAGGate)] ++ [⟨.not, [0, n]⟩]).length =
          n + n + s.1.length + 2 := by simp; omega
    have hδ' : C.depthAt (n + j) = 1 := by rw [hδ, h5]; simp
    have ht : C.layerNAND.depthAt (n + n + s.1.length + 2) = C.depthAt (n + j) + 1 ∧
        (C.IsNANDForm → ∀ x, (C.layerNAND.values (litInput x)).getD
          (n + n + s.1.length + 2) false = (C.values x).getD (n + j) false) := by
      have d1 := C.layerNAND_depthAt_snoc hp2
      have d2 := C.layerNAND_depthAt_snoc hp2'
      rw [e1] at d1
      rw [e2] at d2
      simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Nat.max_zero,
        C.layerNAND.depthAt_input (show 0 < n + n by omega),
        C.layerNAND.depthAt_input (show n < n + n by omega)] at d1 d2
      refine ⟨by omega, fun hC x => ?_⟩
      have v1 := C.layerNAND_values_snoc hC hp2 (litInput x)
      have v2 := C.layerNAND_values_snoc hC hp2' (litInput x)
      rw [e1] at v1
      rw [e2] at v2
      have hl := C.layerNAND_values_lit hn x
      rw [Nat.add_zero] at hl
      simp only [List.all_cons, List.all_nil, Bool.and_true, hl.1, hl.2] at v1 v2
      rw [v2, v1, hval hC x, h5]
      simp
    refine ⟨fun _ k hk1 hk2 => ?_, fun g' hg' => ?_⟩
    · rw [hcol]
      have := hchain hpre hb ht (k - C.depthAt (n + j)) (by omega)
      rwa [show C.depthAt (n + j) + (k - C.depthAt (n + j)) = k by omega] at this
    · rcases mem_layerChain_fst hg' with hg' | ⟨w, rfl⟩
      · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg'
        rcases hg' with (hg' | rfl) | rfl | rfl
        · exact Or.inl hg'
        · exact Or.inr hbase_u
        · refine Or.inr ⟨0, fun a ha => ?_⟩
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl
          · exact C.layerNAND.depthAt_input (by omega)
          · exact C.layerNAND.depthAt_input (by omega)
        · exact Or.inr (hsingle _)
      · exact Or.inr (hsingle w)
  · rw [if_neg h5] at hpre ⊢
    dsimp only at hpre ⊢
    have hp3 := layerChain_isPrefix.trans hpre
    have e1 : n + n + (s.1 ++ [(⟨.not, g.args.map fun a =>
        C.layerAt s.2 a (C.depthAt (n + j) - 1)⟩ : DAGGate)]).length =
          n + n + s.1.length + 1 := by simp; omega
    have ht := hgate _ (C.depthAt (n + j)) hp3 h5 (fun a ha => (harg a ha).2.le) (by omega)
    rw [e1] at ht
    refine ⟨fun _ k hk1 hk2 => ?_, fun g' hg' => ?_⟩
    · rw [hcol]
      have := hchain hpre hb ht (k - C.depthAt (n + j)) (by omega)
      rwa [show C.depthAt (n + j) + (k - C.depthAt (n + j)) = k by omega] at this
    · rcases mem_layerChain_fst hg' with hg' | ⟨w, rfl⟩
      · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg'
        rcases hg' with (hg' | rfl) | rfl
        · exact Or.inl hg'
        · exact Or.inr hbase_u
        · exact Or.inr (hbu _ (fun a ha => (harg a ha).2.le) (by omega))
      · exact Or.inr (hsingle w)

/-- The column fold, semantically, over the layering `C.layerNAND`: for
`s = (List.range v).foldl C.layerColumn ([], [])` with `v ≤ n + |C.gates|` and `s.1` a prefix
of the layering's gates, every copy `u@k` (`u < v`, `C.depthAt u ≤ k ≤ C.depth`) has depth `k`
and, under `C.IsNANDForm`, the value of `u` on every literal input; and every gate of `s.1`
reads vertices of one common depth.  Glue.

**Proof sketch.** Induction on `v` (`List.range_succ`, `List.foldl_append`): the step
`layerColumn_struct` appends one column and extends the gates, so earlier copies are unchanged
(`List.getD_append`), and `layerColumn_sem` gives the new column and gates. -/
private theorem DAGCircuit.layerFold_sem (v : ℕ) (hv : v ≤ n + C.gates.length)
    (hpre : ((List.range v).foldl C.layerColumn ([], [])).1 <+: C.layerNAND.gates) :
    (∀ u < v, C.depthAt u ≤ C.depth → ∀ k, C.depthAt u ≤ k → k ≤ C.depth →
      C.layerNAND.depthAt (C.layerAt ((List.range v).foldl C.layerColumn ([], [])).2 u k) = k ∧
      (C.IsNANDForm → ∀ x, (C.layerNAND.values (litInput x)).getD
        (C.layerAt ((List.range v).foldl C.layerColumn ([], [])).2 u k) false =
          (C.values x).getD u false)) ∧
    ∀ g ∈ ((List.range v).foldl C.layerColumn ([], [])).1, ∃ k, ∀ a ∈ g.args,
      C.layerNAND.depthAt a = k := by
  induction v with
  | zero => exact ⟨fun u hu => absurd hu (Nat.not_lt_zero u), fun g hg => by simp at hg⟩
  | succ v ih =>
    have hst := C.layerFold_struct v
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil] at hpre ⊢
    generalize (List.range v).foldl C.layerColumn ([], []) = s at ih hst hpre ⊢
    obtain ⟨h1, h2, h3, h4, -⟩ := hst
    obtain ⟨⟨col, hc, -⟩, hp, -, -, -⟩ := C.layerColumn_struct s v h2 h3 h4
    obtain ⟨ih1, ih2⟩ := ih (by omega) (hp.trans hpre)
    obtain ⟨hn1, hn2⟩ := C.layerColumn_sem s v (by omega) h1 hpre ih1
    refine ⟨fun u hu hud k hk1 hk2 => ?_, fun g hg => ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hu with hu | rfl
      · have hlat : C.layerAt (s.2 ++ [col]) u k = C.layerAt s.2 u k := by
          rw [layerAt_eq, layerAt_eq, List.getD_append _ _ _ _ (by omega)]
        rw [hc, hlat]
        exact ih1 u hu hud k hk1 hk2
      · exact hn1 hud k hk1 hk2
    · rcases hn2 g hg with hg | hg
      · exact ih2 g hg
      · exact hg
