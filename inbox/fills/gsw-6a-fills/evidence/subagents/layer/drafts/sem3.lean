/-- Under `C.IsNANDForm`, every gate of the layering is a NAND gate:
`C.IsNANDForm → ∀ g ∈ C.layerGates, g.IsNAND`.  Glue. -/
private theorem DAGCircuit.layerGates_isNAND (hC : C.IsNANDForm) :
    ∀ g ∈ C.layerGates, g.IsNAND := by
  have h := (C.layerFold_struct (n + C.gates.length)).2.2.2.1 hC
  rwa [← layerFold_eq, ← layerGates_eq] at h

/-- A list of naturals all of whose entries equal `k`, with an entry `y₀`, has `foldr max 0`
equal to `k`: `(∀ y ∈ l, y = k) → y₀ ∈ l → l.foldr max 0 = k`.  Glue. -/
private theorem foldr_max_eq_of_forall {l : List ℕ} {k y₀ : ℕ} (h : ∀ y ∈ l, y = k)
    (h₀ : y₀ ∈ l) : l.foldr max 0 = k := by
  induction l generalizing y₀ with
  | nil => exact absurd h₀ List.not_mem_nil
  | cons y l ih =>
    rw [List.foldr_cons, h y (by simp)]
    rcases l with _ | ⟨z, l⟩
    · simp
    · rw [ih (y₀ := z) (fun y hy => h y (List.mem_cons_of_mem _ hy)) (by simp), Nat.max_self]

/-- The depth of a gate `g` of the layering, read off a prefix `gs ++ [g]` of its gate list:
`gs ++ [g] <+: C.layerNAND.gates → C.layerNAND.depthAt (n + n + gs.length) =
1 + (g.args.map C.layerNAND.depthAt).foldr max 0`.  Glue. -/
private theorem DAGCircuit.layerNAND_depthAt_snoc {gs : List DAGGate} {g : DAGGate}
    (h : gs ++ [g] <+: C.layerNAND.gates) :
    C.layerNAND.depthAt (n + n + gs.length) =
      1 + (g.args.map C.layerNAND.depthAt).foldr max 0 := by
  have hi : gs.length < (gs ++ [g]).length := by simp
  have hd : (fun a => C.layerNAND.depths.getD a 0) = C.layerNAND.depthAt :=
    funext fun a => (C.layerNAND.depthAt_eq a).symm
  rw [C.layerNAND.depthAt_gate (lt_of_lt_of_le hi h.length_le), DAGGate.depth_eq,
    ← h.getElem hi, List.getElem_concat_length rfl, hd]

/-- The value of a gate `g` of the layering, read off a prefix `gs ++ [g]` of its gate list, when
`C.IsNANDForm`: `(C.layerNAND.values y).getD (n + n + gs.length) false =
!(g.args.all fun a => (C.layerNAND.values y).getD a false)`.  Glue. -/
private theorem DAGCircuit.layerNAND_values_snoc (hC : C.IsNANDForm) {gs : List DAGGate}
    {g : DAGGate} (h : gs ++ [g] <+: C.layerNAND.gates) (y : Fin (n + n) → Bool) :
    (C.layerNAND.values y).getD (n + n + gs.length) false =
      !(g.args.all fun a => (C.layerNAND.values y).getD a false) := by
  have hi : gs.length < (gs ++ [g]).length := by simp
  have hmem : g ∈ C.layerGates := by rw [← layerNAND_gates]; exact h.subset (by simp)
  rw [C.layerNAND.values_getD_gate y (lt_of_lt_of_le hi h.length_le), ← h.getElem hi,
    List.getElem_concat_length rfl, DAGGate.eval_of_isNAND (C.layerGates_isNAND hC g hmem)]

/-- A one-argument gate `NAND[w]` of the layering, read off a prefix `gs ++ [NAND[w]]`: vertex
`n + n + gs.length` has depth `C.layerNAND.depthAt w + 1` and, when `C.IsNANDForm`, value
`!(C.layerNAND.values y).getD w false`.  Glue. -/
private theorem DAGCircuit.layerNAND_single {gs : List DAGGate} {w : ℕ}
    (h : gs ++ [⟨.not, [w]⟩] <+: C.layerNAND.gates) :
    C.layerNAND.depthAt (n + n + gs.length) = C.layerNAND.depthAt w + 1 ∧
      (C.IsNANDForm → ∀ y, (C.layerNAND.values y).getD (n + n + gs.length) false =
        !(C.layerNAND.values y).getD w false) := by
  refine ⟨?_, fun hC y => ?_⟩
  · rw [C.layerNAND_depthAt_snoc h]; simp; omega
  · rw [C.layerNAND_values_snoc hC h]; simp

/-- The literal inputs of the layering, read as old values: for `u < n`, input vertex `u` holds
`(C.values x).getD u false` and input vertex `n + u` its negation, on `litInput x`.  Glue. -/
private theorem DAGCircuit.layerNAND_values_lit {u : ℕ} (hu : u < n) (x : Fin n → Bool) :
    (C.layerNAND.values (litInput x)).getD u false = (C.values x).getD u false ∧
    (C.layerNAND.values (litInput x)).getD (n + u) false = !(C.values x).getD u false := by
  have h0 := C.values_getD_input x ⟨u, hu⟩
  have h1 := C.layerNAND.values_getD_input (litInput x) (Fin.castAdd n ⟨u, hu⟩)
  have h2 := C.layerNAND.values_getD_input (litInput x) (Fin.natAdd n ⟨u, hu⟩)
  rw [litInput_castAdd] at h1
  rw [litInput_natAdd] at h2
  exact ⟨h1.trans h0.symm, h2.trans (congrArg (!·) h0.symm)⟩

/-- The double-NAND chain realizes a column: for a vertex predicate `P` (vertex, level) that
every link `NAND(NAND(a))` (two consecutive gates of `G` after `gs`) lifts two levels, if the
chain's gates are a prefix of `G`, `P a L` and `P b (L + 1)`, then
`P ((a :: b :: (layerChain N gs a b s).2).getD j 0) (L + j)` for every `j ≤ s + 1`.  Glue. -/
private theorem layerChain_col {G : List DAGGate} {N : ℕ} {P : ℕ → ℕ → Prop}
    (hstep : ∀ (gs : List DAGGate) (a L : ℕ),
      gs ++ [⟨.not, [a]⟩, ⟨.not, [N + gs.length]⟩] <+: G → P a L →
        P (N + gs.length + 1) (L + 2)) :
    ∀ {s : ℕ} {gs : List DAGGate} {a b L : ℕ}, (layerChain N gs a b s).1 <+: G → P a L →
      P b (L + 1) → ∀ j ≤ s + 1, P ((a :: b :: (layerChain N gs a b s).2).getD j 0) (L + j)
  | 0, gs, a, b, L, _, ha, hb, j, hj => by
    rw [layerChain_zero]
    rcases j with _ | _ | j
    exacts [ha, hb, by omega]
  | s + 1, gs, a, b, L, hpre, ha, hb, j, hj => by
    rw [layerChain_succ] at hpre ⊢
    have key := layerChain_col hstep hpre hb (hstep gs a L (layerChain_isPrefix.trans hpre) ha)
    rcases j with _ | j
    · exact ha
    · rw [List.getD_cons_succ, show L + (j + 1) = L + 1 + j by omega]
      exact key j (by omega)

/-- One link of the chain over the layering keeps the column invariant of an old vertex `u`:
if `gs ++ [NAND[a], NAND[n + n + |gs|]]` is a prefix of the layering's gates and `a` has depth
`L` (and, under `C.IsNANDForm`, the value of `u` on every literal input), then the outer vertex
`n + n + |gs| + 1` has depth `L + 2` (and the value of `u`).  Glue. -/
private theorem DAGCircuit.layerNAND_link (u : ℕ) {gs : List DAGGate} {a L : ℕ}
    (hp : gs ++ [⟨.not, [a]⟩, ⟨.not, [n + n + gs.length]⟩] <+: C.layerNAND.gates)
    (ha : C.layerNAND.depthAt a = L ∧ (C.IsNANDForm → ∀ x,
      (C.layerNAND.values (litInput x)).getD a false = (C.values x).getD u false)) :
    C.layerNAND.depthAt (n + n + gs.length + 1) = L + 2 ∧ (C.IsNANDForm → ∀ x,
      (C.layerNAND.values (litInput x)).getD (n + n + gs.length + 1) false =
        (C.values x).getD u false) := by
  have hp2 : gs ++ [⟨.not, [a]⟩] ++ [⟨.not, [n + n + gs.length]⟩] <+: C.layerNAND.gates := by
    simpa using hp
  obtain ⟨d1, v1⟩ := C.layerNAND_single ((List.prefix_append _ _).trans hp2)
  obtain ⟨d2, v2⟩ := C.layerNAND_single hp2
  have hl : n + n + (gs ++ [(⟨.not, [a]⟩ : DAGGate)]).length = n + n + gs.length + 1 := by
    simp; omega
  rw [hl] at d2 v2
  exact ⟨by omega, fun hC x => by rw [v2 hC, v1 hC, Bool.not_not]; exact ha.2 hC x⟩

/-- One fold step, semantically, over the layering `C.layerNAND` (whose gates extend those of
the step, `hpre`): if every recorded copy `u@k` of an earlier live vertex `u < v` has depth `k`
and, under `C.IsNANDForm`, the value of `u` on every literal input, then so has every copy
`v@k` of the new column, for `C.depthAt v ≤ k ≤ C.depth`; and every new gate reads vertices of
one common depth.  Glue.

**Proof sketch.** Case split along `layerColumn_eq`, the copies of `v` read off with
`layerAt_eq` and `List.getD_append_right`.  Step 1: a column `a :: b :: chain` after new gates
`pre`, by `layerChain_col` with `layerNAND_link`.  Step 2: an input `v` (`depthAt_input`) is
`v@0`, and its twin `NAND[n + v]` has depth `1` and value `!!xᵥ` (`layerNAND_single`,
`layerNAND_values_lit`).  Step 3: a gate `v = n + j` of depth `δ` reads earlier, shallower
vertices (`depthAt_gate`, `DAGGate.depth_eq`, `C.args_lt`, `DAGGate.getD_lt_depth`) and is a
NAND of their values (`values_getD_gate`, `DAGGate.eval_of_isNAND`).  Step 4: a NAND gate over
copies at one level `k` has depth `k + 1` (`foldr_max_eq_of_forall`) and the gate's value
(`all_congr_mem`); this gives the base `v@δ` (level `δ - 1`; a fan-in-0 base has depth
`1 = δ`) and the twin (level `δ`).  Step 5: a fan-in-0 twin `NAND(NAND(x₀, ¬x₀))` has depth `2`
and value `false`. -/
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
  let P : ℕ → ℕ → Prop := fun w k => C.layerNAND.depthAt w = k ∧ (C.IsNANDForm → ∀ x,
    (C.layerNAND.values (litInput x)).getD w false = (C.values x).getD v false)
  have hcol : ∀ (col : List ℕ) (k : ℕ),
      C.layerAt (s.2 ++ [col]) v k = col.getD (k - C.depthAt v) 0 := fun col k => by
    rw [layerAt_eq, List.getD_append_right _ _ _ _ hlen.le, hlen, Nat.sub_self,
      List.getD_cons_zero]
  have hU : ∀ w : ℕ, ∃ k, ∀ a ∈ (⟨.not, [w]⟩ : DAGGate).args, C.layerNAND.depthAt a = k :=
    fun w => ⟨_, fun a ha => by rw [List.mem_singleton.mp ha]⟩
  -- Step 1: a column `a :: b :: chain` after the new gates `pre`
  have hfin : ∀ (pre : List DAGGate) (a b t : ℕ), (layerChain (n + n) (s.1 ++ pre) a b t).1 <+:
      C.layerNAND.gates → P a (C.depthAt v) → P b (C.depthAt v + 1) →
      (∀ g ∈ pre, ∃ k, ∀ a ∈ g.args, C.layerNAND.depthAt a = k) →
      C.depth = C.depthAt v + t + 1 →
      (C.depthAt v ≤ C.depth → ∀ k, C.depthAt v ≤ k → k ≤ C.depth →
        P (C.layerAt (s.2 ++ [a :: b :: (layerChain (n + n) (s.1 ++ pre) a b t).2]) v k) k) ∧
      ∀ g ∈ (layerChain (n + n) (s.1 ++ pre) a b t).1, g ∈ s.1 ∨
        ∃ k, ∀ a ∈ g.args, C.layerNAND.depthAt a = k := by
    intro pre a b t hp ha hb hpre ht
    refine ⟨fun _ k hk1 hk2 => ?_, fun g hg => ?_⟩
    · rw [hcol]
      have := layerChain_col (P := P) (fun _ _ _ hp ha => C.layerNAND_link v hp ha) hp ha hb
        (k - C.depthAt v) (by omega)
      rwa [Nat.add_sub_of_le hk1] at this
    · rcases mem_layerChain_fst hg with hg | ⟨w, rfl⟩
      · rcases List.mem_append.mp hg with hg | hg
        exacts [Or.inl hg, Or.inr (hpre g hg)]
      · exact Or.inr (hU w)
  rw [layerColumn_eq] at hpre ⊢
  by_cases h1 : C.depth < C.depthAt v
  · rw [if_pos h1]
    exact ⟨fun h => absurd h (by omega), fun g hg => Or.inl hg⟩
  rw [if_neg h1] at hpre ⊢
  by_cases h2 : v < n
  · -- Step 2: an input vertex
    rw [if_pos h2] at hpre ⊢
    have hv0 : P v (C.depthAt v) := ⟨by rw [C.depthAt_input h2]; exact
      C.layerNAND.depthAt_input (by omega), fun _ x => (C.layerNAND_values_lit h2 x).1⟩
    by_cases h3 : C.depth = 0
    · rw [if_pos h3]
      refine ⟨fun _ k hk1 hk2 => ?_, fun g hg => Or.inl hg⟩
      rw [hcol, show k - C.depthAt v = 0 by omega, List.getD_cons_zero,
        show k = C.depthAt v by omega]
      exact hv0
    rw [if_neg h3] at hpre ⊢
    obtain ⟨d1, v1⟩ := C.layerNAND_single (layerChain_isPrefix.trans hpre)
    exact hfin _ _ _ _ hpre hv0 ⟨by rw [d1, C.layerNAND.depthAt_input (by omega),
      C.depthAt_input h2], fun hC x => by
        rw [v1 hC, (C.layerNAND_values_lit h2 x).2, Bool.not_not]⟩
      (fun g hg => by rw [List.mem_singleton.mp hg]; exact hU _)
      (by rw [C.depthAt_input h2]; omega)
  -- Step 3: a gate vertex `v = n + j`: its depth, arguments and value
  rw [if_neg h2] at hpre ⊢
  obtain ⟨j, rfl⟩ : ∃ j, v = n + j := ⟨v - n, by omega⟩
  have hj : j < C.gates.length := by omega
  rw [show n + j - n = j by omega, List.getD_eq_getElem _ _ hj] at hpre ⊢
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
  -- Step 4: a NAND gate over the copies at one level `k` of the arguments
  have hlev : ∀ k, (∀ a ∈ g.args, C.depthAt a ≤ k) → k ≤ C.depth → ∀ a ∈ g.args,
      P (C.layerAt s.2 a k) k ∧ C.layerNAND.depthAt (C.layerAt s.2 a k) = k := fun k hk hkD a ha =>
    have h := hsem a (harg a ha).1 (le_trans (hk a ha) hkD) k (hk a ha) hkD
    ⟨⟨h.1, h.2⟩, h.1⟩
  have hgate : ∀ (gs : List DAGGate) (k : ℕ),
      gs ++ [⟨.not, g.args.map fun a => C.layerAt s.2 a k⟩] <+: C.layerNAND.gates →
      g.args ≠ [] → (∀ a ∈ g.args, C.depthAt a ≤ k) → k ≤ C.depth →
      C.layerNAND.depthAt (n + n + gs.length) = k + 1 ∧ (C.IsNANDForm → ∀ x,
        (C.layerNAND.values (litInput x)).getD (n + n + gs.length) false =
          (C.values x).getD (n + j) false) := by
    intro gs k hp hne hk hkD
    refine ⟨?_, fun hC x => ?_⟩
    · obtain ⟨a₀, ha₀⟩ := List.exists_mem_of_ne_nil _ hne
      rw [C.layerNAND_depthAt_snoc hp, List.map_map,
        foldr_max_eq_of_forall (k := k) (fun y hy => ?_) (List.mem_map_of_mem ha₀)]
      · omega
      · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hy
        exact (hlev k hk hkD a ha).2
    · rw [C.layerNAND_values_snoc hC hp, List.all_map, hval hC x]
      exact congrArg (!·) (all_congr_mem fun a ha => (hlev k hk hkD a ha).1.2 hC x)
  have hbu : ∀ k, (∀ a ∈ g.args, C.depthAt a ≤ k) → k ≤ C.depth →
      ∃ k', ∀ b ∈ (⟨.not, g.args.map fun a => C.layerAt s.2 a k⟩ : DAGGate).args,
        C.layerNAND.depthAt b = k' := fun k hk hkD => ⟨k, fun b hb => by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
    exact (hlev k hk hkD a ha).2⟩
  have hδ1 : 1 ≤ C.depthAt (n + j) := by omega
  have hk1 : ∀ a ∈ g.args, C.depthAt a ≤ C.depthAt (n + j) - 1 := fun a ha => by
    have := (harg a ha).2; omega
  set b0 : DAGGate := ⟨.not, g.args.map fun a => C.layerAt s.2 a (C.depthAt (n + j) - 1)⟩
    with hb0
  have hbase : s.1 ++ [b0] <+: C.layerNAND.gates → C.depthAt (n + j) ≤ C.depth →
      P (n + n + s.1.length) (C.depthAt (n + j)) := by
    intro hp hD
    by_cases h5 : g.args = []
    · refine ⟨?_, fun hC x => ?_⟩
      · rw [C.layerNAND_depthAt_snoc hp, hδ, hb0, h5]; simp
      · rw [C.layerNAND_values_snoc hC hp, hval hC x, hb0, h5]; simp
    · have := hgate s.1 _ hp h5 hk1 (by omega)
      rwa [Nat.sub_add_cancel hδ1] at this
  by_cases h4 : C.depth = C.depthAt (n + j)
  · rw [if_pos h4] at hpre ⊢
    refine ⟨fun _ k hk1 hk2 => ?_, fun g' hg' => ?_⟩
    · rw [hcol, show k - C.depthAt (n + j) = 0 by omega, List.getD_cons_zero,
        show k = C.depthAt (n + j) by omega]
      exact hbase hpre (by omega)
    · rcases List.mem_append.mp hg' with hg' | hg'
      exacts [Or.inl hg', Or.inr ((List.mem_singleton.mp hg') ▸ hbu _ hk1 (by omega))]
  -- Step 5: the parity twin `v@(δ + 1)`, then the chain
  rw [if_neg h4] at hpre ⊢
  dsimp only at hpre ⊢
  by_cases h5 : g.args = []
  · rw [if_pos h5] at hpre ⊢
    dsimp only at hpre ⊢
    have hp' : s.1 ++ [b0] ++ [⟨.not, [0, n]⟩] ++ [⟨.not, [n + n + s.1.length + 1]⟩] <+:
        C.layerNAND.gates := by rw [List.append_assoc _ [_]]; exact layerChain_isPrefix.trans hpre
    have hp1 := (List.prefix_append _ _).trans hp'
    have e1 : (s.1 ++ [b0]).length = s.1.length + 1 := by simp
    have d1 := C.layerNAND_depthAt_snoc hp1
    obtain ⟨d2, v2⟩ := C.layerNAND_single hp'
    simp only [e1, List.length_append, List.length_cons, List.length_nil, List.map_cons,
      List.map_nil, List.foldr_cons, List.foldr_nil, Nat.max_zero,
      C.layerNAND.depthAt_input (show 0 < n + n by omega),
      C.layerNAND.depthAt_input (show n < n + n by omega)] at d1 d2 v2
    have ht : P (n + n + s.1.length + 2) (C.depthAt (n + j) + 1) := by
      refine ⟨by rw [hδ, h5]; simp; omega, fun hC x => ?_⟩
      have v1 := C.layerNAND_values_snoc hC hp1 (litInput x)
      have hl := C.layerNAND_values_lit hn x
      rw [Nat.add_zero] at hl
      simp only [e1, List.all_cons, List.all_nil, Bool.and_true, hl.1, hl.2] at v1
      rw [show n + n + s.1.length + 2 = n + n + (s.1.length + 1 + 1) by omega, v2 hC, ← add_assoc,
        v1, hval hC x, h5]
      simp
    rw [List.append_assoc] at hpre ⊢
    exact hfin _ _ _ _ hpre (hbase ((List.prefix_append _ _).trans hp1) (by omega)) ht
      (fun g' hg' => by
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg'
        rcases hg' with rfl | rfl | rfl
        exacts [hbu _ hk1 (by omega), ⟨0, fun a ha => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl <;> exact C.layerNAND.depthAt_input (by omega)⟩, hU _])
      (by omega)
  · rw [if_neg h5] at hpre ⊢
    dsimp only at hpre ⊢
    have hp' := layerChain_isPrefix.trans hpre
    have ht := hgate _ (C.depthAt (n + j)) hp' h5 (fun a ha => (harg a ha).2.le) (by omega)
    rw [show (s.1 ++ [b0]).length = s.1.length + 1 by simp, ← add_assoc] at ht
    rw [List.append_assoc] at hpre ⊢
    exact hfin _ _ _ _ hpre (hbase ((List.prefix_append _ _).trans hp') (by omega)) ht
      (fun g' hg' => by
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg'
        rcases hg' with rfl | rfl
        exacts [hbu _ hk1 (by omega), hbu _ (fun a ha => (harg a ha).2.le) (by omega)])
      (by omega)

/-- The column fold, semantically, over the layering `C.layerNAND`: for
`s = (List.range v).foldl C.layerColumn ([], [])` with `v ≤ n + |C.gates|` and `s.1` a prefix
of the layering's gates, every copy `u@k` (`u < v`, `C.depthAt u ≤ k ≤ C.depth`) has depth `k`
and, under `C.IsNANDForm`, the value of `u` on every literal input; and every gate of `s.1`
reads vertices of one common depth.  Glue (induction on `v` with `List.range_succ`,
`layerColumn_struct` for the shape of a step, `List.getD_append` for the earlier copies, and
`layerColumn_sem`). -/
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
    refine ⟨fun u hu hud k hk1 hk2 => ?_, fun g hg => (hn2 g hg).elim (ih2 g) id⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hu with hu | rfl
    · rw [hc, layerAt_eq, List.getD_append _ _ _ _ (by omega), ← layerAt_eq]
      exact ih1 u hu hud k hk1 hk2
    · exact hn1 hud k hk1 hk2

