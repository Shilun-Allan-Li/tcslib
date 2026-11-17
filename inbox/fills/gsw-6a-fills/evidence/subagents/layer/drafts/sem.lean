/-- Under `C.IsNANDForm`, every gate of the layering is a NAND gate:
`C.IsNANDForm → ∀ g ∈ C.layerGates, g.IsNAND`.  Glue. -/
private theorem DAGCircuit.layerGates_isNAND (hC : C.IsNANDForm) :
    ∀ g ∈ C.layerGates, g.IsNAND := by
  have h := (C.layerFold_struct (n + C.gates.length)).2.2.2.1 hC
  rwa [← layerFold_eq, ← layerGates_eq] at h

/-- A list of naturals all of whose entries equal `k`, with an entry `y₀`, has `foldr max 0`
equal to `k`: `(∀ y ∈ l, y = k) → y₀ ∈ l → l.foldr max 0 = k`.  Glue. -/
private theorem foldr_max_eq_of_forall {l : List ℕ} {k y₀ : ℕ} (h : ∀ y ∈ l, y = k)
    (h₀ : y₀ ∈ l) : l.foldr max 0 = k :=
  le_antisymm (List.max_le_of_forall_le l k fun y hy => (h y hy).le)
    (List.le_max_of_le h₀ (h y₀ h₀).ge)

/-- The depth of a gate `g` of the layering, read off a prefix `gs ++ [g]` of its gate list:
`gs ++ [g] <+: C.layerNAND.gates → C.layerNAND.depthAt (n + n + gs.length) =
1 + (g.args.map C.layerNAND.depthAt).foldr max 0`.  Glue. -/
private theorem DAGCircuit.layerNAND_depthAt_snoc {gs : List DAGGate} {g : DAGGate}
    (h : gs ++ [g] <+: C.layerNAND.gates) :
    C.layerNAND.depthAt (n + n + gs.length) =
      1 + (g.args.map C.layerNAND.depthAt).foldr max 0 := by
  have hi : gs.length < (gs ++ [g]).length := by simp
  have hg : (gs ++ [g])[gs.length]'hi = g := by simp
  rw [C.layerNAND.depthAt_gate (lt_of_lt_of_le hi h.length_le), DAGGate.depth_eq,
    ← h.getElem hi, hg]
  congr 2
  exact List.map_congr_left fun a _ => (C.layerNAND.depthAt_eq a).symm

/-- The value of a gate `g` of the layering, read off a prefix `gs ++ [g]` of its gate list, when
`C.IsNANDForm`: `(C.layerNAND.values y).getD (n + n + gs.length) false =
!(g.args.all fun a => (C.layerNAND.values y).getD a false)`.  Glue. -/
private theorem DAGCircuit.layerNAND_values_snoc (hC : C.IsNANDForm) {gs : List DAGGate}
    {g : DAGGate} (h : gs ++ [g] <+: C.layerNAND.gates) (y : Fin (n + n) → Bool) :
    (C.layerNAND.values y).getD (n + n + gs.length) false =
      !(g.args.all fun a => (C.layerNAND.values y).getD a false) := by
  have hi : gs.length < (gs ++ [g]).length := by simp
  have hg : (gs ++ [g])[gs.length]'hi = g := by simp
  have hmem : g ∈ C.layerGates := by
    rw [← layerNAND_gates]; exact h.subset (by simp)
  rw [C.layerNAND.values_getD_gate y (lt_of_lt_of_le hi h.length_le), ← h.getElem hi, hg,
    DAGGate.eval_of_isNAND (C.layerGates_isNAND hC g hmem)]

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
    · exact ha
    · exact hb
    · omega
  | s + 1, gs, a, b, L, hpre, ha, hb, j, hj => by
    rw [layerChain_succ] at hpre ⊢
    have hc := hstep gs a L ((List.prefix_append _ _).trans (layerChain_isPrefix.trans hpre)) ha
    have key := layerChain_col hstep hpre hb hc
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
  have hp1 : gs ++ [⟨.not, [a]⟩] <+: C.layerNAND.gates := (List.prefix_append _ _).trans hp2
  have hl : n + n + (gs ++ [(⟨.not, [a]⟩ : DAGGate)]).length = n + n + gs.length + 1 := by
    simp; omega
  have d1 := C.layerNAND_depthAt_snoc hp1
  have d2 := C.layerNAND_depthAt_snoc hp2
  rw [hl] at d2
  simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Nat.max_zero] at d1 d2
  refine ⟨by omega, fun hC x => ?_⟩
  have v1 := C.layerNAND_values_snoc hC hp1 (litInput x)
  have v2 := C.layerNAND_values_snoc hC hp2 (litInput x)
  rw [hl] at v2
  simp only [List.all_cons, List.all_nil, Bool.and_true] at v1 v2
  rw [v2, v1, Bool.not_not]
  exact ha.2 hC x
