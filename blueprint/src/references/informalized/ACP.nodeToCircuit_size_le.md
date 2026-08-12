<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/FeedForwardCircuit.lean :: nodeToCircuit_size_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Tree-unrolling costs at most `(k + 1) ^ m` nodes

**Claim.** If every gate of `F : FeedForward Bool (Fin n) out` has fan-in at most `k`, i.e.
`hk : ∀ d v, Fintype.card (F.gates d v).op.ι ≤ k`, then for every layer `m` and node
`v : F.nodes ⟨m, hm⟩` the unrolled tree satisfies
`(nodeToCircuit F isAnd gfin m hm v).size ≤ (k + 1) ^ m`.
Here `Circuit.size` counts gate nodes plus literal leaves.

**Proof.** `revert hm v; induction' m with m ih`.

* `m = 0`: `unfold nodeToCircuit; simp +decide [Circuit.size]` — the unrolling is a single
  literal, of size `1 = (k + 1) ^ 0`.
* `m + 1`: three steps.
  1. `h_node` computes the size at layer `m + 1` as
     `1 + (children.map size).foldr (· + ·) 0`, by `unfold nodeToCircuit` and
     `simp +decide [Nat.recAux]`, then `unfold Circuit.size` with
     `simp +decide [List.foldr_map]` and two `congr!` steps closed by `Circuit.size.eq_def`.
  2. `h_foldr` is a generic list fact: if every entry of `L : List ℕ` is at most
     `(k + 1) ^ m`, then `L.foldr (· + ·) 0 ≤ L.length * (k + 1) ^ m`. Proved by
     `induction L <;> simp_all +decide [Nat.succ_mul]` and `grind`.
  3. Applying `h_foldr` to the list of child sizes (each bounded by `ih`) gives
     `size ≤ 1 + (fan-in) * (k + 1) ^ m`; `simp_all +decide [pow_succ']` plus
     `nlinarith [hk ⟨m, _⟩ v, pow_pos (Nat.succ_pos k) m]` turns the fan-in bound `≤ k`
     into `1 + k * (k + 1) ^ m ≤ (k + 1) ^ (m + 1)`.

**Remark.** The list length here is the number of enumerated input wires, which is exactly
`Fintype.card (F.gates ⟨m, _⟩ v).op.ι`; the extra `+ 1` in the base of the power absorbs
the gate node itself.

**Used in.** `ACP.FeedForward.toCircuit_size_le`, at `m = F.depth`.
