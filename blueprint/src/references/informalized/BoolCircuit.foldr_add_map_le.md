<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Circuit.lean :: foldr_add_map_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Summing fold of a map is bounded by a constant multiple

**Claim.** Let `h : α → β`, `f : α → Nat`, `g : β → Nat`, `cs : List α` and
`k : Nat`. If `g (h c) ≤ k * f c` for every `c ∈ cs`, then the bound survives
summation:

`(cs.map h).foldr (fun c acc => g c + acc) 0 ≤ k * cs.foldr (fun c acc => f c + acc) 0`.

The inequality version of `foldr_add_map`: a uniform per-element blowup factor
`k` becomes the same factor on the totals.

**Proof.** By list induction, `induction' cs with c cs ih`.

1. Nil case: the goal is `0 ≤ k * 0`, closed by `simp +decide`.
2. Cons case: `simp +zetaDelta at *` unfolds `List.map`/`List.foldr` on both
   sides, splitting `heq` into its head part `heq.1 : g (h c) ≤ k * f c` and its
   tail part `heq.2`. Then `linarith [ih heq.2]` adds the head bound to the
   inductive bound for the tail and distributes `k` over the sum.

**Used in.** `toNAnd_toNOr_size_le` — the only one of the four `foldr_*` helpers
that is actually invoked, at the `NOrCircuit.size` branch via
`convert foldr_add_map_le _ using 1` with `k = 2`, turning the child-wise bound
`c.toNAnd.size ≤ 2 * c.size` into a bound on the summed sizes of the children.
