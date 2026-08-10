<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Circuit.lean :: foldr_or_map -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Disjunctive fold commutes with a pointwise-agreeing map

**Claim.** Let `h : α → β`, `f : α → Bool`, `g : β → Bool`, and `cs : List α`.
If `g (h c) = f c` for every `c ∈ cs`, then

`(cs.map h).foldr (fun c acc => g c || acc) false = cs.foldr (fun c acc => f c || acc) false`.

This is the `||`/`false` twin of `foldr_and_map`; again the hypothesis is only
needed on members of `cs`.

**Proof.** `induction cs <;> aesop`. Nil gives `false = false`; cons unfolds
`List.map`/`List.foldr` to `g (h c) || …` versus `f c || …`, rewrites the head by
`heq` and closes the tails by the inductive hypothesis.

**Remark.** A `private` bookkeeping helper aimed at the OR-gate case of the
normalization proofs, where the child-wise hypothesis has the shape
`∀ c ∈ cs, (h c).eval x = c.eval x`.

**Used in.** Nothing — currently dead code, like `foldr_and_map`:
`toNAnd_toNOr_eval` discharges the OR case with its own inline
`induction cs <;> aesop`, and `private` makes the lemma unreachable elsewhere.
