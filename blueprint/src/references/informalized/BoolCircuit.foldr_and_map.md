<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Circuit.lean :: foldr_and_map -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Conjunctive fold commutes with a pointwise-agreeing map

**Claim.** Let `h : α → β`, `f : α → Bool`, `g : β → Bool`, and `cs : List α`.
If `g (h c) = f c` for every `c ∈ cs`, then folding `&&` with `g` over the mapped
list gives the same Boolean as folding `&&` with `f` over the original:

`(cs.map h).foldr (fun c acc => g c && acc) true = cs.foldr (fun c acc => f c && acc) true`.

Note the hypothesis is only required *on members of* `cs`, not for all of `α`.

**Proof.** `induction cs <;> aesop`. The nil case is `true = true`; in the cons
case `List.map` and `List.foldr` unfold to `g (h c) && …` versus `f c && …`, the
head is rewritten by `heq` at `c` and the tails are handled by the inductive
hypothesis (restricted to the tail membership).

**Remark.** This is a deliberately granular `private` bookkeeping helper for the
AND-gate case of the `Circuit → NAndCircuit`/`NOrCircuit` normalization proofs,
where semantics preservation on children is exactly a hypothesis of the form
`∀ c ∈ cs, (h c).eval x = c.eval x`.

**Used in.** Nothing — it is currently dead code. `toNAnd_toNOr_eval` reproves
the same fact inline with `induction cs <;> aesop`, and since the lemma is
`private` no other file can reach it.
