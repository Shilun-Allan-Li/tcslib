<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ArrowTheorem.lean :: acyclic -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Acyclicity: no Condorcet cycle on any profile

**Definition.** For `f : BooleanFunc n`, `acyclic f` says that for every profile
`p : Profile n`,

`¬ (f (abVotes p) = 1 ∧ f (bcVotes p) = 1 ∧ f (caVotes p) = 1)` and
`¬ (f (abVotes p) = -1 ∧ f (bcVotes p) = -1 ∧ f (caVotes p) = -1)`.

Applying `f` to the three pairwise vote vectors of one profile gives society's
three verdicts. The first clause forbids `a > b`, `b > c`, `c > a`; the second
forbids the reverse cycle `b > a`, `c > b`, `a > c`. Everything else is allowed,
so exactly 2 of the 8 sign patterns are banned. A `Prop`-valued definition; no
proof.

**Remark.** This is the file's substitute for the usual "society's aggregate is
always a transitive ordering / there is always a Condorcet winner" hypothesis —
stated directly on profiles rather than via a probability identity. Because
individual orderings are transitive by construction (they are drawn from the six
orderings tabulated by `abPref`, `bcPref`, `caPref`), any cycle would be an
artifact of the aggregation rule `f`, which is what is being excluded.

The reason the ban on just 2 of 8 patterns has so much force: for a `±1` triple
`(x, y, z)`, `x*y + y*z + x*z` equals `3` when all three agree and `-1`
otherwise. Ruling out the two all-agree patterns therefore pins the sum to `-1`
*pointwise*, on every profile — no averaging slack.

**Used in.** A hypothesis of `acyclic_implies_corrFunc`, which destructures it
per profile (`obtain ⟨hcyc1, hcyc2⟩ := hacyc p`) and uses the two clauses to kill
2 of the 8 branches of a triple `rcases` on `isPmOne f`, the other 6 branches
closing by `norm_num` at `-1`. Averaging that over the `6^n` profiles gives
`3 * corrFunc f = -1`. Also a hypothesis of the top-level `arrow_theorem`.
