<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitHelpers.lean :: dedupTermVar_width_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# De-duplication does not increase the length of a term

**Claim.** `(dedupTermVar t).length ≤ t.length` for every `t : Term n`.

**Proof.** The `foldr` only ever keeps or drops the head, so its output grows
by at most one per input literal.

1. Prove the accumulator-generalised bound
   `(t.foldr (fun l acc => if acc.any (·.var = l.var) then acc else l :: acc) acc).length ≤ t.length + acc.length`
   by `induction' t ... generalizing acc`: the `nil` case is
   `simp +arith +decide`, the `cons` case `grind` (either the length is
   unchanged, or it goes up by exactly one while `t.length` also does).
2. `convert` that bound at `acc = []` with the goal, since
   `t.length + 0 = t.length`.

**Used in.** `cleanDNF_width_le` and `cleanCNF_width_le`, which need that
cleaning a formula cannot raise its width — the width bound is what the
switching lemma consumes.
