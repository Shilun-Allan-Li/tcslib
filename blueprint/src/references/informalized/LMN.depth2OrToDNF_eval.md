<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitHelpers.lean :: depth2OrToDNF_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# depth2OrToDNF computes the same function as the circuit

**Claim.** Let `cs : List (Circuit n)` with `(Circuit.node false cs).depth ≤ 2`
(an OR gate on top). Then for every input `x`,
`(depth2OrToDNF cs).eval x = (Circuit.node false cs).eval x`.

**Proof.** In two moves.

1. **Per child.** `h_child_eval`: for `c ∈ cs`, `(depth2OrToDNF [c]).eval x = c.eval x`.
   By `rcases` on `c`:
   - `c = .lit l`: the contribution is `[[l.toLiteral]]`, and
     `DNF.eval`/`Term.eval`/`Literal.eval` unfold to `l.eval x` after
     `simp [Lit.toLiteral]` (the sign flip `neg = !sign` is absorbed).
   - `c = .node true cs'` (AND child): `depth_le_two_children_depth_le_one` gives
     `c.depth ≤ 1`, then `depth_le_one_children_are_lits` says every element of
     `cs'` is a literal, so the `filterMap` drops nothing. An auxiliary list
     induction identifies `Term.eval` of the collected literals with
     `cs'.foldr (fun c acc => c.eval x && acc) true`, i.e. `Circuit.eval`.
   - `c = .node false cs'` (OR child): same two depth lemmas; here the
     contribution is one singleton term per literal child, and the induction
     matches `DNF.eval` against the OR-`foldr`.
2. **Splitting the top OR.** `h_depth2OrToDNF`: `depth2OrToDNF cs = cs.flatMap (fun c => depth2OrToDNF [c])`
   (`unfold; aesop`). With `h_foldr` rewriting `foldr (· || ·) false` as
   `decide (∃ c ∈ cs, c.eval x = true)`, both sides become "some child is
   satisfied", and `grind` finishes. ∎

**Used in.** `depth2_circuit_switching_bound` in
`LMN/CircuitLayerReduction.lean`, which replaces an OR-top depth-2 circuit by
this DNF before invoking `switching_bernoulli_dtDepth_dnf_general`.
