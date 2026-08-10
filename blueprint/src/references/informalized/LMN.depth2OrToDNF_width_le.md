<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitHelpers.lean :: depth2OrToDNF_width_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# depth2OrToDNF has width at most the circuit's max fanin

**Claim.** For `cs : List (Circuit n)` with `(Circuit.node false cs).depth ≤ 2`,
`(depth2OrToDNF cs).width ≤ (Circuit.node false cs).maxFanin`, where
`DNF.width` is the maximum term length and
`Circuit.maxFanin (.node _ cs) = max cs.length (cs.foldr (fun c acc => max c.maxFanin acc) 0)`.

**Proof.** Bound each term, then take the max.

1. **Per child.** For `c ∈ cs`, the length of every term `c` contributes is at
   most `(Circuit.node false cs).maxFanin`: `1` if `c = .lit l`, `cs'.length` if
   `c = .node true cs'`, and `1` per contributed singleton if `c = .node false cs'`.
   The AND case uses `h_c_maxFanin : c.maxFanin ≤ (Circuit.node false cs).maxFanin`
   (a `foldr max` membership induction closed by `aesop`, then
   `Circuit.maxFanin`-unfolding); the two `1`-cases use
   `List.length_pos_iff` on `cs`, which is nonempty because `c ∈ cs`.
2. **Transfer to the flatMap.** `grind +qlia` lifts the per-child bound to every
   `t ∈ depth2OrToDNF cs` in its unfolded `List.flatMap` form.
3. **Max.** `h_max_width` (`foldr max 0` of a list all of whose entries are
   `≤ B` is `≤ B`, list induction + `aesop`) plus `List.mem_map` on
   `DNF.width = (·.map Term.width).foldr max 0` gives the claim. ∎

**Remark.** The depth hypothesis `hd` is never used in the proof body: the term
lengths produced by `depth2OrToDNF` are bounded by fanin regardless of depth. It
is kept for signature uniformity with `depth2OrToDNF_eval`, which does need it.

**Used in.** `depth2_circuit_switching_bound`
(`LMN/CircuitLayerReduction.lean`), chained by `le_trans` with the circuit's
`maxFanin ≤ w` to supply the width hypothesis of
`switching_bernoulli_dtDepth_dnf_general`.
