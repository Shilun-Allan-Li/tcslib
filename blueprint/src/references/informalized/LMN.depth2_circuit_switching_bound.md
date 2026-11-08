<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitLayerReduction.lean :: LMN.depth2_circuit_switching_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Switching bound for depth-two circuits

**Claim.** A Boolean function computed by a circuit of depth at most $2$, size at most $s$, and maximum fan-in at most $w$ satisfies the stated Bernoulli restriction decision-tree depth bound, provided the given parameter hypotheses hold.

**Proof.** Choose a circuit witnessing the representation hypothesis. First use equality of the represented functions to replace the original function inside the restriction probability by the circuit’s evaluation; the probability is unchanged (`bernoulliRestrProb_congr_fn'`). If the circuit is a literal, represent that literal as a one-term DNF and apply the general DNF switching bound; the literal’s width is at most the circuit’s fan-in bound. If the circuit is a node, split according to its gate type. For an OR node, the depth-at-most-two hypothesis allows its children to be converted into a DNF: the conversion preserves evaluation (`depth2OrToDNF_eval`) and has width bounded by the node’s maximum fan-in (`depth2OrToDNF_width_le`). The general DNF switching theorem then gives the claimed probability bound. For an AND node, convert its children into a CNF instead; this preserves evaluation (`depth2AndToCNF_eval`) and its width is bounded by the node’s maximum fan-in (`depth2AndToCNF_width_le`). Applying the general CNF switching theorem gives the same bound. In each node case, the circuit fan-in hypothesis supplies the required width bound, and the remaining parameter hypotheses are exactly those required by the applicable switching theorem.

**Key facts.** `LMN.bernoulliRestrProb_congr_fn'`, `LMN.depth2OrToDNF_eval`, `LMN.depth2OrToDNF_width_le`, `LMN.switching_bernoulli_dtDepth_dnf_general`, `LMN.depth2AndToCNF_eval`, `LMN.depth2AndToCNF_width_le`, `LMN.switching_bernoulli_dtDepth_cnf_general`.
