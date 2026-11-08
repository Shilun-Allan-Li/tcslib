<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFHard.lean :: Complexity.TQBFHard.truth_redQBF -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Truth of the reduction formula

**Claim.** Under the stated space bound for $N$ and time bound for $V$, the constructed quantified Boolean formula is true exactly when $x$ belongs to the language decided by $N$.

**Proof.** Set $n=|x|$, let $w$ be the reduction width, $s$ the chosen work-space radius, $L_c$ the configuration-code length, and $C$ the reduction circuit. First remove the existential suffix that encodes a satisfying assignment for the circuit's CNF: the pointwise extension characterization (truth_exSuffix_of_pointwise) and the circuit-extension equivalence (toCNF_extension_iff) reduce truth of the formula to the prefix truth of the assertion that $C$ evaluates to true. The quantifier-prefix length is the width of the circuit input (length_redQuants), as required for that characterization.

Next identify the circuit's predicate. The evaluation theorem for the reduction circuit (eval_redCircuit), followed by the predicate characterization (predB_iff), identifies its truth with three conditions: the initial and accepting configuration blocks are valid, and the level matrix condition holds. The level-matrix flattening theorem (levelMatrix_iff_flat) rewrites the latter as the existence of a failed selector at some level or a final encoded step. Applying the top-level prefix characterization (prefixTruth_top) therefore turns the quantified assertion into the existence of two width-$w$ endpoint blocks satisfying initialization, acceptance, and the midpoint reachability condition.

Finally, the space assumption supplies $d(n^c+1)\le s$: bound $n^c$ by $(n+1)^c$ and use $1\le(n+1)^c$. The code-length bound (vlen_le_vwid) gives $L_c\le w$, and the configuration-count estimate (configBound_le_two_pow) gives the required bound by $2^w$. The machine characterization theorem (mem_iff_mid), with these bounds, identifies existence of the endpoint blocks with $x\in L$. Reversing its equivalence yields the claimed direction.

**Key facts.** `Complexity.QBF.truth_exSuffix_of_pointwise`, `Complexity.TQBFHard.length_redQuants`, `Complexity.TQBFHard.toCNF_extension_iff`, `Complexity.TQBFHard.eval_redCircuit`, `Complexity.TQBFHard.levelMatrix_iff_flat`, `Complexity.TQBFHard.predB_iff`, `Complexity.QBF.prefixTruth_congr`, `Complexity.TQBFHard.prefixTruth_top`, `Complexity.TQBFHard.vlen_le_vwid`, `Complexity.TQBFHard.configBound_le_two_pow`, `Complexity.TQBFHard.mem_iff_mid`.

**Caveat.** The supplied statement of predB_iff is truncated, so its exact final equivalence is not fully visible; the proof uses it to identify the circuit predicate with initialization, acceptance, and the flattened level condition.
