<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitSatReduction.lean :: BoolCircuit.CktSatReduction.polyTimeComputable_outPrefix -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Output Prefix

**Claim.** The function that maps a bit string $w$ to the output prefix formed from the description tail of $w$ is computable in polynomial time.

**Proof.** The output is the concatenation of the constant prefix $[\mathrm{true},\mathrm{true}]$, the description tail, and the constant suffix $[\mathrm{true},\mathrm{false}]$. Each constant function is polynomial-time computable (`polyTimeComputable_const`), and the description tail is a finite-state transduction, hence polynomial-time computable (`polyTimeComputable_transduce`). Concatenation preserves polynomial-time computability (`PolyTimeComputable.append`), so the whole output-prefix function is polynomial-time computable.

**Key facts.** `Complexity.polyTimeComputable_const`, `Complexity.polyTimeComputable_transduce`, `Complexity.PolyTimeComputable.append`.
