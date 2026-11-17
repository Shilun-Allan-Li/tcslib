<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/UnaryLogspace.lean :: Complexity.ltLang_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Log-space decidability of the comparison language

**Claim.** The language of strings encoding $1^n$ paired with the binary expansion of an index $i<n$ is decidable in logarithmic space.

**Proof.** The proof builds a logarithmic-space decider using the composition theorem for alternating register machines (Complexity.LogProg.arm_decides_poly). Its oracle languages are the doubled-string language, already known to lie in logarithmic space (Complexity.LogProg.dblLang_mem), and a fixed unary-index comparison routine. The comparison machine has a start state and uses the doubled-string oracle to check the input format and recover a canonical binary index.

For a valid plain input, write the second component in canonical form as the binary expansion of its value $i$ (Complexity.LogProg.canon_eq_bits); the canonicality of binary expansions is supplied by Complexity.LogProg.canon_bits. The target language membership condition on this encoding is exactly $i<n$ (Complexity.mem_unaryIdx), so its indicator is $\mathrm{decide}(i<n)$ (Complexity.LogProg.indicator_eq_decide). The machine first makes the transition from its start state to its test state, then runs the comparison loop (Complexity.LogProg.AHalt.step and Complexity.LtM.loop), which halts with precisely that answer. The loop's workspace is bounded by a polynomial in the input length, as required by the composition theorem.

For an input that is not valid plain syntax, it cannot belong to the target language: membership would imply valid plain syntax (Complexity.validPlain_of_mem_unaryIdx). The machine therefore rejects immediately, using constant workspace. These two cases establish the correctness hypothesis for the composition theorem, which yields logarithmic-space decidability.

**Key facts.** `Complexity.LogProg.arm_decides_poly`, `Complexity.LogProg.dblLang_mem`, `Complexity.LogProg.canon_eq_bits`, `Complexity.LogProg.indicator_eq_decide`, `Complexity.LogProg.AHalt.step`, `Complexity.LtM.loop`, `Complexity.mem_unaryIdx`, `Complexity.validPlain_of_mem_unaryIdx`, `Complexity.LogProg.canon_bits`.

**Caveat.** The supplied proof relies on the loop lemma for the comparison machine's correctness and workspace bound; the loop's internal construction is not included in this payload.
