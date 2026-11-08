<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Word.lean :: Complexity.Codec.cfgCode_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Configuration Code Size Bound

**Claim.** The natural number represented by the configuration encoding is strictly less than $2^{K(s+L(|x|)+1)}$.

**Proof.** For any Boolean string $w$, its represented value is strictly less than $2^{|w|}$ (`Complexity.Codec.bitsVal_lt_two_pow`). Apply this to the configuration encoding. Its length is at most $K(s+L(|x|)+1)$ by the encoding-length bound (`Complexity.Codec.length_cfgWord_le`). Since exponentiation by $2$ is monotone in the natural-number exponent, these inequalities give the claimed strict bound.

**Key facts.** `Complexity.Codec.bitsVal_lt_two_pow`, `Complexity.Codec.length_cfgWord_le`.
