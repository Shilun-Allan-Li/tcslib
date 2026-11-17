<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean :: Complexity.compQ_query_overflow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Overflowing query is out of range

**Claim.** Under the polynomial length hypothesis, if the binary expansion of the stated output bound is shorter than the binary expansion of $p$, then the output bit at position $p$ is false and $p$ is not below the output length.

**Proof.** Write $B=(2C+3)(|\langle w,\operatorname{bin}(p)\rangle|+1)^{e+1}$. If $B\ge p$, monotonicity of the length of binary expansions (`length_bits_mono`) would imply $|\operatorname{bin}(B)|\ge|\operatorname{bin}(p)|$, contrary to the assumed strict inequality. Thus $B<p$. The output-length bound `compQ_host_cap`, applied with tail $\operatorname{bin}(p)$, gives $|\operatorname{compQ}(f,w)|\le B<p$. Consequently position $p$ lies beyond the output, so its defaulted bit is false, and $p$ is not less than the output length.

**Key facts.** `Complexity.LogProg.length_bits_mono`, `Complexity.compQ_host_cap`.
