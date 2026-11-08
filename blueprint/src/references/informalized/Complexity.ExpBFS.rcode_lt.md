<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Radius.lean :: Complexity.ExpBFS.rcode_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound on reachable codes

**Claim.** Every code reachable from the initial configuration by encoded steps within the $s$-window is less than $2^{K(N)(s+\ell(|x|)+1)}$.

**Proof.** Use the reachability characterization (`rcode_iff`) to write $u$ as the code of the configuration reached by some finite choice string. The uniform configuration-code bound (`cfgCode_lt`) applies to that configuration directly, giving the required strict inequality.

**Key facts.** `Complexity.ExpBFS.rcode_iff`, `Complexity.Codec.cfgCode_lt`.
