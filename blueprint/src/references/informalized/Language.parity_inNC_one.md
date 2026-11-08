<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Parity.lean :: Language.parity_inNC_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parity in Log-Depth Circuit Complexity

**Claim.** The language of Boolean lists with an odd number of true entries belongs to the circuit class with fan-in two, polynomial size, and depth bounded by a constant multiple of $\log_2 n+1$.

**Proof.** The established tree-circuit construction places the parity language in the tree-restricted version of this class with depth exponent $1$ (Language.parity_inTreeNC_one). The theorem that every such tree circuit family also qualifies as a general circuit family, preserving the depth exponent (Language.InTreeNC.inNC), then yields the claimed membership.

**Key facts.** `Language.parity_inTreeNC_one`, `Language.InTreeNC.inNC`.
