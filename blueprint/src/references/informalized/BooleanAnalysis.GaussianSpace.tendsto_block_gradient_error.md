<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/GaussianBobkov.lean :: BooleanAnalysis.GaussianSpace.tendsto_block_gradient_error -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Vanishing Block Gradient Error

**Claim.** For fixed $n$ and $C$, the sequence $\sqrt{n(m+1)}\,2C/(m+1)$ tends to zero as $m$ tends to infinity.

**Proof.** The sequence can be rewritten as $(2C\sqrt n)\sqrt{1/(m+1)}$. The reciprocal sequence $1/(m+1)$ tends to zero, and continuity of the square-root function on the nonnegative reals shows that its square root also tends to zero. Multiplication by the fixed constant $2C\sqrt n$ preserves convergence to zero. The proof verifies the rewriting by elementary square-root and field identities.
