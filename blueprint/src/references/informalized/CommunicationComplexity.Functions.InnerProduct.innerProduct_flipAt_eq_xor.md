<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncInnerProduct.lean :: CommunicationComplexity.Functions.InnerProduct.innerProduct_flipAt_eq_xor -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Flipping a Coordinate Toggles the Inner Product

**Claim.** If the $i$th coordinate of $y$ is true, flipping the $i$th coordinate of $x$ toggles the mod-$2$ inner product of $x$ and $y$.

**Proof.** Separate the $i$th summand from each inner-product sum; this is valid because $i$ belongs to the full coordinate set. At every other coordinate, the flipped input agrees with $x$, so those summands have the same sum. At coordinate $i$, the contribution changes from $x_i\wedge y_i=x_i$ to $\neg x_i\wedge y_i=\neg x_i$, using $y_i=1$. Replacing $x_i$ by its negation in a sum modulo two toggles the sum, so the new inner product is the XOR of the old one with true.
