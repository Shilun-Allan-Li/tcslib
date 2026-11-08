<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncInnerProduct.lean :: CommunicationComplexity.Functions.InnerProduct.sum_mul_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Factoring constants from a sum

**Claim.** For finite lphalpha and real-valued functions  and g, the sum of a f(x) times b g(x) equals a b times the sum of f(x)g(x).

**Proof.** For each index $x$, commutativity and associativity of real multiplication give $(a f(x))(b g(x))=(ab)(f(x)g(x))$. Summing these terms factors the constant $ab$ out of the finite sum, yielding the stated identity.
