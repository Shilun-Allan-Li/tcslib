<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LayeredPPoly.lean :: Language.inLayeredPPoly_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Size Layered Circuit Characterization

**Claim.** A Boolean language is recognized by polynomial-size layered circuits using only identity, NOT, and unbounded fan-in AND gates exactly when there is such a family with polynomially bounded size and recognized language equal to that language.

**Proof.** Unpack membership in the polynomial layered-size class. It supplies natural numbers $a,k$, a circuit family $C$, the required gate restriction, a bound $(C_n).\mathrm{size}\leq a(n+1)^k$ for every input length, and equality of its language with $L$. The same $a,k$ and family directly witness the stated right-hand side. Conversely, unpack the right-hand side to obtain such $a,k,C$ and its size bound; these data, together with the gate restriction and language equality, are precisely a witness that $L$ belongs to the polynomial layered-size class.
