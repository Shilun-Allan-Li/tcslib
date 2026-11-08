<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clNPVerifier -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Verifier Parameters for NP Languages

**Claim.** For every language in NP, there are certificate parameters, a Boolean verifier language, and an oblivious finite Boolean Turing machine with positive time-bound parameters, such that membership is equivalent to acceptance of a certificate of the prescribed length and the verifier runs within the stated quadratic bound.

**Proof.** Unpack the definition of membership in NP. It supplies natural numbers $C,e$, a language $V$ in polynomial time, and the certificate equivalence: $x$ belongs to $L$ exactly when some word $u$ has length $C(|x|+1)^e$ and $xu$ belongs to $V$. Apply the oblivious-verifier result to $V$ (`Complexity.clObliviousVerifier`). It supplies a finite Boolean machine $M$, positive natural numbers $c,A,d$, obliviousness, and the bound $c(A(n+1)^d+1)^2$ for deciding $V$. Keep the certificate data from the first step and combine it with these machine parameters and properties.

**Key facts.** `Complexity.clObliviousVerifier`.
