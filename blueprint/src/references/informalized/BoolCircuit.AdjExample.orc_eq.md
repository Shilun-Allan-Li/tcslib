<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformExample.lean :: BoolCircuit.AdjExample.orc_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Oracle Test for Strict Inequality

**Claim.** For every $n,v\in\mathbb N$, the oracle returns true on $\langle 1^n,\operatorname{bits}(v)\rangle$ exactly when $v<n$.

**Proof.** The oracle is the indicator of the strict-inequality language, so its value equals the decision of membership (`indicator_eq_decide`). By definition, membership means that the input has some representation $\langle 1^{n'},\operatorname{bits}(v')\rangle$ with $v'<n'$. Equality with $\langle 1^n,\operatorname{bits}(v)\rangle$ forces $n'=n$ and the payload words to agree (`pairEncode_replicate_inj`); injectivity of the bit encoding then gives $v'=v$ (`bits_injective`). Thus membership is equivalent to $v<n$, as required.

**Key facts.** `Complexity.LogProg.indicator_eq_decide`, `Turing.pairEncode_replicate_inj`, `Complexity.LogProg.bits_injective`.
