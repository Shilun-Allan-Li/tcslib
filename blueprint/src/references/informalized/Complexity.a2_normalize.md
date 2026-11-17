<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.a2_normalize -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exponential time class normalization

**Claim.** If a language of binary strings is decided by a finite nondeterministic Turing machine within $K(n+C\cdot2^{(n+1)^c}+1)^r$, then it belongs to $\bigcup_{e\in\mathbb{N}}\mathrm{NTIME}(n\mapsto2^{n^e})$.

**Proof.** Choose $K,r$ and a deciding machine $N$ from the hypothesis. The envelope bound (`a2_envelope`) supplies $A,e$ such that, for each input length $n$, the given time bound is at most $A\cdot2^{n^e}$. Keep the same machine and choose exponent $e$ in the union. Its halting guarantee extends to the larger time bound by monotonicity of halting (`HaltsWithin.mono`). For acceptance, because every computation branch has already halted by the original bound, extending the choice word to the larger prescribed length does not change whether an accepting computation exists (`acceptsWithin_iff_of_halts`). Therefore the same machine decides the language within the normalized bound, proving membership in the union.

**Key facts.** `Complexity.a2_envelope`, `Turing.NDTM.HaltsWithin.mono`, `Complexity.acceptsWithin_iff_of_halts`.
