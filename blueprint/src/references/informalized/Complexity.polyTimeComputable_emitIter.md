<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PolyTimeBlockLoop.lean :: Complexity.polyTimeComputable_emitIter -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Iterated Output Concatenation

**Claim.** If $g$ and $e$ are polynomial-time computable and all iterates $g^i(w)$ have length bounded by $b(|w|+1)^l$, then concatenating $e(g^i(w))$ for $0\le i\le a'(|w|+1)^{k'}$ is polynomial-time computable.

**Proof.** Choose machines $G$ and $E$ computing $g$ and $e$ within polynomial time bounds, as supplied by the two hypotheses. The machine construction theorem for iterated output concatenation applies to these machines: given their bounds, the iteration limit, and the assumed uniform length bound on every intermediate iterate, it supplies a machine and polynomial time bound for the concatenation of the corresponding outputs (`FinTM.exists_emitIterTM`). This is exactly the required function, so its supplied machine witnesses polynomial-time computability.

**Key facts.** `Turing.FinTM.exists_emitIterTM`.
