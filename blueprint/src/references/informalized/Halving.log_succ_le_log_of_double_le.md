<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/MistakeBounds/Halving.lean :: Halving.log_succ_le_log_of_double_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Logarithm Increment Under Doubling

**Claim.** If $b>0$ and $2b\le a$, then $\lfloor\log_2 b\rfloor+1\le\lfloor\log_2 a\rfloor$.

**Proof.** Since $b>0$, the defining bound for the integer base-$2$ logarithm gives $2^{\lfloor\log_2 b\rfloor}\le b$. Multiplying by $2$ yields $2^{\lfloor\log_2 b\rfloor+1}\le 2b\le a$. The defining comparison between powers and the integer logarithm then implies $\lfloor\log_2 b\rfloor+1\le\lfloor\log_2 a\rfloor$.
