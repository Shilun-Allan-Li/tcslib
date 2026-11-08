<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaResources.lean :: FABL.clog_card_lowDegreeJuntaFourierFamily_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Size bound for a low-degree Fourier family

**Claim.** For a subset of the coordinates and a degree cutoff of $\lfloor 3k/4\rfloor$, the base-two logarithm rounded up of the corresponding Fourier family’s size is at most $(\lfloor 3k/4\rfloor+1)(n+2)$.

**Proof.** Write $d=\lfloor 3k/4\rfloor$. The family’s cardinality is at most $(d+1)(n+1)^d$, by the bound on the size of the low-degree junta Fourier family (\texttt{card\_lowDegreeJuntaFourierFamily\_le}). Bound each factor by a power of two: $d+1\le 2^{d+1}$ and $n+1\le 2^{n+1}$. Hence the cardinality is at most $2^{d+1} (2^{n+1})^d=2^{(d+1)+(n+1)d}$. The exponent satisfies $(d+1)+(n+1)d\le(d+1)(n+2)$, so the cardinality is at most $2^{(d+1)(n+2)}$. The defining comparison for the rounded-up base-two logarithm now gives the claimed bound.

**Key facts.** `FABL.card_lowDegreeJuntaFourierFamily_le`.
