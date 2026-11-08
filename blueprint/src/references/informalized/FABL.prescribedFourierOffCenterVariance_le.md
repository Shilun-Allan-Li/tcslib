<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/PrescribedFourierSupport.lean :: FABL.prescribedFourierOffCenterVariance_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Variance bound for a large family

**Claim.** For positive $n$, nonempty $\mathcal F$, and $0<\varepsilon<1$, if $|\mathcal F|\ge (1-\varepsilon^2/(6n))2^n$, then $2^n/|\mathcal F|-1\le \varepsilon^2/(5n)$.

**Proof.** Put $z=\varepsilon^2/n$. Positivity of $n$ and $\varepsilon$ gives $z>0$, while $\varepsilon<1$ and $n\ge1$ give $z\le1$. The elementary inequality
\[
1\le (1-z/6)(1+z/5)
\]
follows because the difference between the right side and $1$ is $z(1-z)/30$. The assumed lower bound on $|\mathcal F|$ is $(1-z/6)2^n\le |\mathcal F|$. Multiplying it by the nonnegative factor $1+z/5$ and using the displayed inequality gives $2^n\le |\mathcal F|(1+z/5)$. Since $|\mathcal F|>0$, division yields $2^n/|\mathcal F|\le1+z/5$, hence $2^n/|\mathcal F|-1\le z/5=\varepsilon^2/(5n)$.
