<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Randomization/General.lean :: BooleanAnalysis.Hypercontractivity.centered_negative_contraction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform centered negative contraction

**Claim.** For every $q\ge2$, there is a constant $c$ with $0<c\le1$, equal to $2/5$ when $q=4$, such that the stated centered negative contraction holds for every probability space, mean-zero $L^q$ random variable, and real $a$.

**Proof.** Apply the scalar contraction theorem to $q\ge2$ (\texttt{scalar\_contraction}). It supplies a constant $c$ with $0<c\le1$, with $c=2/5$ when $q=4$, and the pointwise inequality $|1-cz|^q\le |1+z|^q-q(1+c)z$ for every real $z$. For any probability space and any eligible $X$, the norm comparison theorem for scalar contractions (\texttt{norm\_le\_of\_scalar}) integrates this pointwise inequality using the mean-zero condition and the $L^q$ hypothesis, yielding $N_q(a-cX)\le N_q(a+X)$. These choices of $c$ work uniformly for all the spaces and random variables in the claim.

**Key facts.** `BooleanAnalysis.Hypercontractivity.CenteredContraction.scalar_contraction`, `BooleanAnalysis.Hypercontractivity.CenteredContraction.norm_le_of_scalar`.
