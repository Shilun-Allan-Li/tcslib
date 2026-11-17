<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/HypercontractiveApplications.lean :: FABL.unbiasedLabel_collisionProbability -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Collision bound for unbiased labels

**Claim.** If each of the $m$ labels has uniform measure $1/m$ on the Boolean cube, then for the correlated pair $(X,Y)$ with correlation parameter $0\le\rho\le1$, the probability that the labels agree is at most $(1/m)^{(1-\rho)/(1+\rho)}$.

**Proof.** For each label $j$, let $f_j$ be its indicator: it is $1$ on points carrying label $j$ and $0$ elsewhere. Its values are therefore in $\{0,1\}$, and the unbiasedness assumption says its mean is $\alpha=1/m$. The event that the two labels agree is the disjoint union, over $j$, of the events that both points have label $j$. Additivity of expectation over this finite sum (\texttt{FABL.pmfExpectation\_sum}) expresses the collision probability as the sum of these individual event probabilities. For each $j$, the small-set expansion bound (\texttt{FABL.smallSetExpansion\_event}) bounds the probability that both correlated points lie in the $j$-th label class by $\alpha^{2/(1+\rho)}$. Summing $m$ identical bounds gives $m\alpha^{2/(1+\rho)}$. Since $m=\alpha^{-1}$, the exponent laws combine this as $\alpha^{(1-\rho)/(1+\rho)}$, which is the claimed bound. The event-equivalence result (\texttt{FABL.pmfEventProbability\_congr}) justifies replacing each label event by the corresponding indicator event.

**Key facts.** `FABL.pmfExpectation_sum`, `FABL.smallSetExpansion_event`, `FABL.pmfEventProbability_congr`.
