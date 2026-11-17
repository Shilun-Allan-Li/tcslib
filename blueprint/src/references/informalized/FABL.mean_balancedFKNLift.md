<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/FKNImprovement.lean :: FABL.mean_balancedFKNLift -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Balanced lift has mean zero

**Claim.** For every Boolean function $f$, the real-valued sign representation of its balanced lift to the $(n+1)$-dimensional sign cube has mean zero.

**Proof.** Split the uniform mean according to the first coordinate, which is equally likely to be $1$ or $-1$ ($\texttt{FABL.expect_fin_cons}$). When the first coordinate is $1$, the lifted function reduces to $f$ on the remaining coordinates; when it is $-1$, it reduces to $-f(-x)$ ($\texttt{FABL.balancedFKNLift_toReal_fin_cons_one}$ and $\texttt{FABL.balancedFKNLift_toReal_fin_cons_neg_one}$). The mean of $-f(-x)$ is the negative of the mean of $f(x)$: negation permutes the sign cube, so it preserves the uniform mean, and negation of the function negates that mean. Thus the two conditional means cancel, giving zero.

**Key facts.** `FABL.expect_fin_cons`, `FABL.balancedFKNLift_toReal_fin_cons_one`, `FABL.balancedFKNLift_toReal_fin_cons_neg_one`.
