<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/MajorityFourierTailAsymptotics.lean :: FABL.odd_rpow_neg_three_halves_eq_neg_half_div -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Odd-arity power identity

**Claim.** For every odd natural number $k$, $k^{-3/2}=k^{-1/2}/k$.

**Proof.** Write $k=2q+1$. The odd-arity formulas identify $k^{-3/2}$ with $1/(k\sqrt{k})$ and $k^{-1/2}$ with $1/\sqrt{k}$ (\texttt{oddArity\_rpow\_neg\_three\_halves} and \texttt{oddArity\_rpow\_neg\_one\_half}, respectively). Substituting the latter expression into $k^{-1/2}/k$ gives the same fraction, since $k$ is positive and hence nonzero.

**Key facts.** `FABL.oddArity_rpow_neg_three_halves`, `FABL.oddArity_rpow_neg_one_half`.
