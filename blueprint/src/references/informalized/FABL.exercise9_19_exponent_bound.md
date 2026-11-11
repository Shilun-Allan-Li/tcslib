<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/LevelWeightAsymptotics.lean :: FABL.exercise9_19_exponent_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Numerical exponent bound

**Claim.** The real numbers satisfy $21/20\le8/5-(373/1000)\log 4$.

**Proof.** The logarithm estimate $\log 4<7/5$ (\texttt{FABL.log\_four\_lt\_seven\_fifths}) and the positivity of $373/1000$ imply
\[
\frac85-\frac{373}{1000}\log 4>\frac85-\frac{373}{1000}\cdot\frac75=\frac{1120-2611/5}{1000}=\frac{21}{20}.
\]
In particular, the claimed weak inequality holds.

**Key facts.** `FABL.log_four_lt_seven_fifths`.
