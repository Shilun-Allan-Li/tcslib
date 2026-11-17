<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GotsmanLinialExtremizer.lean :: FABL.gotsmanLinial_factor_ne_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonvanishing of Layer Factors

**Claim.** For $x\in\{\pm1\}^n$ and $j<k$, the difference between the coordinate sum of $x$ and the root $2(a+j)-n+1$, where $a=\lfloor(n-k)/2\rfloor$, is nonzero.

**Proof.** The coordinate sum of a sign vector is twice its number of positive coordinates minus $n$ (\texttt{FABL.sum_signValue_eq_two_mul_positiveCoordinateCount_sub}). If the stated difference were zero, equating these expressions and cancelling $-n$ would give $2P=2(a+j)+1$, where $P$ is the number of positive coordinates. The left side is even and the right side odd, an impossibility. Hence the difference is nonzero.

**Key facts.** `FABL.sum_signValue_eq_two_mul_positiveCoordinateCount_sub`.
