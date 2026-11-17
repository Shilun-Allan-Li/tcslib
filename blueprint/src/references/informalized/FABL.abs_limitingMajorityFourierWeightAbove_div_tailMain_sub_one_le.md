<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/MajorityFourierTailAsymptotics.lean :: FABL.abs_limitingMajorityFourierWeightAbove_div_tailMain_sub_one_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Asymptotic Majority Fourier Tail Bound

**Claim.** For every odd natural number $k$, the limiting majority Fourier weight above degree $k$, divided by its stated tail main term, differs from $1$ by at most $1/k$.

**Proof.** The tail main term is positive because $k>0$. The interval bound for the tail weight places its ratio to this positive main term between $1-1/k$ and $1+1/(3k)$: divide the lower endpoint by the main term, and divide the upper endpoint likewise. Since $k>0$, we have $1/(3k)\leq 1/k$, so this ratio lies in $[1-1/k,1+1/k]$. Any real number in this interval differs from $1$ in absolute value by at most $1/k$, as required.

**Key facts.** `FABL.majorityFourierTailMain_pos`, `FABL.limitingMajorityFourierWeightAbove_mem_Icc`.
