<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/MajorityFourierOneNorm.lean :: FABL.sum_range_eq_sum_odd_of_even_eq_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Even-Zero Sum Reduces to Odd Terms

**Claim.** If $a_{2j}=0$ for every nonnegative integer $j$, then for every nonnegative integer $m$, the sum of $a_k$ for $0\le k\le 2m+1$ equals the sum of $a_{2j+1}$ for $0\le j\le m$.

**Proof.** Proceed by induction on $m$. When $m=0$, the left side is $a_0+a_1$; the even-term hypothesis gives $a_0=0$, leaving $a_1$, as required. For the induction step, the sum through index $2(m+1)+1$ is the previous sum through $2m+1$, followed by the two terms $a_{2m+2}$ and $a_{2m+3}$. The even-term hypothesis, applied at $m+1$, makes $a_{2m+2}=0$. By the induction hypothesis the previous sum is the sum of the odd-indexed terms through $a_{2m+1}$, and the remaining term $a_{2m+3}$ is the next odd-indexed term. Together these are exactly the odd-indexed sum through $a_{2(m+1)+1}$.
