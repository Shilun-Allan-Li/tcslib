<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFourier.lean :: FABL.sum_pairDiagonalWeight -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sum of Pairwise Diagonal Weights

**Claim.** For a finite set $U$ of coordinates and a real number $\delta$, the sum over ordered pairs $(i,j)\in U\times U$, with weight $\delta$ on the diagonal and $\delta^2$ off the diagonal, is $\delta^2|U|^2+\delta(1-\delta)|U|$.

**Proof.** Fix $i\in U$. In the inner sum over $j\in U$, assign the baseline weight $\delta^2$ to every term, then add the correction $\delta-\delta^2$ at the unique term $j=i$. The inner sum is therefore $\delta^2|U|+(\delta-\delta^2)$. Summing this over all $i\in U$ gives $\delta^2|U|^2+(\delta-\delta^2)|U|$, which rearranges to the stated expression.
