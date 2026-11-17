<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.sat_foldMax_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Maximum Fold over Concatenation

**Claim.** For lists $a,b$ of natural numbers, folding maximum with initial value $0$ over their concatenation equals the maximum of the two separate folds with initial value $0$.

**Proof.** Induct on $a$. If $a$ is empty, the concatenation is $b$, and the fold over the empty list contributes the initial value $0$, so the claimed equality follows. If $a$ begins with $v$ and has tail $a'$, the fold over the concatenation is $\max(v, (a' ++ b).\mathrm{foldr}(\max,0))$. By induction, the inner fold is the maximum of the folds over $a'$ and $b$. Associativity of maximum rearranges this to the maximum of the fold over $a$ and the fold over $b$.
