<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.prod_choose_sub_mul_factorials -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Factorial Identity for Successive Choices

**Claim.** If $td\le n$, then the product of the successive binomial choices, multiplied by $(d!)^t$ and $(n-td)!$, equals $n!$.

**Proof.** Induct on $t$. For $t=0$, the product is empty and both sides reduce to $n!$. For the successor step, the hypothesis gives $td+d\le n$, so $d\le n-td$ and $td\le n$. The new final binomial factor is $\binom{n-td}{d}$, and the remaining factorial is $(n-td-d)!$, since $n-(t+1)d=(n-td)-d$. The factorial formula for a binomial coefficient gives $\binom{n-td}{d}d!(n-td-d)!=(n-td)!$. Regrouping the factors therefore reduces the successor expression to the induction expression at $t$, which equals $n!$.
