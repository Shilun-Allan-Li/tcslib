<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Applications/KKL/Basic.lean :: KKL.card_bounded_subsets_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Counting bounded subsets

**Claim.** For a finite set $s$ and a natural number $k$, the number of subsets of $s$ having at most $k$ elements is at most $(|s|+1)^k$.

**Proof.** First prove by induction on $j$ that $\sum_{i=0}^{j}|s|^i\le (|s|+1)^j$. For $j=0$ both sides are $1$. In the induction step, add the new term $|s|^{j+1}$ to the preceding sum. The induction hypothesis bounds the old sum by $(|s|+1)^j$, while $|s|^{j+1}\le (|s|+1)^j|s|$; together these give the claimed bound for $j+1$. Now each subset $t\subseteq s$ with $|t|\le k$ belongs to the family of $i$-element subsets for $i=|t|\in\{0,\ldots,k\}$. The size of this union is at most the sum of the sizes of those families. There are $\binom{|s|}{i}$ subsets of size $i$, and $\binom{|s|}{i}\le |s|^i$. Thus the desired count is at most $\sum_{i=0}^{k}|s|^i$, which the induction bounds by $(|s|+1)^k$.
