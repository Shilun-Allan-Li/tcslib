<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/ModThree.lean :: FABL.modThreeCubicProduct_expansion -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Complex Product Expansion

**Claim.** For a sign vector $x=(x_0,\ldots,x_{n-1})$ and each subset $S\subseteq\{0,\ldots,n-1\}$, the product of the complex factors expands as $\prod_i(-\frac12+\frac{\sqrt3}{2}x_i i)=(-\frac12)^n\sum_S(-\sqrt3)^{|S|}m_S(x)i^{|S|}$.

**Proof.** Rewrite each factor as $(-1/2)(1+(-\sqrt3 x_i)i)$. Multiplying these factorizations extracts one constant factor $-1/2$ for every coordinate, giving $(-1/2)^n$ times the product of the terms $1+(-\sqrt3 x_i)i$. Distributing this product amounts to choosing, for each coordinate, either $1$ or the other term; the coordinates where the latter is chosen form a subset $S$. The resulting term is the product over $i\in S$ of $(-\sqrt3 x_i)i$. By the variable-product identity (\texttt{FABL.modThreeCubicVariableProduct}), this is exactly the term indexed by $S$ in the stated sum.

**Key facts.** `FABL.modThreeCubicVariableProduct`.
