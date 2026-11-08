<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadThreeSat.lean :: FABL.prod_piecewise_two_sets -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Product for two nested subsets

**Claim.** For nested finite subsets $A\subseteq B$, the product that assigns $a$ on $A$, $b$ on $B\setminus A$, and $1$ elsewhere is $a^{|A|}b^{|B|-|A|}$.

**Proof.** First split the full product into the factors indexed by $A$ and those indexed by its complement. The first group contributes $a^{|A|}$. Within the complement, split again according to membership in $B$: the indices there that lie in $B$ are exactly $B\setminus A$, and all other factors are $1$. Thus the second group contributes $b^{|B\setminus A|}$. Since $A\subseteq B$, the cardinality of this difference is $|B|-|A|$, yielding the formula.
