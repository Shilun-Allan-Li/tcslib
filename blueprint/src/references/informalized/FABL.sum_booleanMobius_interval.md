<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/OrthogonalDecomposition.lean :: FABL.sum_booleanMobius_interval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Alternating Boolean interval sum

**Claim.** For finite sets $A\subseteq S$, the alternating sum over subsets $J\subseteq S$ containing $A$, with sign $(-1)^{|S|-|J|}$, equals $1$ when $A=S$ and $0$ otherwise.

**Proof.** Replace each such $J$ by its complement within $S$, $U=S\setminus J$. This gives a bijection from subsets $J$ with $A\subseteq J\subseteq S$ to subsets $U\subseteq S\setminus A$. Since $J\subseteq S$, the cardinality identity $|S|-|J|=|S\setminus J|$ turns the original sum into $\sum_{U\subseteq S\setminus A}(-1)^{|U|}$. The alternating sum over the subsets of a finite set is $1$ if that set is empty and $0$ otherwise: for a nonempty set, pairing subsets that differ by a fixed element cancels their terms. Thus the sum is $1$ exactly when $S\setminus A=\varnothing$, which, given $A\subseteq S$, is equivalent to $A=S$.
