<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Products/Basic.lean :: BooleanAnalysis.Hypercontractivity.signedIntersectionEnergy_insert -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Insertion recurrence for intersection energy

**Claim.** For finite $S$, an element $i\notin S$, and a real-valued function $g$ on finite subsets, the signed intersection energy satisfies $E_{S\cup\{i\}}(g)=E_S(T\mapsto g(T\cup\{i\}))-E_S(g)$.

**Proof.** Partition the subsets of $S\cup\{i\}$ into those omitting $i$ and those containing it; the powerset sum is thereby expanded in each of its two indices. For $A\subseteq S$, adjoining $i$ increases the cardinality of the ambient set by one without changing $|A|$, so its sign factor is the negative of the original factor $(-1)^{|S|-|A|}$. The same applies to the second index. In the intersection term, if neither subset contains $i$, the intersection is $A\cap B$; if both contain $i$, it is $(A\cap B)\cup\{i\}$; and if just one contains $i$, it remains $A\cap B$. Combining the four possibilities, the two sign changes make the term with both inclusions positive and the mixed terms negative. Summing these contributions gives the energy on $S$ with $g$ evaluated on $T\cup\{i\}$, minus the energy on $S$ with $g$ unchanged, as claimed.
