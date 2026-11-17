<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PClosure.lean :: Complexity.mem_P_of_atoms -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Finite Boolean Combination Closure

**Claim.** If each language defined by an atomic bit condition $b_i(z)=1$ belongs to $\mathsf{P}$, then the language defined by any Boolean function of the finitely many bits also belongs to $\mathsf{P}$.

**Proof.** First fix a bit assignment $\beta$ and a finite set of indices $s$. We show by induction on $s$ that the strings satisfying $b_i(z)=\beta(i)$ for every $i\in s$ form a language in $\mathsf{P}$. For the empty set this is the universal language (`Complexity.univ_mem_P`). When inserting an index $i$, the new condition is the intersection of the old conditions with the single condition $b_i(z)=\beta(i)$. If $\beta(i)=1$, that single-condition language is in $\mathsf{P}$ by hypothesis; if $\beta(i)=0$, it is the complement of the language for bit $1$, hence is in $\mathsf{P}$ by closure under complements (`Complexity.compl_mem_P`). Closure under intersections (`Complexity.inter_mem_P`) completes the induction.

Next, for any finite set of assignments, the language whose strings realize at least one assignment in that set is in $\mathsf{P}$. Induct on the set of assignments: the empty set gives the empty language (`Complexity.empty_mem_P`), and adjoining one assignment takes a union with its realization language from the first step. Closure under unions (`Complexity.union_mem_P`) gives the claim.

Finally, take the finite set of all assignments $\beta$ for which $F(\beta)=1$. A string is in the desired language exactly when its actual assignment $i\mapsto b_i(z)$ belongs to this set: one direction chooses that actual assignment, and the other uses the equalities $b_i(z)=\beta(i)$ to identify it with the actual assignment. The preceding finite-union result therefore proves membership in $\mathsf{P}$.

**Key facts.** `Complexity.univ_mem_P`, `Complexity.compl_mem_P`, `Complexity.inter_mem_P`, `Complexity.empty_mem_P`, `Complexity.union_mem_P`.
