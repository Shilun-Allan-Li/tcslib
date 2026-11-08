<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.codecValidity_cost_raw -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Raw Validity Formula Cost Bound

**Claim.** For a finite-state Turing machine $M$ with $k$ work tapes and natural numbers $n,s$, the validity CNF cost is at most the stated sum of the input-head, state, work-head, work-cell, and summary contributions.

**Proof.** Apply the one-hot CNF cost bound (`codecOneHot_cost`) to the input-head choices and the optional state choices. Since the input-head type has $n+2$ elements and the optional state type has $|\mathrm{State}(M)|+1$ elements, these contribute at most $(n+2)+1+3(n+2)^2$ and $(|\mathrm{State}(M)|+1)+1+3(|\mathrm{State}(M)|+1)^2$, respectively. Relabeling preserves cost (`codecCnfCost_relabel`).

For each work tape, the one-hot constraints on its $2s+1$ possible head locations cost at most $(2s+1)+1+3(2s+1)^2$. The constraints for each of its $2s+1$ cells consist of one two-literal clause, whose cost is $3$; thus the cell constraints for one tape cost $3(2s+1)$. Summing over the $k$ tapes uses the flat-map cost bound (`codecCnfCost_flatMap_le`), giving the two terms multiplied by $k$. The final summary clause has two literals and therefore cost $3$. Costs add across concatenated CNFs (`codecCnfCost_append`); combining these estimates gives the claimed bound.

**Key facts.** `Complexity.codecOneHot_cost`, `Complexity.codecCnfCost_relabel`, `Complexity.codecCnfCost_flatMap_le`, `Complexity.codecCnfCost_append`.
