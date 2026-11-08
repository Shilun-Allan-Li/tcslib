<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveNANDComposition.lean :: FABL.recursiveNandOutputCosts_le_recurrence -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output-Cost Recurrence Bounds

**Claim.** For every natural number $d$, the randomized recursive NAND tree's maximum expected query cost on inputs with output $+1$ is at most the recursively defined false cost at level $d$, and its corresponding maximum on inputs with output $-1$ is at most the recursively defined true cost at level $d$.

**Proof.** Proceed by induction on $d$. At level zero, both output-conditioned costs equal the initial cost $1$, so the two bounds follow from the base definitions. For the induction step, the false-output cost at level $d+1$ is at most twice the true-output cost at level $d$ (\(\texttt{FABL.recursiveNandFalseOutputCost_succ_le}\)). By the induction hypothesis, this is at most twice the true recurrence cost at level $d$, which equals the false recurrence cost at level $d+1$ (\(\texttt{FABL.recursiveNandFalseCost_succ}\)). Likewise, the true-output cost at level $d+1$ is at most the sum of the false-output cost at level $d$ and half the true-output cost there (\(\texttt{FABL.recursiveNandTrueOutputCost_succ_le}\)). Applying both induction bounds gives at most the false recurrence cost plus half the true recurrence cost at level $d$, exactly the true recurrence cost at level $d+1$ (\(\texttt{FABL.recursiveNandTrueCost_succ}\)).

**Key facts.** `FABL.recursiveNandFalseOutputCost_succ_le`, `FABL.recursiveNandFalseCost_succ`, `FABL.recursiveNandTrueOutputCost_succ_le`, `FABL.recursiveNandTrueCost_succ`.
