<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clTemplate_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation after relabeling

**Claim.** Relabeling the chosen CNF table for $p$ by $w$ evaluates to $p$ on the vector whose $i$-th bit is $a(w(i))$.

**Proof.** The CNF evaluation rule for a relabeled formula identifies its value under $a$ with the value of the original formula under the assignment obtained by first applying the relabeling to each variable. By the evaluation property of the chosen table (`Complexity.clTemplate_spec`), that value is $p$ applied to the original table's first $box{\ell}$ bits. Substituting the relabeled assignment gives the vector $i\mapsto a(w(i))$, as required.

**Key facts.** `Complexity.clTemplate_spec`.
