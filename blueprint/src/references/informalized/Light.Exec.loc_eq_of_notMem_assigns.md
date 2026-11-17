<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Assigns.lean :: Light.Exec.loc_eq_of_notMem_assigns -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unassigned locations are unchanged

**Claim.** If a statement executes from $\sigma$ to $\sigma'$ and location $y$ is absent from the statement’s assignment list, then $\sigma'.loc(y)=\sigma.loc(y)$.

**Proof.** Induct on the execution derivation. Skip and a false-guard loop leave locations unchanged; a store changes only memory. An assignment updates only its assigned location, which differs from $y$ by the assumption that $y$ is absent from the assignment list; the same update argument applies to a call’s returned location. For a sequence, absence from the concatenated assignment list implies absence from each component’s list, so the induction hypotheses give equality across each execution in turn. For either conditional branch, absence from the combined branch assignment lists implies absence from the selected branch’s list, and the induction hypothesis applies. A true-guard loop preserves the equality through its body execution and subsequent loop execution by applying the induction hypotheses successively.
