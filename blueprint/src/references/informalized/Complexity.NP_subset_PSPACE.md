<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Inclusions.lean :: Complexity.NP_subset_PSPACE -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# NP Is Contained in Polynomial Space

**Claim.** Every language in $\mathrm{NP}$ belongs to $\mathrm{PSPACE}$.

**Proof.** Take a language $L\in\mathrm{NP}$, with verifier language $V\in\mathrm P$ and certificate length $C(n+1)^c$ on inputs of length $n$. First choose a clean deterministic verifier for $V$ that runs in polynomial time (`b2b_clean_verifier`). The proof then combines three machines: this verifier, a machine that copies its input, and a machine that generates the required unary certificate length (`computesFunInTime_id_spaceUsed`, `computesFunInTime_polyUnary_spaceUsed`). The host-machine construction (`b2b_host`) uses them to decide whether some certificate of the prescribed length makes the verifier accept. The host-contract theorem (`b2b_host_contract`) supplies, for each input, a halting computation with the correct membership answer and a space bound in terms of the input length, certificate length, and the component machines' bounds. The definition of $L$ identifies its membership condition with existence of such an accepted certificate. Finally, `b2b_ledger_bound` bounds the host's total space by $D(n+1)^f$ for suitable constants $D,f$. Applying the ledger-to-PSPACE theorem (`b2b_mem_PSPACE_of_ledger`) gives $L\in\mathrm{PSPACE}$, as required.

**Key facts.** `Complexity.b2b_clean_verifier`, `Turing.FinTM.computesFunInTime_id_spaceUsed`, `Turing.FinTM.computesFunInTime_polyUnary_spaceUsed`, `Complexity.b2b_ledger_bound`, `Complexity.b2b_host_contract`, `Complexity.b2b_mem_PSPACE_of_ledger`.
