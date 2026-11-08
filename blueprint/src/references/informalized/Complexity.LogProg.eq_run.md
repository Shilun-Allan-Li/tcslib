<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Frag.lean :: Complexity.LogProg.eq_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Execution of the Equality Program

**Claim.** The equality program reaches the yes state exactly when the two stored numbers agree, and otherwise reaches the no state, while its earlier configurations remain in the prescribed comparison states with both heads together and within the stated bounds.

**Proof.** First apply the common-prefix comparison result (`eqC_run`) to the two binary words for $a$ and $b$, taking the common prefix to be empty. It yields a time $T_1$ and position $p$ where the program has reached the branching state: the yes-branch state if the words agree, and the no-branch state otherwise. Before that time it remains in the comparison state, with the common head position bounded below by $-1$ and above by the length of the first word. The hypotheses for the two comparison states ensure that these steps make no oracle calls.

The binary representation map is injective (`bits_injective`), so the binary words agree exactly when $a=b$. Split into these two cases. In the equal case, the branching state is the yes-branch state; in the unequal case, it is the no-branch state. Apply the one-word scan result (`eqB_run`) from position $p$ to the chosen branch. It shows that after $(p+1)^{\mathrm{toNat}}+1$ additional steps the program reaches the designated final state with both heads returned to $0$. During this scan, the shared head stays between $-1$ and $p$, and the state is the selected branch state; its transition hypotheses also rule out oracle calls.

Concatenate the comparison run and the scan run using the run-addition law (`rrun_add`). The resulting endpoint is the configuration in the claimed yes/no state at position $0`. For any earlier time, if it is before $T_1$, the comparison-run bound applies. Otherwise write it as $T_1+t'$; it is strictly before the endpoint, so the scan-run bound applies. In either part the heads remain together, the state makes no oracle call, and the position lies between $-1$ and the length of the first binary word.

**Key facts.** `Complexity.LogProg.eqC_run`, `Complexity.LogProg.bits_injective`, `Complexity.LogProg.eqB_run`, `Complexity.LogProg.rrun_add`.
