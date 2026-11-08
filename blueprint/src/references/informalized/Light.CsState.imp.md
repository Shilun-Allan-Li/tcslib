<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/CountSort.lean :: Light.CsState.imp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Implication for Count-Sort States

**Claim.** If a count-sort state has memory satisfying $R$, and every memory satisfying $R$ also satisfies $R'$, then the same state satisfies the corresponding conditions with $R'$ in place of $R$.

**Proof.** Unpack the state representation: it supplies parameters $c,p$ and a memory $\mu'$ such that the state is the prescribed count-sort state, $\mu'$ agrees with the initial memory outside the destination and counter ranges, and $R(\mu')$ holds. Keep the same parameters and memory. The agreement condition is unchanged, and the assumed implication $R(\mu')\Rightarrow R'(\mu')$ supplies the new memory property. Thus these same witnesses establish the desired state condition.
