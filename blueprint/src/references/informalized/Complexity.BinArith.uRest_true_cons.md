<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Loops.lean :: Complexity.BinArith.uRest_true_cons -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial True Bit Is Ignored

**Claim.** For every finite bit string $w$, the unary-rest transducer has the same output on $1w$ as on $w$: $uRest(1w)=uRest(w)$.

**Proof.** By the definition of the transducer, the initial true bit contributes the output prescribed by the initial state and true input, and then the state updates to the state obtained by applying the transition map to that pair. Here the initial state is false: the output is empty, since the output map emits only when the state is true, and the new state is false since $\mathrm{false}\lor\neg\mathrm{true}=\mathrm{false}$. Thus processing the first bit leaves exactly the original state and emits nothing. The remaining input is $w$, so its output is precisely $uRest(w)$.
