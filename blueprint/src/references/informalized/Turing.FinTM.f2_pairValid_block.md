<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_pairValid_block -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pair Validity on One Block

**Claim.** Starting in the parser's initial scanning state just before the bits $b,c$, after two steps the head is two positions farther along. If $b=c$, the machine remains in its scanning state with empty output; otherwise it halts and outputs $[\neg b\land c]$.

**Proof.** Use the scan-step lemma on the first bit $b$: the machine advances one position, emits nothing, and enters the state that remembers $b$ (`Turing.FinTM.f2_scanStep_right`). Apply it again to the next bit $c$. If $b=c$, this second step emits nothing and returns to the initial scanning state. If they differ, it halts and emits $\neg b\land c$, which is true precisely in the case $b=0,c=1$. In either case the two rightward moves place the head two positions beyond its starting point. The stated configuration follows by splitting on whether $b=c$.

**Key facts.** `Turing.FinTM.f2_scanStep_right`.
