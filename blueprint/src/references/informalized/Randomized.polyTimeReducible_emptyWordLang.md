<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BPPEqP.lean :: Randomized.polyTimeReducible_emptyWordLang -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reduction to the Empty-Word Language

**Claim.** Every language in polynomial time is polynomial-time many-one reducible to the language consisting only of the empty word.

**Proof.** The empty-word language contains $a=[]$ and omits $b=[	ext{true}]$. Apply the constant-yes/no reduction theorem to the target language $L'$, which is in $	extsf P$: map an input to $a$ when it belongs to $L'$, and to $b$ otherwise. This map is polynomial-time computable, and its output belongs to the empty-word language exactly when the original input belongs to $L'$. Thus it is the required many-one reduction (`Randomized.polyTimeReducible_of_mem_P`).

**Key facts.** `Randomized.polyTimeReducible_of_mem_P`.
