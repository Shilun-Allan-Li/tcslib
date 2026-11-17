<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/Cells.lean :: Light.Compiler.Rel.beyond -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preservation of the Memory Relation

**Claim.** If a memory satisfies the relation for $Z$, $\sigma$, and $q$, with $1\le q$, then any memory agreeing with it outside the scratch addresses and the specified upper stack addresses also satisfies that relation.

**Proof.** Apply the general agreement-outside preservation result for the memory relation (Light.Compiler.Rel.of_agreeOutside). Its hypotheses require that the exceptional address set avoid all constant addresses, and that the new memory retain the encoded frame pointer, local-variable, and ordinary-memory values. The set of scratch addresses together with stack addresses indexed from $q+F$ up to but not including $Q$ avoids the constants. Since $1\le q$, every address used for the frame pointer or a local variable lies outside this exceptional set; every ordinary memory address also lies outside it. Agreement therefore transfers the corresponding stored values from $m$ to $m'$, supplying the required frame-pointer and storage conditions. The result follows with the same state and frame pointer.

**Key facts.** `Light.Compiler.Rel.of_agreeOutside`, `WordRAM.AgreeOutside.read`.

**Caveat.** The supplied upstream statement of Rel.of_agreeOutside is parameterized by a possibly changed state and frame pointer; the proof specializes both to the original $\sigma$ and $q$. The omitted address-set arithmetic is packaged in the proof as `by cells`.
