<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satRedCfg_input -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input Symbol in a Reduction Frame

**Claim.** In the canonical reduction frame at input position $i$, the symbol read is the $i$-th entry of $x$ when it exists, and is blank otherwise.

**Proof.** The canonical frame stores its input-head position as $i+1$. The input-symbol-at-position fact says that whenever a configuration's stored position has value $i+1$, its read symbol is the optional list entry $x[i]?$. Applying that fact to this frame proves the claim (the displayed position equality follows directly from the frame's definition).

**Key facts.** `Turing.FinTM.inputSymbol_at`.
