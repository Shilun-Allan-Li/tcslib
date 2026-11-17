<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/Mult.lean :: Complexity.mult_last_bit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Final-bit processing

**Claim.** For each field $f$ and bounded register assignment, the clearing state reaches the canonical-field read state with register $0$ set to the corresponding source register minus the prescribed offset. It then proceeds to the next canonical-field test when that input bit is $1$, and to the rejecting answer otherwise, while preserving the side conditions and register bound throughout.

**Proof.** Let $s_f$ be the source register selected by $f$, and let $d_f$ be $1$ for the third field and $2$ for the first two. First, the copy routine copies register $s_f$ into register $0$ and enters the downward-counting state; the finite table identity `Complexity.mult_copy` identifies this routine's source, destination, and exit state. Each copied value and subsequent decrement remains within the register bound by the register-update bound lemma. For the third field, one decrement reaches the read state; for either other field, two decrements do so. Thus register $0$ there equals $v(s_f)-d_f$. The oracle-query lemma says that the input-bit oracle on the encoded query returns exactly the bit of $x$ at that index (with zero outside the string). Consequently the read instruction chooses the next canonical-field test if this bit is $1$, and the rejecting answer state if it is $0$. Compose these reachability segments and include the initial clearing instruction; the preconditions lemma supplies the instruction side conditions at each starting configuration.

**Key facts.** `Complexity.LogProg.register_update_le`, `Complexity.mult_copy`, `Complexity.LogProg.AReach.single`, `Complexity.LogProg.AReach.trans`, `Complexity.mult_preconditions`, `Complexity.LogProg.vword_whole₁`, `Complexity.mult_queries`, `Complexity.LogProg.AReach.step`.
