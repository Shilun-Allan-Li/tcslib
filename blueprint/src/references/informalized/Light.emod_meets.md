<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/Emod.lean :: Light.emod_meets -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded modular reduction

**Claim.** Under the stated word, space, modulus, and free-memory bounds, the modular-reduction procedure returns $x\bmod M$ within cost $43$ times the binary size of $\lfloor |x|/M\rfloor$ plus $34$, while preserving memory below $fr$.

**Proof.** First use $|x|\le V$ to obtain $x.\mathrm{natAbs}\le V$, and identify the natural absolute value with $|x|$. Split according to the sign of $x$. In either case, initialize the remainder register to $|x|$; the sign determines whether this is done by negating $x$ or by copying it. Initialize the count register to zero and the multiplier register to $M$.

The table phase repeatedly records the current multiplier while it does not exceed the current remainder, then doubles the multiplier. Its execution lemma (`Emod.table_ends`) supplies the resulting table and preserves the memory below $fr$. The reduction phase traverses that table in reverse, subtracting a table entry precisely when it fits in the current remainder. Its execution lemma (`Emod.reduce_ends`) shows that the resulting register is $|x|\bmod M$ and gives the corresponding cost bound. The sign-correction phase converts this nonnegative remainder to the signed remainder of $x$ modulo $M$, without changing memory (`Emod.sign_ends`).

Sequencing these phases and the register initializations gives the tail cost. The sign split and its initial assignment are combined with that tail using the conditional-sequencing lemma (`Ends.iteThen`); the time and postcondition are adjusted by monotonicity where needed (`Ends.mono`). Finally, the procedure body is installed at the specified index to obtain the claimed procedure execution (`Meets.of_body`).

**Key facts.** `Light.Ends.iteThen`, `Light.Emod.table_ends`, `Light.Ends.mono`, `Light.Emod.reduce_ends`, `Light.Emod.sign_ends`, `Light.Ends.next`, `Light.Ends.setToThen`, `Light.Meets.of_body`.
