<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/StatementCode.lean :: Light.Compiler.length_digitsCode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Digit Code Length

**Claim.** For an integer register $c$ and a finite digit list $L$, the digit code has length $D(L)$, where $D([])=1$, and prepending a zero digit increases the length by one while prepending a nonzero digit increases it by two.

**Proof.** Induct on the digit list. For the empty list, the code is a singleton instruction, matching $D([])=1$. For a list $d::L$, the code consists of the code for $L$, followed by one addition instruction and, when $d\ne 0$, one further addition instruction. By the induction hypothesis the first part has length $D(L)$. Thus the total length is $D(L)+1$ if $d=0$ and $D(L)+2$ otherwise, exactly the defining recurrence for $D(d::L)$.
