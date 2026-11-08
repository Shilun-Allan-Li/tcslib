<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeFormat.lean :: Turing.CodeFormat.parseFull_sound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Soundness of Full Parsing

**Claim.** If parsing a bit string $x$ succeeds with output code $M$ and remainder $t$, then $x$ is the serialization of $M$ followed by $t$.

**Proof.** Unfolding the parser, success supplies a pair-decoding result $(\mathrm{bits},\mathrm{rest})$, and rules out failure of the binary consistency check. Thus $\mathrm{bits}$ is exactly the binary representation of the decoded state bound. Success also supplies a valid initial state and remainder $r_1$ from reading its unary code, followed by a successful table read producing a table and remainder $t$. The parser's final result identifies its assembled code with $M$ and its final remainder with $t$. The table reader's soundness says that its input is the table bits followed by $t$. The finite-state reader's soundness says that its input is the unary encoding of the initial state followed by that table input (`codeReadFin_sound`). Likewise, a successful pair decoding reconstructs the original string as the pair encoding of its two components (`eq_pairEncode_of_pairDecode`). Combining these decompositions shows that $x$ is the pair encoding of the binary state bound and the unary initial-state code followed by the table bits and $t$. The binary consistency equality ensures that this is precisely the serialization of the assembled code; since that code is $M$, the result follows.

**Key facts.** `Turing.eq_pairEncode_of_pairDecode`, `Turing.codeReadFin_sound`.
