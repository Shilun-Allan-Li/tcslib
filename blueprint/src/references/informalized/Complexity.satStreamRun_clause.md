<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satStreamRun_clause -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Streaming Schedule for a Clause

**Claim.** Starting at phase $1$ just before an encoded clause, exactly $|C|+1$ rounds emit the prescribed clause body and finish in phase $0$, with the consumed length and fresh cursor specified by the clause-body construction.

**Proof.** Proceed by cases on the clause. For the empty clause, its encoding is just the terminator. The terminator-round rule (\texttt{Complexity.satStreamRound_false}) consumes it and emits $[0]$, which is exactly the clause-body output; the run has one round and ends in phase $0$. For a nonempty clause, write it as $a::C$. The first literal-round rule (\texttt{Complexity.satStreamRound_literal}) applies in phase $1$: it emits the encoding of $a$, leaves the fresh cursor at $j$, and moves to phase $2$. Split further on $C$. If $C$ is empty, the next bit is the clause terminator, so the terminator-round rule consumes it, emits $[0]$, and moves from phase $2$ to phase $0$. Together these two rounds emit the encoding of $a$ followed by the terminator, exactly the prescribed body for a singleton clause. If $C=b::C'$, the next literal-round rule applies in phase $2$, emits the encoding of $b$, keeps the fresh cursor fixed, and moves to phase $3$. The remaining run is precisely the schedule for $C'$ from phase $3$ (\texttt{Complexity.satStreamRun_tail}). Its output and final cursor supply the tail portion of the clause-body construction. In both subcases, the consumed-length updates add the lengths of the successive literal encodings and the final terminator, hence total $|p|+|\operatorname{serializeClause}(C)|$; the number of rounds is one per literal plus one for the terminator, and the final phase is $0$.

**Key facts.** `Complexity.satStreamRound_false`, `Complexity.satStreamRound_literal`, `Complexity.satStreamRun_tail`.
