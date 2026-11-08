<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satStreamRound_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preservation of the Length Bound

**Claim.** If the consumed length is at most the input length and the fresh cursor is at most the input length plus the consumed length, then one streaming round preserves both bounds.

**Proof.** Write the two assumptions as $u\le |x|$ and $f\le |x|+u$. If the phase is already finished, the state is unchanged. Otherwise inspect the unconsumed suffix $x.drop\,u$. Its length is $|x|-u$, so the assumed bound guarantees that every consumed bit lies within the input. If the suffix is empty, or begins with a terminator in a phase that consumes it, the consumed length either stays fixed or increases by one; the corresponding new state still satisfies both inequalities. A leading marker in phase $0$ likewise increases the consumed length by one and leaves the fresh cursor fixed. If a literal is parsed, its encoding is a prefix of the suffix: the parser representation theorem (\texttt{Std.Sat.CNF.parseLit_repr}) identifies that suffix with the literal encoding followed by the remainder. Thus the encoded literal length is at most the suffix length. Advancing the consumed length by that encoding length preserves its upper bound by $|x|$, and the fresh-cursor bound follows since the new consumed length does not decrease. In the special phase-$3$ case, the fresh cursor also increases by one; the encoding of any literal has positive length, so the increase in consumed length covers that increment as well. If parsing fails, the round finishes without changing either cursor, and the original bounds apply.

**Key facts.** `Std.Sat.CNF.parseLit_repr`.
