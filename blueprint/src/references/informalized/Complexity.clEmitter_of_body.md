<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clEmitter_of_body -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Emission of a CNF Sequence

**Claim.** Under the stated hypotheses, the sequence of CNF formulas $G(x,i)$ for $0\le i\le R(|x|)$, serialized as one concatenation, is computable in polynomial time.

**Proof.** Fix an input $x$. First define an invariant saying that the body machine’s packed word has the form $\mathrm{pack}(x,i)$ for some $i\le R(|x|)+1$. The initial word satisfies this invariant at index zero, and the step rule preserves it by sending index $i$ to $\min(i+1,R(|x|)+1)$. Thus the loop theorem for a body machine that repeatedly returns to an anchor state applies (`Turing.FinTM.exists_emitLoopTM`): the supplied start and round hypotheses give the required initial configuration and bounded, positive-time rounds, with no intervening visits to the anchor. The separate machine $F$ computes the binary representation of $R(|x|)$ within the same polynomial bound. The loop construction therefore produces an emitter whose time is bounded by a constant times the startup and round costs and the number of rounds.

It remains to identify its output and bound its running time polynomially. The cursor-orbit lemma (`Complexity.clCursor_orbit`) shows that on the $i$th round the packed word represents index $\min(i,R(|x|)+1)$; for indices in the output range $i\le R(|x|)$, this is $i$. The emission hypothesis then yields exactly the serialized fragment for $G(x,i)$ on that round. The chunk-serialization identity (`Complexity.clChunks_serialize`) says that concatenating these fragments, with the terminator on the final round, is the serialization of the concatenated CNF sequence. Finally, since both $P$ and $R$ are polynomially bounded, the loop’s time bound is polynomially bounded (`Complexity.clLoop_polyBound`). Monotonicity of computation time (`Turing.FinTM.ComputesInTime.mono`) raises the emitter’s actual time bound to this polynomial bound.

**Key facts.** `Turing.FinTM.exists_emitLoopTM`, `Complexity.clCursor_orbit`, `Complexity.clChunks_serialize`, `Complexity.clLoop_polyBound`, `Turing.FinTM.ComputesInTime.mono`.
