<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PreimageHost.lean :: Complexity.LogProg.OIS.index_dec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Safe Decrement of the Encoded Index

**Claim.** From the decrement phase with index $i\le |v|$, the compiled program reaches the query phase with index $i-1$ after finitely many steps, and every earlier configuration satisfies the safety bounds.

**Proof.** The decrement routine theorem `dec_run` applies to the extra tape, initially holding $\operatorname{bits}(i)$ at head position zero. It provides a finite run ending with that tape holding $\operatorname{bits}(i-1)$ at zero, and says that every strictly intermediate configuration has a non-call program state and an extra-tape head between $-1$ and $|\operatorname{bits}(i)|$. Replacing the routine's initial and final register configurations by the encoded configurations is justified by `index_view`; in particular the endpoint is precisely the representation with index $i-1$ in the query phase. For each intermediate configuration, the original tapes remain those of $c$, while the routine's non-call state, tape content, and head position let `index_fragment_safe` establish safety. Its upper head bound is at most $|\operatorname{bits}(|v|+1)|$, since $i\le |v|<|v|+1$ and binary-expansion length is monotone (`length_bits_mono`).

**Key facts.** `Complexity.LogProg.dec_run`, `Complexity.LogProg.OIS.index_view`, `Complexity.LogProg.OIS.index_fragment_safe`, `Complexity.LogProg.length_bits_mono`.
