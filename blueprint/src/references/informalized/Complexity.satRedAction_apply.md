<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satRedAction_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Action on a Reduction Frame

**Claim.** Under the stated hypotheses, applying the two-tape reduction action to the canonical frame with data $(x,q,i,n,B,a,b,o)$ gives the canonical frame with data $(x,q',i',n',B',a',b',o')$.

**Proof.** Configurations are equal once their state, input position, two work tapes, two work-head positions, and output agree. The action sets the state to $q'$, and the input-position hypothesis gives the required new position. For work tape $0$, split according to whether a write is prescribed: without a write its contents stay unchanged, and with a write they are updated at the current head. In either case the assumed tape equality identifies the result with the counter tape of length $n'$. The same two possibilities on work tape $1$, together with its tape hypothesis, give $B'$. Finally, the head positions advance by $d_0,d_1$, so the two head-position equations give $a',b'$, and appending the optional output bit gives $o'$.
