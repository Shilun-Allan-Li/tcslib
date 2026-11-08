<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean :: Complexity.drop_lookup -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lookup from the Search State

**Claim.** From the specified search state and register values, the machine halts with the length test in true mode and otherwise with the queried bit of the transformed nested encoding, defaulting to false, while satisfying safety and the register bound.

**Proof.** Write $n=2|w|+2$ and let $out=dropIdx(\langle\langle w,b\rangle,b'\rangle)$. Decoding the nested pairing identifies $out$ with $\langle w,b'\rangle$, whose length is $n+|b'|$ by the pairing length formula (`Complexity.dropIdx_pairEncode`, `Turing.length_pairEncode`). The search procedure first scans the prefix of length $n$ (`Complexity.drop_seek_run`). If $q<n$, it reaches the hit state at the address for the corresponding prefix bit. The prefix-address identity shows that this address reads the bit of $out$ at $q$ (`Complexity.dropIdx_prefix_address`). The hit-state lemma supplies the answer and halting guarantee (`Complexity.drop_hit`), and the register bound after the address updates follows by the register-update bound (`Complexity.LogProg.register_update_le`).

If $q\ge n$, the first scan moves the machine to the suffix search, after copying the relevant boundary register. The copy-run lemma justifies that transition and its register update (`Complexity.drop_copy_run`). If $q<n+|b'|$, the suffix scan reaches the hit state at the appropriate suffix address; the suffix-address identity identifies that input bit with the bit of $out$ at $q$ (`Complexity.dropIdx_suffix_address`). Again the hit-state lemma yields the requested result. If $q\ge n+|b'|$, the suffix is exhausted, so the queried bit defaults to false and the length test is false; the machine returns false from its answer state (`Complexity.drop_ret`). In each branch, the search runs are concatenated with the hit or return halting run (`Complexity.LogProg.AReach.trans`, `Complexity.LogProg.AReach.halt`), and register bounds are maintained using `Complexity.LogProg.register_update_le`.

**Key facts.** `Complexity.dropIdx_pairEncode`, `Turing.length_pairEncode`, `Complexity.drop_seek_run`, `Complexity.dropIdx_prefix_address`, `Complexity.LogProg.register_update_le`, `Complexity.drop_hit`, `Complexity.drop_copy_run`, `Complexity.dropIdx_suffix_address`, `Complexity.drop_ret`, `Complexity.LogProg.AReach.trans`, `Complexity.LogProg.AReach.halt`.
