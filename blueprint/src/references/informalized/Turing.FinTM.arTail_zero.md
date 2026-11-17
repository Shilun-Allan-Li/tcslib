<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction.lean :: Turing.FinTM.arTail_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial write-sweep family

**Claim.** At counter $0$, the write-sweep family is the blockwise coding of the tape obtained by updating $t$ at $p$ to $w$.

**Proof.** Fix a position $z$ and block offset $j$. At counter zero the threshold $0\le j$ always holds, so the replacement clause applies exactly when $z=p$. If $z=p$, the entry is $E(w)_j$; otherwise it is $E(t(z))_j$. These are precisely the entries obtained by first updating the tape at $p$ and then coding each symbol with $E$, so the families agree pointwise.
