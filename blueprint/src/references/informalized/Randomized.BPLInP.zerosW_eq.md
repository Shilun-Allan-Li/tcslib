<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BPLInPWords.lean :: Randomized.BPLInP.zerosW_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output of the zero transducer

**Claim.** On every finite Boolean word $w$, the transducer that emits false on each input bit outputs the word of false entries of length $|w|$.

**Proof.** Induct on $w$. On the empty word, the transducer emits nothing, as does the empty replicate list. For $w=b::w'$, the transducer emits the single value false for the first bit, then continues on $w'$. By the induction hypothesis the remaining output consists of $|w'|$ false entries. Prepending false gives exactly the replicate list of length $|w'|+1=|w|$.
