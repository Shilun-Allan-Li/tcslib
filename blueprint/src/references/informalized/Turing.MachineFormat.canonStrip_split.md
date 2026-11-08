<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeSimulator.lean :: Turing.MachineFormat.canonStrip_split -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Trailing-one decomposition

**Claim.** Every Boolean word is the concatenation of its prefix obtained by removing all trailing ones and a string of some number of ones; that prefix is empty or ends in zero.

**Proof.** Induct on the word by building it from the right. The empty word has the claimed form with zero trailing ones and empty prefix. Suppose the claim holds for $w$, and append a bit. If the bit is $0$, removing trailing ones from $w ++ [0]$ leaves the whole word, which ends in $0$, so take zero trailing ones. If the bit is $1$, removing trailing ones leaves the same prefix as for $w$; append one more $1$ to the trailing block. The prefix condition is inherited from the induction hypothesis.
