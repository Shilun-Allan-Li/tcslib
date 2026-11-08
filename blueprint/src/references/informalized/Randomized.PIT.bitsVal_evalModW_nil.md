<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroP.lean :: Randomized.PIT.bitsVal_evalModW_nil -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero Value of the Encoded Evaluation

**Claim.** For every natural number $n$, bit string $R$, and list $P$ of bit strings, evaluating the encoded context formed from $n$, $R$, and $P$ with an empty second component yields a bit string whose binary value is zero.

**Proof.** Apply the characterization of the gate evaluator on an encoded context ($\mathrm{gateRun\_eq}$) with the gate word empty. Its iteration count is the length of that word, hence zero, so the state retains the empty list of computed values. The theorem identifying the evaluator’s output on an encoded state ($\mathrm{runVal\_encState}$) says that this output is the binary encoding of the last computed value, with default value zero when the list is empty. Thus the output is $Nat.bits(0)$, whose binary value is zero by the definition of $bitsVal$.

**Key facts.** `Randomized.PIT.gateRun_eq`, `Randomized.PIT.runVal_encState`.
