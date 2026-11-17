<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_catalogMarker_cases -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cases for the Last True Bit

**Claim.** Every finite Boolean word either has no true bit and its cut at the last true bit is undefined, or has a last true bit and a corresponding cut $u$ such that the cut of every prefix followed by the word is defined and equals that prefix followed by $u$.

**Proof.** Use induction by removing the final bit. For the empty word, there is no true bit and the cut is undefined. Suppose the word is $v$ followed by one bit. If that bit is false, appending it does not change whether a true bit occurs or the cut determined by the last true bit. Thus whichever alternative holds for $v$ also holds after appending the false bit; in the case with a cut, the prefix identity follows from the induction hypothesis and associativity of concatenation. If the final bit is true, it is the last true bit, so the cut is exactly $v$. For any prefix $pre$, the last true bit of $pre$ followed by $v$ followed by true is still that final bit, and the resulting cut is $pre$ followed by $v$.
