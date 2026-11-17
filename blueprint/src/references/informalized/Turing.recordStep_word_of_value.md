<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean :: Turing.recordStep_word_of_value -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Word Determined by Its Value

**Claim.** A Boolean word of length $|w|$ whose least-significant-digit-first value is $n<2^{|w|}$ is the length-$|w|$ binary digit list of $n$.

**Proof.** Map each Boolean entry to its natural-number digit. This map is injective on Booleans, so it suffices to show that the resulting natural-number digit lists agree. Uniqueness of base-$2$ digit expansions of equal length (`Nat.ofDigits_inj_of_len_eq`) applies: both lists have length $|w|$, and every digit in either list is less than $2$. Their values agree because the given list has value $n$, while the canonical test-bit list has value $n$ by the binary-digit value identity (`Turing.record_digits_value`), using $n<2^{|w|}$. Thus the digit lists, and hence the original Boolean words, are equal.

**Key facts.** `Turing.record_digits_value`.
