<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean :: Turing.record_digits_inj -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniqueness of Bounded Binary Digits

**Claim.** If two natural numbers below $2^w$ have the same lists of their first $w$ binary digits, then the numbers are equal.

**Proof.** For each number, the bounded-digit value theorem (`record_digits_value`) says that converting its list of $w$ binary digits back to a base-two value recovers the original number. Since the two digit lists agree, their converted values agree as well. Thus the original numbers are equal.

**Key facts.** `Turing.record_digits_value`.
