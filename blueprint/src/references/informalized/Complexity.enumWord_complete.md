<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.enumWord_complete -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recovery of a Word from Its Value

**Claim.** For every finite Boolean word $u$, the width-$|u|$ little-endian binary word representing its little-endian value is exactly $u$.

**Proof.** The word $u$ and the width-$|u|$ word representing its value have the same length: the latter has length $|u|$ by the fixed-width length property (`Complexity.enumWord_length`). They also have the same value. Indeed, the value of the width-$|u|$ representation is its input number whenever that number is less than $2^{|u|}$ (`Complexity.enumWord_value`), and the needed bound for the value of $u$ is supplied by `Complexity.enumValue_lt`. The injectivity of the little-endian value among words of equal length (`Complexity.enumValue_injective`) therefore identifies the two words.

**Key facts.** `Complexity.enumWord_length`, `Complexity.enumWord_value`, `Complexity.enumValue_lt`, `Complexity.enumValue_injective`.
