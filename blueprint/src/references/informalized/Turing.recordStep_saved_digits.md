<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean :: Turing.recordStep_saved_digits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Saved Counter Digits

**Claim.** If $w$ represents the all-ones word of width $|w|$ and $q+1<2^{|w|}$, then complementing the word obtained after $q+1$ fixed-width decrements of $w$ gives the width-$|w|$ binary digit list of $q+1$.

**Proof.** The all-ones value hypothesis implies $q+1$ is at most the value of $w$. Therefore the value formula for repeated counter decrements applies (`counterWord_value`): the resulting word has value $2^{|w|}-1-(q+1)$. The complement-value identity (`recordStep_complement_value`) then shows that the complemented word has value $q+1$, using that the decremented word retains width $|w|$ (`counterWord_length`). Since $q+1<2^{|w|}$, the unique width-$|w|$ Boolean digit list with value $q+1$ is `binDigits w.length (q+1)` (`recordStep_word_of_value`). This is the desired equality.

**Key facts.** `Turing.counterWord_value`, `Turing.recordStep_complement_value`, `Turing.counterWord_length`, `Turing.recordStep_word_of_value`.
