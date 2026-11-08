<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean :: Turing.recordStep_digits_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successor and Predecessor of Fixed-Width Digits

**Claim.** If $n+1<2^w$, incrementing the fixed-width little-endian representation of $n$ gives the representation of $n+1$, and decrementing the representation of $n+1$ gives that of $n$.

**Proof.** The proof first identifies the fixed-width word for $n+1$ and then proves the decrement statement. The value theorem for the digit list (`Turing.record_digits_value`) says that the representation of $n+1$ has value $n+1$. Decrementing a binary word by one subtracts one from its value (`Turing.counterWord_value`); the length is preserved (`Turing.counterWord_length`). Hence the decremented word has length $w$ and value $n$. Uniqueness of the length-$w$ representation (`Turing.recordStep_word_of_value`) identifies it with the representation of $n$. The decrement operation returns an optional word, so the proof also rules out the `none` case: if decrement returned none, its default value would force the two fixed-width representations to be equal, contradicting injectivity of fixed-width binary digits (`Turing.record_digits_inj`) since $n+1\ne n$. Thus decrement returns exactly the representation of $n$. Finally, for any word whose decrement is the word $v$, incrementing $v$ recovers the original word: induction on the word verifies this inverse relation, distinguishing whether its first digit is true or false. Applying that fact to the established decrement equality proves the increment assertion.

**Key facts.** `Turing.record_digits_value`, `Turing.counterWord_value`, `Turing.counterWord_length`, `Turing.recordStep_word_of_value`, `Turing.record_digits_inj`.
