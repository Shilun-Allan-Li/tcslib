<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.enumInc_word -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Increment of a Width-Constrained Word

**Claim.** If $i<2^w$, incrementing the width-$w$ little-endian word representing $i$ returns the width-$w$ word representing $i+1$ when $i+1<2^w$, and otherwise returns no result.

**Proof.** The increment specification (`enumInc_spec`) says that a successful increment preserves word length and raises its value by one, while failure occurs exactly when the original value plus one is $2$ to the word's length. The representation facts give length $w$ and value $i$ for the word representing $i$ (`enumWord_length`, `enumWord_value`). If increment fails, the specification therefore gives $i+1=2^w$, so the stated condition for no result follows. If it succeeds with word $v$, then $v$ has length $w$ and value $i+1$. Every length-$w$ word has value less than $2^w$ (`enumValue_lt`), so $i+1<2^w$. The canonical word representing $i+1$ has the same length and value; injectivity of values among equal-length words (`enumValue_injective`) identifies it with $v$.

**Key facts.** `Complexity.enumInc_spec`, `Complexity.enumWord_length`, `Complexity.enumWord_value`, `Complexity.enumValue_lt`, `Complexity.enumValue_injective`.
