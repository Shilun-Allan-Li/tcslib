<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.codecWord_eq_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of the Boolean Word Encoding

**Claim.** For finite $\alpha$ and $L\ge |\alpha|$, the length-$L$ Boolean words encoding $a,b:\alpha\to\{\mathrm{false},\mathrm{true}\}$ are equal exactly when $a=b$.

**Proof.** Suppose the two encoded lists are equal. For any $i\in\alpha$, read both lists at the position assigned to $i$ by the enumeration of $\alpha$. The recovery property `codecWord_get` says these entries are respectively $a(i)$ and $b(i)$. Equality of the lists gives equality of the entries, so $a(i)=b(i)$ for every $i$, hence the functions agree. Conversely, if $a=b$, their encodings are equal because the encoding is defined pointwise from the function.

**Key facts.** `Complexity.codecWord_get`.
