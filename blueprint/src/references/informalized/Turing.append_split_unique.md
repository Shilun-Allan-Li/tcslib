<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/ChoiceWords.lean :: Turing.append_split_unique -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniqueness of List Concatenation Split

**Claim.** Suppose $n\mapsto n+f(n)$ is strictly increasing and $x\mathbin{++}u=y\mathbin{++}v$, with $|u|=f(|x|)$ and $|v|=f(|y|)$. Then $x=y$ and $u=v$.

**Proof.** Taking lengths in the concatenation equality gives $|x|+|u|=|y|+|v|$. Using the assumed lengths of the suffixes, this becomes $|x|+f(|x|)=|y|+f(|y|)$. Strict increase makes this function injective, so $|x|=|y|$. Once the two prefixes have equal length, equality of the concatenated lists forces their prefixes to agree and their suffixes to agree, yielding $x=y$ and $u=v$.
