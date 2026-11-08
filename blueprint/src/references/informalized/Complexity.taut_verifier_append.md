<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Tautology.lean :: Complexity.taut_verifier_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Verifier on a Sized Concatenation

**Claim.** If $|u|=|x|+1$, then $x++u$ belongs to the verifier language exactly when the DNF formula decoded from $x$ evaluates to false under the assignment read from $u$, with variables beyond $u$ assigned false.

**Proof.** Set the split point to $|x|$. The length hypothesis gives $|x|+(|x|+1)=|x++u|$, so the split-solving lemma says the verifier’s split search returns exactly this point. Taking and dropping at that point recover $x$ and $u$, respectively. Thus the verifier’s bit is the negation of the decoded formula’s evaluation on the assignment from $u$; it equals true precisely when that evaluation is false.

**Key facts.** `Complexity.taut_split_exists`.
