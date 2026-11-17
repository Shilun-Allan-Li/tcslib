<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerMachineParse.lean :: Complexity.Meyer.readField_eq_some -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Structure of a Successfully Read Field

**Claim.** If reading a field from $s$ returns $(w,r)$, then some bit $e$ satisfies $s=\operatorname{fcode}(w)\mathbin{++}[e,0]\mathbin{++}r$.

**Proof.** Induct on the recursive structure of the successful read, allowing the returned word and remainder to vary. In the recursive case, $s$ begins with $b,1$ and the read continues on the remaining suffix, prepending $b$ to the returned word. The induction hypothesis expresses that suffix as the field code of the remaining word, followed by a bit, the delimiter, and the remainder. Restoring the prefix $b,1$ extends the field code by exactly the code for the bit $b$, yielding the required form. In the terminating case, the read sees a pair consisting of an arbitrary bit $e$ followed by the delimiter $0$; the returned word is empty and the remaining suffix is $r$, so the claimed decomposition holds directly. Any other input pattern cannot produce a successful read, so there is no further case to prove.
