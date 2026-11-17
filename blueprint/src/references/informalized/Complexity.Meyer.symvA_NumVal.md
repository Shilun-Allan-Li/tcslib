<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerSound.lean :: Complexity.Meyer.symvA_NumVal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Symbolic Valuation Agreement

**Claim.** Evaluating the symbolic-answer atom under the numerical valuation gives the same optional Boolean value as querying the answer table at the time and position represented by the labels.

**Proof.** Unfold both sides. The symbolic valuation tests the Boolean value of the atom with the positive sign; if it is true, it returns `none`, and otherwise it returns the value of the atom with the negative sign. By the definition of `NumVal`, these two atom values are precisely the corresponding table answers at `tvOf W t T` and `avOf a j A`. This is exactly the definition of the table-based optional answer, so the two expressions agree.
