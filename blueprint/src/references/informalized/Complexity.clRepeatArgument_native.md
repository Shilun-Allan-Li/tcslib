<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clRepeatArgument_native -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Repetition Arguments

**Claim.** If the state-word function and the unary clock-word function are polynomial-time computable, then the packed repetition arguments formed from them are polynomial-time computable.

**Proof.** List the component word functions indexed by the $C.k+1$ tapes of the repetition argument. For a state-word tape, the component is $s(x)$ when the tape index is zero and the constant empty word otherwise. The first case is polynomial-time computable by hypothesis; the second is polynomial-time computable because constant functions are computable in linear time (`Turing.FinTM.computesFunInTime_const`) and linear-time computability implies polynomial-time computability (`Complexity.clNative_linear`). The final component is the unary word $1^{N(x)}$, polynomial-time computable by the other hypothesis. Thus every component function is polynomial-time computable. The result that finitely many such component functions can be packed by the field encoding while preserving polynomial-time computability (`Complexity.clNative_fields`) applies to this list. Since that list is exactly the list of components obtained by enumerating the repetition words, the packed output is the required encoding.

**Key facts.** `Turing.FinTM.computesFunInTime_const`, `Complexity.clNative_linear`, `Complexity.clNative_fields`.
