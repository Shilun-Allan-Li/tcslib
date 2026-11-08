<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/MathlibBridge.lean :: Turing.codePrimBitsNat -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Primitive Recursiveness of Binary Evaluation

**Claim.** The function assigning a finite Boolean string its binary value, with the first bit least significant, is primitive recursive.

**Proof.** The value is defined by folding from the right, starting with $0$ and replacing an accumulated value $m$ by $\operatorname{bit}(m,b)$ for each Boolean $b$. The operation $\operatorname{bit}$ on a natural number and a Boolean is primitive recursive (Turing.codePrimBit). The list-fold recursion principle therefore applies this operation successively to the entries of the input list, with the primitive recursive identity as the list element input and the constant $0$ as the initial value. This gives the claimed primitive recursiveness.

**Key facts.** `Turing.codePrimBit`.
