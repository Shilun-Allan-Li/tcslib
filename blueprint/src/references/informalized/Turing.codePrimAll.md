<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/MathlibBridge.lean :: Turing.codePrimAll -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Primitive Recursiveness of the All-True Test

**Claim.** The Boolean-valued function on finite Boolean strings that returns true exactly when every entry is true is primitive recursive.

**Proof.** The list fold operation is primitive recursive when its step and initial value are primitive recursive. Apply this to the Boolean operation that takes a list element and an accumulated Boolean and returns their conjunction, with initial value true. The resulting fold computes the all-true test: on the empty list it is true, and on a list with head $b$ and tail $xs$ it is $b$ conjoined with the fold of $xs$. Induction on the list verifies that this fold is exactly the test that every entry is true. Therefore the all-true test is primitive recursive.
