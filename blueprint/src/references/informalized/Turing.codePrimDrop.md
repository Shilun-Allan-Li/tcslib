<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/MathlibBridge.lean :: Turing.codePrimDrop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Primitive Recursiveness of Suffix Removal

**Claim.** The operation taking a finite Boolean string and a natural number $n$ to the string obtained by removing its first $n$ entries is primitive recursive.

**Proof.** Begin with the original string, and iterate the operation that removes the first entry exactly $n$ times. The list-tail operation is primitive recursive, so natural-number iteration gives a primitive recursive function of the string and the iteration count. To identify this iterate with suffix removal, induct on $n$, allowing the input string to vary. At $n=0$ no entries are removed. In the successor case, removing one entry first and then applying the induction hypothesis removes the required number of entries; if the string is empty, both sides are empty, and if it is nonempty, the list equations give the result.
