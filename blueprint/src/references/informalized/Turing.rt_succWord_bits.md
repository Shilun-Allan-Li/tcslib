<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/RecordTable.lean :: Turing.rt_succWord_bits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Successor Word

**Claim.** For every natural number $n$, the successor word associated with the binary expansion of $n$ is the binary expansion of $n+1$.

**Proof.** Proceed by binary recursion from one, with the zero and one cases checked directly from the definition of the successor word. In the general bit case, split according to the final binary bit. If the number is $2m$, its binary word is obtained by appending a zero to the word for $m$; incrementing changes that final zero to one, giving the binary word of $2m+1$. This is the even-to-odd bit decomposition (`Nat.bit0_bits` and `Nat.bit1_bits`). If the number is $2m+1$, the word has a final one. The successor-word rule for a leading one (`Turing.rt_succWord_cons`) removes that one as a carry and prefixes a zero to the successor word for the remaining part. The induction hypothesis identifies that remaining word with the bits of $m+1$, and the even-bit decomposition then identifies the result with the bits of $2m+2$.

**Key facts.** `Turing.rt_succWord_cons`.
