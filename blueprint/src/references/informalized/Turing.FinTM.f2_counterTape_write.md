<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_counterTape_write -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Writing the Counter Tape

**Claim.** For Boolean lists $u$ and $v$, updating the tape of $u$ followed by $v$ at position $|u|$ to the value $c$ yields the tape of $u$ followed by $c$ and then the tail of $v$.

**Proof.** Compare the two tape functions at an arbitrary integer position. At position $|u|$, the read lemma identifies the old tape value with the head of $v$; updating it to $c$ agrees with the new list, whose entry there is $c$. At a negative position both tapes have no value. At any other nonnegative position, if it lies before the boundary $|u|$, both lists return the same entry from $u$. If it lies beyond the boundary, the concatenation indexing rule identifies the old entry with the corresponding entry of $v$ after its head, which is exactly the entry in the new tail. Thus the functions agree at every position.

**Key facts.** `Turing.FinTM.f2_counterTape_read`.
