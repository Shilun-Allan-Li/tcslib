<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeParser.lean :: Turing.codeReadVec_sound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Soundness of vector decoding

**Claim.** If the vector reader of length $n$ succeeds on a bit string $x$, returning a vector $f$ and suffix $r$, then $x$ is the concatenation of the encodings of the entries of $f$, in order, followed by $r$.

**Proof.** Proceed by induction on $n$. When $n=0$, the reader returns the unique empty vector and leaves the input unchanged, so success forces $x=r$; this is exactly the empty concatenation followed by $r$. For the successor step, success of the vector reader entails a successful first read, yielding some value $a$ and intermediate suffix $r_1$, followed by a successful read of the remaining vector, yielding its entries and final suffix $r$. The assembled vector has first entry $a$ and remaining entries given by that latter vector. By the assumed soundness of the single-value reader, the original input is the encoding of $a$ followed by $r_1$. By the induction hypothesis, $r_1$ is the concatenation of the encodings of the remaining entries followed by $r$. Combining these equalities and associating the concatenations gives the required encoding of the whole vector followed by $r$.
