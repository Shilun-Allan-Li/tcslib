<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/UPathRL.lean :: Complexity.LogProg.ups_start -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial Unary Program Semantics

**Claim.** Under the stated zero-probability condition for malformed inputs and the walk-probability condition for valid symmetric encodings, the program started in its initial state with all registers zero has the stated termination, register bound, and acceptance probability.

**Proof.** Set $B=200(|x|+1)^4$. The elementary estimates $2|x|+2\le B$ and, for every $n\le |x|$, $100n^4+10n\le B$ provide the space bounds used throughout.

1. The initial unary scan either finds the unary delimiter and determines an encoded vertex count $n$, or finds no valid unary suffix. In the latter case the assumed zero-probability condition supplies $q=0$. In the former, the unary suffix determines $n$ uniquely (`unaryRest_unique`), and the scan proceeds to the matrix portion. The unary scan’s two outcomes and its continuation are packaged by `ups_unary`.

2. The matrix scan similarly either establishes the required matrix encoding or fails, in which case the input is not a valid graph encoding and the assumed zero-probability condition applies. Once the matrix is established, the program copies the relevant pointer and counters into the row-checking stage. The matrix scan’s correctness and failure alternatives are expressed by `ups_mat`, and the register copy is justified by `ups_cp`.

3. The row check verifies symmetry of the encoded edge relation. If it fails, there is no valid symmetric encoding, so the acceptance probability is zero by hypothesis. If it succeeds, it supplies symmetry for every pair of vertices and continues with the encoded start vertex. This step is captured by `ups_yrow`; the input pattern ensures that the encoded indices are within the input’s length.

4. The start-vertex search finds the binary encoding of some candidate vertex $j$ in the doubled portion of the input. A successful match provides the start index and pointer needed for the target search. If no such match exists, the input cannot be a valid unary graph encoding, so the failure hypothesis again gives probability zero. The search invariant is `ups_ssearch`; the uniqueness of a doubled encoding (`dblAt_unique`) identifies the decoded index, while `bits_injective` identifies its natural-number value.

5. With $j$ fixed, the target search finds the plain binary encoding of a vertex $t$ at the end of the input. If it finds no such index, the input is not a valid encoding and the acceptance probability is zero. Otherwise the two decoded endpoints, together with the unary and matrix portions, form a valid shape with symmetric edge relation. The search invariant is `ups_tsearch`.

6. The program then initializes the walk length and invokes its walk routine. The length scan and initialization are justified by `ups_len`; its numerical work bound follows from the chosen $B$. The walk routine returns the probability that a uniformly random walk of length $100n^4$ in the padded regular multigraph, started at $j$, visits $t$ (`ups_walk`). The assumed equation for valid encodings identifies this probability with $q$. The program’s register state is then reconciled with the desired one, and equality of the probabilities is transported by `PSem.congr`.

At each scan or search stage, the no-witness branch is discharged using the corresponding failure hypothesis and uniqueness of the previously identified encoding; thus the proof covers malformed inputs as well as valid ones.

**Key facts.** `Complexity.LogProg.ups_unary`, `Complexity.unaryRest_unique`, `Complexity.LogProg.ups_mat`, `Complexity.LogProg.ups_cp`, `Complexity.LogProg.ups_yrow`, `Complexity.LogProg.ups_ssearch`, `Complexity.dblAt_unique`, `Complexity.LogProg.bits_injective`, `Complexity.LogProg.ups_tsearch`, `Complexity.LogProg.ups_len`, `Complexity.LogProg.ups_walk`, `Complexity.LogProg.PSem.congr`.
