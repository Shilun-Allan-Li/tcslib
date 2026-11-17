<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.enumCont_pad_words -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Padding Preserves a One-Word Seam

**Claim.** When $0<k$ and $k\le K$, padding the seam configuration with state $q$ and word $s$ on tape zero gives the seam configuration on the $K$-tape bank with state $\mathrm{emb}(q)$ and the same word on tape zero.

**Proof.** Compare state, input-head position, output, and tape-head positions directly: padding maps the state as specified, preserves the input position and output, and leaves every head at zero. For tape contents, an index below $k$ retains its original contents. In particular, tape zero carries $s$. Every other index below $k$ carries the empty word. An index at least $k$ is newly added and is blank by the definition of padding; since $k>0$, such an index cannot be zero. Therefore the resulting bank has $s$ on tape zero and blanks elsewhere, exactly as required. The bound $k\le K$ ensures the original bank fits in the padded bank.
