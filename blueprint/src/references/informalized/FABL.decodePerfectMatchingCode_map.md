<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.decodePerfectMatchingCode_map -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decoding commutes with relabelling

**Claim.** Applying a map to every vertex before decoding a perfect-matching code gives the same result as applying that map to both endpoints of every decoded pair.

**Proof.** Proceed by induction on the order $m$, allowing the vertex list to vary. At order zero, decoding returns the empty list, so the identity holds. For the successor case, write the code as $(j,c')$ and split the vertex list into its first entry $x$ and tail $xs$. If the tail has no entry at position $j$, both decodings are empty. Otherwise let the entry there be $y$. Mapping the list preserves whether that indexed entry exists, and when it exists its image is $f(y)$. Thus the first decoded pair maps from $(x,y)$ to $(f(x),f(y))$. Removing the selected entry commutes with mapping the list, so the induction hypothesis applied to the shorter tail identifies the remaining decoded pairs. Together these give the required equality.
