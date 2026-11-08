<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SipserGacs.lean :: Randomized.zipWith_ofFn -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zip of Indexed Sequences

**Claim.** For sequences $a,b$ indexed by $0,\ldots,m-1$, zipping their lists of values with $f$ gives the list whose entry at each index $i$ is $f(a(i),b(i))$.

**Proof.** The two lists of values and the list formed by applying $f$ pointwise all have length $m$. At each index $i<m$, the entries of the first two lists are respectively $a(i)$ and $b(i)$, so their zipped entry is $f(a(i),b(i))$, exactly the entry at index $i$ in the pointwise list. Equal lengths and equality of corresponding entries give equality of the lists.
