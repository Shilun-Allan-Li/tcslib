<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/OracleSim.lean :: Turing.FinTM.prefixWords_update -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating a Padded Word Family

**Claim.** For $k\le k'$, extending a family that is empty except for the word $u$ at index $i<k$ gives the larger family that is empty except for $u$ at the corresponding index.

**Proof.** Compare the two functions at an arbitrary index $j<k'$. If $j<k$, both families address the same index in the original range. When $j=i$, each update returns $u$; when $j\ne i$, each returns the original empty value. If $j\not<k$, prefix extension itself returns the empty word. Also $j$ cannot be the image of $i$, since that image has value $i<k\le k'$, and equality would force $j=i<k$. Therefore the updated larger family is empty there as well. The functions agree at every index.
