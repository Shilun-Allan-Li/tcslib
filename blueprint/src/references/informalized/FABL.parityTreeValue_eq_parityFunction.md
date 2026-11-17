<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Parity.lean :: FABL.parityTreeValue_eq_parityFunction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parity tree computes full parity

**Claim.** If $n\le r^h$, then the depth-$h$ parity tree value at index $0$ is the product of all coordinates of $x$.

**Proof.** The product formula for a parity tree value (\(FABL.parityTreeValue_eq_prod_fin\)) rewrites its value at depth $h$ and index $0$ as the product of the padded inputs at indices $0,\ldots,r^h-1$. The product identity for padded inputs (\(FABL.prod_paddedParityInput_eq_prod\)) says that whenever $n\le m$, the product of the first $m$ padded inputs is the product of the first $n$ actual coordinates: all factors beyond index $n-1$ are $1$. Apply it with $m=r^h$. Finally, the definition of parity over the full coordinate set identifies that product with the claimed parity.

**Key facts.** `FABL.parityTreeValue_eq_prod_fin`, `FABL.prod_paddedParityInput_eq_prod`.
