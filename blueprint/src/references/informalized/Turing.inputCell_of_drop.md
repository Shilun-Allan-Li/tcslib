<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/InputDevice.lean :: Turing.inputCell_of_drop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input Cells After Dropping a Prefix

**Claim.** If deleting the first $\ell$ symbols of $z$ gives $y$, then for each nonzero index $i$, the input cell at index $i$ in $y$ equals the input cell at index $\ell+i$ in $z$, interpreting out-of-range indices as blank.

**Proof.** Replace $y$ by $z.drop\,\ell$ using the hypothesis. Since $i\ne0$, the input-cell definition reads the list at index $i-1$. The shifted index $\ell+i$ is also nonzero, so its input-cell value is the element of $z$ at index $\ell+i-1$. The list indexing formula for a dropped prefix identifies $(z.drop\,\ell)[i-1]?$ with $z[\ell+(i-1)]?$; the two indices agree because $\ell+i-1=\ell+(i-1)$. This equality also covers indices outside the list, where both optional lookups return no symbol.
