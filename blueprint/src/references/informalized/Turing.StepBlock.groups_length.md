<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepBlock.lean :: Turing.StepBlock.groups_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of Flattened Equal-Length Groups

**Claim.** If every list in a finite list of groups has length $3^{k+1}$, then flattening the groups yields a list of length equal to the number of groups times $3^{k+1}$.

**Proof.** Induct on the list of groups. The empty list has flattened length zero, as claimed. For a nonempty list with first group $g$ and remaining groups $G'$, flattening concatenates $g$ with the flattening of $G'$. Its length is therefore $|g|$ plus the length of the latter. The hypothesis gives $|g|=3^{k+1}$, and the induction hypothesis gives $|\mathrm{flatten}(G')|=|G'|3^{k+1}$. Adding these and using $|G|=1+|G'|$ proves the formula.
