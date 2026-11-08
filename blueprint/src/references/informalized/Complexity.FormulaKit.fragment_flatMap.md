<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/FormulaKit/Emit.lean :: Complexity.FormulaKit.fragment_flatMap -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fragment of a Flattened List

**Claim.** For a finite list $xs$ and a map $G$ assigning a CNF formula over natural-number variables to each element, the fragment of the concatenation of the formulas $G(b)$ in list order is the concatenation, in that order, of their fragments.

**Proof.** Proceed by induction on $xs$. For the empty list, both sides are empty. For a list with first element $b$ and tail $xs$, flattening gives the concatenation of $G(b)$ with the flattening of the tail. By the fragment-concatenation identity (Complexity.FormulaKit.fragment_append), the fragment of this formula is the fragment of $G(b)$ followed by the fragment of the tail's flattened formula. The induction hypothesis identifies the latter with the concatenation of the fragments for the elements of $xs$, which is exactly the required list-order concatenation.

**Key facts.** `Complexity.FormulaKit.fragment_append`.
