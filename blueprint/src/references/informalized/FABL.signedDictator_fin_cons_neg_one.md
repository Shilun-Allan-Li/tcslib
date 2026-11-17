<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/FKNImprovement.lean :: FABL.signedDictator_fin_cons_neg_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Signed Dictator Under Coordinate Extension

**Claim.** Extending $x$ by placing $-1$ first makes the signed dictator equal to the negative of its value on the vector formed by placing $1$ first and negating every coordinate of $x$.

**Proof.** Negating the vector with first coordinate $-1$ and remaining coordinates $x$ gives the vector with first coordinate $1$ and remaining coordinates $-x$. The signed dictator changes sign under global negation (the fact that negating every input coordinate negates its value, `signedDictator_neg_input`). Thus its value on the first extended vector is the negative of its value on the second. The coordinate identity follows by checking the first coordinate and then each of the remaining coordinates.

**Key facts.** `FABL.signedDictator_neg_input`.
