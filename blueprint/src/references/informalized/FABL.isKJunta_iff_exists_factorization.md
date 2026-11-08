<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/SocialChoiceFunctions/Definitions.lean :: FABL.isKJunta_iff_exists_factorization -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Juntas and Coordinate Factorizations

**Claim.** A function is a $k$-junta exactly when there is a set of at most $k$ coordinates and a function of those coordinates whose composition with coordinate restriction equals the original function.

**Proof.** For the forward implication, a $k$-junta supplies a coordinate set of size at most $k$ on which the function depends. The characterization of dependence as factoring through restriction gives a function on the restricted coordinates whose composition with restriction is the original function. Conversely, given such a factorization, the function's value is determined by those coordinates, so it depends on that coordinate set. Its size bound then makes it a $k$-junta.
