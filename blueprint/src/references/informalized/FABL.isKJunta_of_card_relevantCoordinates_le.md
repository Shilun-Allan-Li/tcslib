<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LowDegreeSpectralConcentration.lean :: FABL.isKJunta_of_card_relevantCoordinates_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Junta from Relevant Coordinates

**Claim.** If at most $r$ coordinates have positive influence on a real-valued function, then the function depends on at most $r$ coordinates.

**Proof.** Take the set of all relevant coordinates, namely those with positive influence. By hypothesis its cardinality is at most $r$. The function depends only on its relevant coordinates (\(\texttt{FABL.dependsOn\_relevantCoordinates}\)); therefore this set witnesses that the function is a junta of size at most $r$.

**Key facts.** `FABL.dependsOn_relevantCoordinates`.
