<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LowDegreeSpectralConcentration.lean :: FABL.isKJunta_of_card_relevantCoordinates_toReal_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Boolean Junta from Relevant Coordinates

**Claim.** If at most $r$ coordinates have positive influence on the real-valued sign representation of a Boolean function, then the Boolean function depends on at most $r$ coordinates.

**Proof.** Apply the result that a real-valued function with at most $r$ relevant coordinates is an $r$-junta (\(\texttt{FABL.isKJunta\_of\_card\_relevantCoordinates\_le}\)) to the sign representation. The junta equivalence between a Boolean function and its real-valued sign representation then transfers this conclusion back to the original Boolean function (\(\texttt{FABL.isKJunta\_toReal\_iff}\)).

**Key facts.** `FABL.isKJunta_of_card_relevantCoordinates_le`, `FABL.isKJunta_toReal_iff`.
