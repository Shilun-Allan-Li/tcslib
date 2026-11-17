<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LowDegreeSpectralConcentration.lean :: FABL.isKJunta_toReal_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Juntas are preserved by real encoding

**Claim.** The real sign representation of a Boolean function depends on at most $r$ coordinates if and only if the Boolean function itself does.

**Proof.** For either direction, take a set of at most $r$ coordinates witnessing the junta property. The fact that dependence on a given coordinate set is equivalent before and after applying the real sign encoding (\texttt{dependsOn\_toReal\_iff}) transfers the dependence property across the encoding. The same coordinate set and its cardinality bound therefore witness the other junta property.

**Key facts.** `FABL.dependsOn_toReal_iff`.
