<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CNFReductions.lean :: FABL.length_tseitinLiftLiterals -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lifted literal list length

**Claim.** The lifted literal list has length equal to the width of the original term.

**Proof.** Lifting applies a coordinate-preserving literal map to every entry of the term’s literal list. Mapping a list preserves its length, and the width of the term is defined to be the length of that literal list. Hence the lifted list has length equal to the width.
