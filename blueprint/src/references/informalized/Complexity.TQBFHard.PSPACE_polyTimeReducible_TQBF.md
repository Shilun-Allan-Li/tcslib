<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFHard.lean :: Complexity.TQBFHard.PSPACE_polyTimeReducible_TQBF -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# PSPACE Reduces to TQBF

**Claim.** Every language in PSPACE has a polynomial-time many-one reduction to the language of bit strings whose decoded quantified Boolean formula is true.

**Proof.** Take $L$ in PSPACE. Since PSPACE is contained in NPSPACE ($\texttt{PSPACE_subset_NPSPACE}$), choose a nondeterministic machine and polynomial space bound witnessing that membership. The reduction construction uses the machine to form a quantified Boolean formula encoding the computation; the polynomial-time predicate construction supplies the required formula-building verifier ($\texttt{TQBFHard.polyTimeComputable_predB}$). The resulting reduction map is polynomial-time computable ($\texttt{TQBFHard.polyTimeComputable_redMap}$). For each input $x$, the correctness theorem for this formula says that it is true exactly when $x\in L$ ($\texttt{TQBFHard.truth_redQBF}$). Encoding the constructed formula as a bit string and decoding it recovers that formula ($\texttt{QBF.decode_encode}$), so the encoded output belongs to TQBF exactly when $x$ does. This gives the required many-one reduction.

**Key facts.** `Complexity.PSPACE_subset_NPSPACE`, `Complexity.TQBFHard.polyTimeComputable_predB`, `Complexity.TQBFHard.polyTimeComputable_redMap`, `Complexity.QBF.decode_encode`, `Complexity.TQBFHard.truth_redQBF`.
