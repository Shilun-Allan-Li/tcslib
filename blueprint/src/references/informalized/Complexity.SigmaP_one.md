<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/PolyHierarchy/Levels.lean :: Complexity.SigmaP_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# The First Existential Level

**Claim.** The class $\Sigma_1^P$ equals $\mathsf{NP}$, the class of languages whose membership has polynomial-length certificates verifiable in polynomial time.

**Proof.** For the first inclusion, represent a language in $\Sigma_1^P$ using a polynomial-time predicate and a certificate of the prescribed polynomial length. A machine can split an input formed by concatenating the instance and its certificate, then encode the two pieces in the paired form used by the alternating definition (`computesFunInTime_splitSolve`). Taking the preimage of the original polynomial-time language under this split-and-encode computation keeps the verifier in $\mathsf P$ (`preimage_mem_P`). The one existential quantifier in the definition of $\Sigma_1^P$ is exactly the certificate quantifier (`altQuant_true_succ`); for certificates of the prescribed length, the split encoding agrees with the paired encoding (`certSplit_append`). This gives an $\mathsf{NP}$ description. Conversely, start with an $\mathsf{NP}$ certificate predicate and use as the $\Sigma_1^P$ base language the preimage under the polynomial-time operation that concatenates the two decoded components (`polyTimeComputable_pairConcat`, `preimage_mem_P`). Again, the one existential quantifier is the same certificate condition (`altQuant_true_succ`), and decoding the paired instance and certificate recovers their concatenation. Thus the two classes contain one another.

**Key facts.** `Turing.FinTM.computesFunInTime_splitSolve`, `Complexity.preimage_mem_P`, `Complexity.altQuant_true_succ`, `Complexity.certSplit_append`, `Complexity.polyTimeComputable_pairConcat`.
