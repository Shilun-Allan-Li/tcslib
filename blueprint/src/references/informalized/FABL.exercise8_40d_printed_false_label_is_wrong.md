<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveNANDComposition.lean :: FABL.exercise8_40d_printed_false_label_is_wrong -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Depth-one false-output cost

**Claim.** For the randomized decision tree from the recursive NAND construction at depth one, the output-conditional cost for output $1$ is not $3/2$.

**Proof.** The depth-one false-output cost is exactly $2$ (\texttt{FABL.recursiveNandFalseOutputCost\_one}). Since $2\ne3/2$, the asserted inequality follows.

**Key facts.** `FABL.recursiveNandFalseOutputCost_one`.
