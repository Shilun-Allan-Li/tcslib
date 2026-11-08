<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/AC0ThresholdParitySeparation.lean :: FABL.blockMinterm_eval_eq_neg_one_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of a block minterm

**Claim.** The block minterm evaluates to $-1$ exactly when its assignment agrees at every position with the input restricted to the block coordinates indexed by $b$.

**Proof.** A term evaluates to $-1$ exactly when every literal in it is satisfied, meaning that the input at each literal's coordinate equals its required sign (`FABL.DNFTerm.eval_eq_neg_one_iff`). The block minterm has one literal for each position $j$, with coordinate given by the block coordinate map and required sign $a(j)$. Thus evaluation to $-1$ says, for every $j$, that $x$ at that block coordinate equals $a(j)$. This is precisely the pointwise equality of $a$ with the restriction of $x$ to those coordinates.

**Key facts.** `FABL.DNFTerm.eval_eq_neg_one_iff`.
