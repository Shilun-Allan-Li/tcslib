<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveNANDComposition.lean :: FABL.eval_nandContinuationTree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# NAND Continuation Tree Evaluation

**Claim.** The continuation tree formed from a sign and a sign-output decision tree evaluates to $1$ exactly when both the given sign and the decision tree's output are $-1$; in all other cases it evaluates to $-1$.

**Proof.** A sign is either $1$ or $-1$. If the first sign is $1$, the continuation tree is the constant leaf labelled $-1$, which agrees with the NAND rule because its two inputs cannot both be $-1$. If the first sign is $-1$, the tree is the original decision tree with its output transformed by the pairwise NAND rule. It therefore evaluates to $1$ precisely when the original tree outputs $-1$, and to $-1$ otherwise. Together the cases give the asserted evaluation.
