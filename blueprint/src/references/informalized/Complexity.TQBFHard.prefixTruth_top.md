<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFHardSemantics.lean :: Complexity.TQBFHard.prefixTruth_top -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Characterizing the Top-Level Prefix

**Claim.** The top-level quantified formula is true exactly when there are length-$w$ words $A,B$ satisfying $I(A)$ and $J(B)$ and related by the $R$-level midpoint relation.

**Proof.** Compress the three initial existential blocks into words $z,a,b$, each of length $w$. The matrix only uses $a$ and $b$: on assignments agreeing with the written assignment below position $3w$, the blocks read at positions $w$ and $2w$ are precisely $a$ and $b$. Indeed, each block is read from its own written interval, while later writes leave earlier positions unchanged (`readBlock_eq'`, `writeBlock_of_lt`, `writeBlock_of_mem`). Thus the remaining prefix is equivalent to the conjunction $I(a)\land J(b)$ and the level matrix at position $3w$ with endpoints $a,b$; moving these assignment-independent conjuncts outside the prefix and applying the level-matrix characterization gives $I(a)\land J(b)\land\mathrm{Mid}_w(E,R,a,b)$ (`prefixTruth_congr_agree`, `prefixTruth_and_const`, `prefixTruth_levelMatrix`). In the forward direction, discard the unused first witness $z$ to obtain the required $A=a$ and $B=b$. In the reverse direction, given suitable $A,B$, choose any length-$w$ word for the unused block—for example, the all-false word—and use $A,B$ for the other two existential blocks. The established equivalence then proves the formula.

**Key facts.** `Complexity.TQBFHard.prefixTruth_replicate_ex`, `Complexity.QBF.prefixTruth_congr_agree`, `Complexity.TQBFHard.readBlock_eq'`, `Complexity.TQBFHard.writeBlock_of_lt`, `Complexity.TQBFHard.writeBlock_of_mem`, `Complexity.TQBFHard.prefixTruth_and_const`, `Complexity.TQBFHard.prefixTruth_levelMatrix`.
