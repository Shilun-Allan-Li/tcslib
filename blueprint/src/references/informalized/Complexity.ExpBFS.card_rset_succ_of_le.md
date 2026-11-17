<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Radius.lean :: Complexity.ExpBFS.card_rset_succ_of_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Stability of Reachable-Code Counts

**Claim.** If $N$ decides $L$ using space bound $sp$ and $sp(|x|)\le s$, then the numbers of reachable configuration codes for window sizes $s$ and $s+1$ are equal.

**Proof.** The count for radius $s$ is at most the count for radius $s+1$ by the monotonicity theorem (\texttt{card\_rset\_le\_succ}). For the reverse inequality, take any code reachable in the larger window. The path characterization of reachability represents it as the code of a configuration reached by some choice string (\texttt{rcode\_iff}). Every configuration along that run lies in the radius-$sp(|x|)$ window because the machine decides using that space bound (\texttt{inWin\_runWith\_of\_decides}); since $sp(|x|)\le s$, it lies in the radius-$s$ window too (\texttt{inWin\_mono}). The same path therefore gives a radius-$s$ reachable code, and recoding maps it to the original radius-$(s+1)$ code (\texttt{recode\_spec}). Consequently, the larger-window reachable set is contained in the image under recoding of the smaller-window reachable set. Its cardinality is at most that image's cardinality, which is at most the smaller set's cardinality (\texttt{Finset.card\_image\_le}). Combining both inequalities gives equality.

**Key facts.** `Complexity.ExpBFS.card_rset_le_succ`, `Complexity.ExpBFS.mem_rset`, `Complexity.ExpBFS.rcode_iff`, `Complexity.ExpBFS.inWin_runWith_of_decides`, `Complexity.ExpBFS.inWin_mono`, `Complexity.ExpBFS.recode_spec`.
