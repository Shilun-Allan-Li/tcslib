<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Radius.lean :: Complexity.ExpBFS.card_rset_le_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of Reachable-Code Counts

**Claim.** For each window size $s$, the number of reachable configuration codes in the radius-$s$ window is at most the number in the radius-$(s+1)$ window.

**Proof.** Map each code reachable in the radius-$s$ window to its recoded version for radius $s+1$. Reachability is preserved by this recoding (\texttt{recode\_mem}), and the recoding is injective on the radius-$s$ reachable set (\texttt{recode\_injOn}). The image therefore has the same cardinality as the original set and is contained in the larger-window reachable set. Hence the latter has at least as many elements.

**Key facts.** `Complexity.ExpBFS.recode_mem`, `Complexity.ExpBFS.recode_injOn`.
