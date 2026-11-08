<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/UPathLoops.lean :: Complexity.LogProg.ix_v_upd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unaffected Row and Column Registers

**Claim.** Replacing the input pointer and the counters $a,b$ of a register record leaves unchanged its values at the row and column indices assigned to any of the four sites.

**Proof.** Check the four sites. Their row and column indices are $(11,12)$, $(12,11)$, $(12,11)$, and $(4,8)$. None of these indices is $0$, $2$, or $3$, the register positions storing the fields being replaced. Hence each selected register value is unchanged, giving both equalities.
