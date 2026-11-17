<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satDrop_skip -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Skipping by the Stored Length

**Claim.** For each $r\le n$, starting in state $4$ at clamped input offset $p$, with a unary counter of length $n$, head at $0$, and empty output, the machine reaches after $r$ steps state $4$ at offset $p+r$, with the counter unchanged and its head at $r$.

**Proof.** Induct on $r$. For $r=0$, zero steps leave the starting configuration unchanged (`runFrom_zero`). For the successor case, first apply the induction hypothesis to reach offset $p+r$ with counter head at $r$. Since $r+1\le n$, we have $r<n$, so the unary counter contains true at position $r$ (`satRedCounter_read`). In state $4$ the machine consequently moves both the input and counter heads right, leaves the counter tape and output unchanged, and remains in state $4$. The clamped input-position successor law and the silent-move action law (`satStreamPos_succ`, `satDrop_move`) identify the next configuration at offset $p+r+1$ and head $r+1$. The successor-step run law (`runFrom_succ_eq_step'`) combines this transition with the induction hypothesis to give the result.

**Key facts.** `Turing.MultiTapeTM.runFrom_zero`, `Complexity.satRedCounter_read`, `Complexity.satStreamPos_succ`, `Complexity.satDrop_move`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
