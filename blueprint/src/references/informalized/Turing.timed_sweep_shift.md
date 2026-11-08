<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timed_sweep_shift -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Tape Invariance Under a Frontier Shift

**Claim.** For integer frontier $z$ and lists $l,w,r$, the tape represented by frontier $z$, left list $l$, and right list $w$ followed by $r$ equals the tape represented by frontier $z+|w|$, left list $w^{\mathrm{rev}}$ followed by $l$, and right list $r$.

**Proof.** Induct on the finite list $w$, generalizing the frontier and the left list. If $w$ is empty, both representations are identical. For the step, write $w=a::w_0$. The current cell at frontier $z$ already contains $a$, so writing $a$ there leaves the represented tape unchanged; this follows from the frontier-read property (`sweepTape_read`). The one-cell shift identity (`sweepTape_right`) then moves that cell into the left list and advances the frontier to $z+1$, leaving right list $w_0++r$. Apply the induction hypothesis to this shorter right list. The resulting left list is $w_0^{\mathrm{rev}}++[a]++l$, which is exactly $(a::w_0)^{\mathrm{rev}}++l$; the frontier arithmetic gives $z+|a::w_0|$.

**Key facts.** `Turing.FinTM.sweepTape_read`, `Turing.FinTM.sweepTape_right`.
