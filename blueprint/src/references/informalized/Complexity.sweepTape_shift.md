<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean :: Complexity.sweepTape_shift -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Shift invariance of the tape representation

**Claim.** The tape represented by frontier $z$, left list $l$, and right list $w$ followed by $r$ is the same as that represented by frontier $z+|w|$, left list $w$ reversed followed by $l$, and right list $r$.

**Proof.** Induct on the list $w$, generalizing the frontier and the left list. For the empty list, the two representations agree directly. For $w=a::w'$, first move the symbol $a$ from the head of the right list across the frontier: the tape is unchanged when the frontier advances by one and $a$ is prepended to the left list. The tape is unchanged at the frontier itself because reading there gives the head of the right list (Turing.FinTM.sweepTape_read); the one-cell shift identity then applies (Turing.FinTM.sweepTape_right). Apply the induction hypothesis to the remaining list $w'$, with the shifted frontier and the updated left list. Since reversing $a::w'$ puts $a$ at the end of the reversed tail, the resulting left list is exactly $(a::w')$ reversed followed by $l$. The frontier has advanced by $1+|w'|=|w|$, as required.

**Key facts.** `Turing.FinTM.sweepTape_read`, `Turing.FinTM.sweepTape_right`.
