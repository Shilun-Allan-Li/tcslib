<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean :: Complexity.laneCfg_right -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rightward lane update

**Claim.** Applying the specified action to the lane configuration with right list $a::r$ produces the lane configuration with frontier $z+1$, left list $b::l$, and right list $r$, in state $q'$.

**Proof.** Compare the configuration fields. The action enters state $q'$. Its stationary input-head movement leaves the input position unchanged (\(\texttt{Turing.moveInputPos_zero}\)). On the designated tape it writes $b$ at the old frontier and moves the head one position right; the sweep-tape update identity identifies the resulting tape with the one at frontier $z+1$ whose left list is $b::l$ and right list is $r$ (\(\texttt{Turing.FinTM.sweepTape_right}\)). Every other work tape is unchanged, and the output remains unchanged because the action emits nothing. Thus all configuration fields agree.

**Key facts.** `Turing.moveInputPos_zero`, `Turing.FinTM.sweepTape_right`.
