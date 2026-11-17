<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Program.lean :: Complexity.LogProg.seam_init -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Compiled Machine Initial Configuration

**Claim.** On every Boolean input, the compiled machine's initial configuration equals the seam formed from the initial configuration of the register program with start state $l_0$.

**Proof.** The compiled machine starts in state $\mathrm{prog}(l_0)$, at input-head position $1$, with every work tape blank, every work head at $0$, and empty output. The seam of the program's initial configuration has the same state, input position, and output. For each of the original $m$ tapes, the appended tape and head position agree with the original blank tape and zero position; for each of the additional $k_D$ tapes, the seam supplies a blank tape and a head at zero. Thus the configurations agree in every component.
