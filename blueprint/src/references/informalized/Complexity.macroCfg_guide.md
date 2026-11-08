<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean :: Complexity.macroCfg_guide -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Guide symbol in a macrostep configuration

**Claim.** The symbol read on the guide tape in a macrostep configuration with guide head at $g$ is the base guide-tape content at coordinate $g$.

**Proof.** A macrostep configuration keeps the base configuration's tape contents and assigns the guide head coordinate $g$. By the definition of the symbol under a work-tape head, the read symbol is the tape content at that head coordinate. Substituting these two facts gives the base guide tape's content at $g$.
