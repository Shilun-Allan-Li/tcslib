<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.computesFunInTime_splitSolve_spaceUsed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Split Search with Bounded Space

**Claim.** For every $C,e\in\mathbb{N}$, a finite Boolean Turing machine computes the specified padded split encoding, or the empty word if no admissible split exists, within $c(|x|+1)^{e+2}$ steps and uses at most $c(|x|+1)^{e+1}$ work-tape cells through every time.

**Proof.** Use the closed split-search construction with its simultaneous running-time and space estimates. It provides a machine and one constant $c$ satisfying both bounds and computing exactly the stated output.

**Key facts.** `Turing.FinTM.f2_splitSolve_closed`.
