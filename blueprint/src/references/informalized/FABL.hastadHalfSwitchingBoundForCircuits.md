<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/LMN.lean :: FABL.hastadHalfSwitchingBoundForCircuits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Half switching bound for bounded-width formulas

**Claim.** Every Boolean function represented by a DNF or CNF of width at most $w>0$ has switching-failure probability at rate $1/(10w)$ at most $2^{-k}$, for every natural number $k$.

**Proof.** Fix the width-$w$ representation and $k$. The general half switching bound for width-bounded DNF or CNF formulas states directly that the switching-failure probability at rate $1/(10w)$ is at most $(1/2)^k$ (`hastadHalfSwitchingBound`). The claimed theorem is this bound with the rate written using the definition of the switching-layer rate.

**Key facts.** `FABL.hastadHalfSwitchingBound`.

**Caveat.** The supplied informal statement describes a different circuit theorem; the proof source and formal statement establish the width-bounded DNF/CNF switching bound stated here.
