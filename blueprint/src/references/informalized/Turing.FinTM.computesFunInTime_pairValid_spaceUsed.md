<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.computesFunInTime_pairValid_spaceUsed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pair-code validity with bounded space

**Claim.** A finite Boolean-alphabet Turing machine outputs the one-bit validity indicator in linear time and uses at most one work-tape cell at every time.

**Proof.** Choose the zero-work-tape pair-validity machine and set $c=1$. Its computation theorem gives the required output within $|x|+1$ steps. Since it has no work tapes, its total work space is zero at every time, by the zero-tape space identity; this is at most $1$.

**Key facts.** `Turing.FinTM.f2_pairValid_computes`, `Turing.MultiTapeTM.spaceUsed_zero_tapes_eq_zero`.
