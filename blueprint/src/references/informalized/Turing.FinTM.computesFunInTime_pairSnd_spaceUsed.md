<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.computesFunInTime_pairSnd_spaceUsed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pair decoding with linear time and space

**Claim.** A finite Boolean-alphabet Turing machine outputs the parsed second component, or the empty word if parsing fails, within linear time and uses at most linear space at every time.

**Proof.** Choose the machine that extracts the second component, with time constant $6$. Its computation theorem gives the correct output by cases on whether parsing succeeds: the selected output is the second component on success and empty on failure. Its stated running time is $5(|x|+1)$, which is at most $6(|x|+1)$.

For space, the general bound that a machine with $k$ work tapes uses at most $k(T+1)$ cells through any time, provided it halts by time $T$, applies with $T=5(|x|+1)$. The chosen machine has one work tape, so this is at most $6(|x|+1)$.

**Key facts.** `Turing.FinTM.f2_pairExtract_computes`, `Turing.FinTM.ComputesInTime.mono`, `Turing.FinTM.f2_space_of_time`.
