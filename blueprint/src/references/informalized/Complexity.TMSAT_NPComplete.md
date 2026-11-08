<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/TMSAT.lean :: Complexity.TMSAT_NPComplete -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# TMSAT Is NP-Complete

**Claim.** For an effective machine-code scheme whose canonizer has a polynomially bounded running time, TMSAT belongs to NP and is NP-hard; hence it is NP-complete.

**Proof.** NP-completeness follows by proving its two defining properties. The membership theorem for TMSAT shows that the stated canonizer hypothesis places TMSAT in NP ($\texttt{TMSAT_mem_NP}$). Separately, the hardness theorem establishes that TMSAT is NP-hard ($\texttt{TMSAT_NPHard}$). Pairing these conclusions gives NP-completeness.

**Key facts.** `Complexity.TMSAT_mem_NP`, `Complexity.TMSAT_NPHard`.
