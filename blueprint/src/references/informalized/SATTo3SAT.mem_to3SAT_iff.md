<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/NPReductions/SATTo3SAT.lean :: SATTo3SAT.mem_to3SAT_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Membership in the SAT-to-3-SAT Encoding

**Claim.** A 3-clause occurs in the SAT-to-3-SAT encoding of $f$ exactly when it occurs in the encoding of some clause $f_i$ at index $i<|f|$.

**Proof.** Unfold the definition of the SAT-to-3-SAT encoding: it is the recursive encoding of $f$ started at index zero. The membership characterization for the recursive encoding then gives a position $i<|f|$ and membership in the single-clause encoding at index $0+i=i$ (\texttt{SATTo3SAT.mem\_to3SATAux\_iff}).

**Key facts.** `SATTo3SAT.mem_to3SATAux_iff`.
