<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Tribes.lean :: FABL.criticalInverse_le_criticalLog -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Critical Inverse Logarithmic Bound

**Claim.** For every positive natural number $w$, $2^{-w}\le -\log(1-2^{-w})$.

**Proof.** Set $q=1-2^{-w}$. The critical base bound gives $0<q<1$ (`FABL.criticalBase_mem_Ioo`). For positive $q$, the logarithmic inequality $\log q\le q-1$ applies. Rearranging it gives $1-q\le-\log q$; since $1-q=2^{-w}$, this is the claimed bound.

**Key facts.** `FABL.criticalBase_mem_Ioo`.
