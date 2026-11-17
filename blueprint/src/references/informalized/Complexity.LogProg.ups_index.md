<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/UPathLoops.lean :: Complexity.LogProg.ups_index -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Index routine preserves semantics

**Claim.** Under the stated register bounds and row and column hypotheses, if the entry program has bounded-register termination and acceptance and rejection probabilities $q$ and $1-q$ for every eligible choice length, then the index routine has the same property.

**Proof.** First, the index bounds imply that the row-major offset lies in range: $r n+c<n^2$ (`rowMajor_lt`), and hence $rn\le n^2$. The routine clears the input pointer and then uses the increment routine to add twice the remaining distance from the initial column counter to $n$, plus the required two-bit offset. The bound on the registers and $2n+2+2n^2\le B$ ensure that these preparatory steps respect the register bound. The row-loop result (`ups_row`) then reduces the problem to the state with row counter set to $r$ and pointer $2n+2+2rn$. Next, the routine clears the inner counter and uses the increment routine to add $2c$, arriving at pointer $2n+2+2(rn+c)$ while preserving the row and column values. The index-entry result (`ups_ad`), applied to the third index addition, identifies this state with the supplied entry configuration. Thus the assumed semantics at that entry transfer back through each deterministic initialization step, and equality of the final register records identifies the resulting state with the one in the hypothesis (`UPS.of_eq`).

**Key facts.** `Complexity.rowMajor_lt`, `Complexity.LogProg.PSem.clr`, `Complexity.LogProg.UReg.reg`, `Complexity.LogProg.ups_row`, `Complexity.LogProg.ups_ad`, `Complexity.LogProg.ix_v_upd`, `Complexity.LogProg.PSem.inc`, `Complexity.LogProg.UPS.of_eq`.
