<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformWalk.lean :: BoolCircuit.AdjWalk.Em.emit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Emission of a Single Site Bit

**Claim.** Starting in state $\mathrm{em}(s)$ with registers $(k,V,U,W)$, the machine emits the one-bit segment assigned to site $s$ and reaches its successor state with registers $(k+1,V,U,W)$, while respecting the register bound.

**Proof.** The input's plain payload is the canonical bit word for $i$. Thus the machine's comparison of the first register's bit encoding with that payload succeeds exactly when $k=i$ (`plainWord_pairEncode`, `bits_injective`). If $i=k$, the emitted bit is the queried bit of the one-term segment, and the machine halts with that answer; the register bounds hold at the starting configuration, so the one-step halting principle applies (`gd_rg`, `AHalt.step`, `AHalt.ret`). If the whole segment lies before the queried position, then $k<i$. The comparison therefore fails, and the machine enters the bump state. That state increments the first register and moves to $s$'s successor, leaving the other registers unchanged. The bound $k+1\le B$ ensures the first register remains within the bound, while $V,U,W\le B$ bound the others. The reached configuration satisfies the stated postcondition, and reflexivity gives the remaining reach (`gd_rg`, `AReach.step`, `AReach.refl`).

**Key facts.** `Complexity.LogProg.plainWord_pairEncode`, `Complexity.LogProg.bits_injective`, `BoolCircuit.AdjWalk.gd_rg`, `Complexity.LogProg.AHalt.step`, `Complexity.LogProg.AHalt.ret`, `Complexity.LogProg.AReach.step`, `Complexity.LogProg.AReach.refl`.
