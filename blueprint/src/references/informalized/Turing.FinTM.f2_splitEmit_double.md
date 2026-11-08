<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_splitEmit_double -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output after paired input steps

**Claim.** For each $j\le |s|$, the specified machine after $2j$ steps is in state $0$, with both heads at position $j$, and has output obtained by repeating each bit of the prefix $w\mathbin{\upharpoonright}j$ twice in order.

**Proof.** Induct on $j$. At $j=0$, the initial configuration has the stated form. For the successor case, the bound $j+1\le |s|\le |w|$ ensures that both the next buffer bit $s[j]$ and input bit $w[j]$ exist. The position-reading property (`f2_splitPos_read`) shows the input head scans $w[j]$, and the buffer-tape contents give $s[j]$ at the auxiliary head. In state $0$, the machine emits the input bit and enters state $1$; the first step does not move either head. In state $1$, it emits the same input bit again, moves both heads forward by one, and returns to state $0$. The input-position successor identity (`f2_splitPos_succ`) identifies the advanced input position with that associated to $j+1$; the auxiliary head likewise advances from $j$ to $j+1$. The two new output bits append $w[j],w[j]$ to the existing output. Since the prefix of length $j+1$ consists of the prefix of length $j$ followed by $w[j]$, this is exactly the required repeated-bit output. The successor-time run equation (`runFrom_succ_eq_step'`) expresses these two transitions as the increase from $2j$ to $2(j+1)$ steps, and the zero-movement identity (`moveInputPos_zero`) accounts for the stationary input head during the first step.

**Key facts.** `Turing.FinTM.f2_splitPos_read`, `Turing.FinTM.f2_splitPos_succ`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.moveInputPos_zero`.
