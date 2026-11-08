<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/OracleSim.lean :: Turing.oracleBookmark_ne_origin -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A bookmarked point is not the oracle origin

**Claim.** For integers $p$ and nonzero $z$, changing the oracle's value at $p$ to $\mathrm{some}(\mathrm{false})$ leaves its value at $z$ different from $\mathrm{some}(\mathrm{true})$.

**Proof.** If $z=p$, the updated value is explicitly $\mathrm{some}(\mathrm{false})$, which differs from $\mathrm{some}(\mathrm{true})$. If $z\ne p$, the update leaves the oracle unchanged at $z$. Since $z\ne0$, the oracle origin has value none there, also different from $\mathrm{some}(\mathrm{true})$.
