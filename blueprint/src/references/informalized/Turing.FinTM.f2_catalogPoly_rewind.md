<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_catalogPoly_rewind -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rewind phase restores a head

**Claim.** Starting in $\mathrm{rewind}(i)$ with head positions obtained from $h$ by setting position $i$ to $j-1$, after $j+1$ steps the machine is in $\mathrm{advance}(i+1)$, with position $i$ reset to zero and all other head positions unchanged; output remains $o$.

**Proof.** Induct on $j$. When $j=0$, the selected head is at $-1$, a blank cell. The rewind transition therefore moves it right and enters $\mathrm{advance}(i+1)$; this restores its position to zero, while the other heads and output are unchanged. For the successor case, the selected head starts at $j$, where $0\le j<q$, so the tape contains true there. The machine moves that head left and stays in rewind, leaving it at $j-1$. The induction hypothesis then applies to the remaining $j+1$ steps. The one-step move behavior is given by `f2_catalogPolyMove_apply`, and the run recursion identities (`runFrom_succ_eq_step`, `runFrom_zero`) relate these steps to the full run.

**Key facts.** `Turing.FinTM.f2_catalogPolyMove_apply`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`.
