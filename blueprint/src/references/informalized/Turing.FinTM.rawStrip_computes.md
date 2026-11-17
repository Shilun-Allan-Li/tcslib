<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.rawStrip_computes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Marker Stripping Time Bound

**Claim.** On every Boolean word $x$, the raw marker-stripping machine outputs the prefix strictly before the last true bit, or the empty word if there is no true bit, within $4(|x|+1)$ steps.

**Proof.** Fix $x$. After $|x|+1$ steps, the machine has copied the entire input to its work tape and made the transition into its trimming state (`rawStrip_copy` together with the end-marker transition). This starting configuration has the input fully read and the work tape holding $x$. Apply the trimming bound with $w=x$: within some $t\le3(|x|+1)$ additional steps, the machine halts and outputs $(\mathrm{splitAtLastTrue}(x)).\mathrm{getD}([])$ (`rawStrip_trim`). The run-addition law (`runFrom_add`) combines the copying and trimming phases, giving a halt with the desired output after $|x|+1+t$ steps. This is at most $4(|x|+1)$. The time monotonicity principle (`ComputesInTime.mono`) extends the computation to exactly the claimed time.

**Key facts.** `Turing.FinTM.rawStrip_copy`, `Turing.FinTM.rawStrip_trim`, `Turing.MultiTapeTM.runFrom_add`, `Turing.FinTM.computesInTime_iff`, `Turing.FinTM.ComputesInTime.mono`.
