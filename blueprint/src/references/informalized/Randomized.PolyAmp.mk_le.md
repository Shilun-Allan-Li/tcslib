<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplifyPolyRun.lean :: Randomized.PolyAmp.mk_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Register bounds for initialization

**Claim.** Under the stated sum bound and coordinate bounds, every register of the initialized tuple is at most $B$.

**Proof.** The initialized register values are $n,\ell,S,0,K,K+1,i,\mathrm{cnt},c,d,j,0,0,0,0$. The sum bound implies that $n,\ell,S,K$ are at most $B$ and that $K+1\le B$; the hypotheses bound $i$ and $\mathrm{cnt}$ by $K+1$, and $c,d,j$ by $K$. The remaining entries are zero. Hence each coordinate is at most $B, as required.
