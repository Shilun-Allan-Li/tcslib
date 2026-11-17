<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clFresh_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded reset and field loading

**Claim.** For every Boolean input word $x$, valid input-head position $p$, stream prefix $\mathrm{pre}$, field word $w$, stream tail, and old target word, the unrestricted loader reaches its completed reading configuration within $2|\mathrm{old}|+3|w|+6$ steps, with the target equal to $w$, target head at zero, and stream head at $|\mathrm{pre}|+2|w|+2$.

**Proof.** Run the wipe phase first. The first-completion result for wiping (`clWipe_first`) gives a time $a\le 2|\mathrm{old}|+2$ at which the old target has been erased and the machine is at the wipe exit control. The seam-composition theorem (`Turing.seamCompTM_run_ofCfg`) then joins this run to the reader run, inserting the single transition that transfers control across the seam. For the reader phase, apply `clRead_run` with an empty old target; its length condition holds because $0\le |w|$. It takes $3|w|+3$ steps and produces the stated target, head positions, and completed reading control. The combined time is $a+1+(3|w|+3)$, which is at most $2|\mathrm{old}|+3|w|+6$.

**Key facts.** `Complexity.clWipe_first`, `Turing.seamCompTM_run_ofCfg`, `Complexity.clRead_run`.
