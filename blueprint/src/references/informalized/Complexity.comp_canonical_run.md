<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean :: Complexity.comp_canonical_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Canonicality Check Run

**Claim.** Under the stated register bounds and register equalities, the machine reaches the inner-preparation state when $b$ is canonical and the negative-answer state otherwise, changing at most register $0$ and keeping all registers bounded by $B$.

**Proof.** Let the input be $H=\operatorname{pairEncode}(\operatorname{pairEncode}(x,b),\mathrm{tail})$. First split on whether $b$ is empty.

If $b=[]$, the pair-encoding length formula (`Turing.length_pairEncode`) and the hypotheses on registers $3$ and $4$ give $v(4)=v(3)$. Thus the canonicality-check instruction takes its equality branch directly to the inner-preparation state. No register changes; the one-step reach principle (`Complexity.LogProg.AReach.single`) records this transition and its invariant.

If $b$ is nonempty, the same length formula shows $v(4)\ne v(3)$. The machine therefore takes the reset branch and clears register $0$. It then copies register $3$ into register $0$, reaching the canonical-decrement state; the copy-run lemma (`Complexity.comp_copy_run`) justifies this run and preserves the register bound. From there, two decrements place register $0$ at $2|\operatorname{pairEncode}(x,b)|-2$, while the other registers remain unchanged. The input-bit oracle at this address reads the last bit of $b$: the address calculation is `Complexity.comp_last_address`, and the query is interpreted as an input bit by `Complexity.comp_bit` together with the whole-input query identity (`Complexity.LogProg.vword_whole₁`). The machine consequently branches to inner preparation exactly when the last bit is true; otherwise it reaches the negative-answer state. By the last-bit characterization of canonicality (`Complexity.LogProg.drop_canon`), this is exactly the required distinction between canonical and noncanonical $b$.

The temporary values written to register $0$ are $0$, $v(3)$, $v(3)-1$, and $v(3)-2$. Each is at most $B$ by the original register bound and the update-bound lemma (`Complexity.LogProg.register_update_le`). All other registers retain their original bounded values. The one-step and concatenation principles for reachability (`Complexity.LogProg.AReach.step`, `Complexity.LogProg.AReach.trans`) assemble the transitions, and the machine-invariant lemma (`Complexity.comp_preS`) supplies the instruction-side invariant along the run.

**Key facts.** `Complexity.LogProg.AReach.single`, `Turing.length_pairEncode`, `Complexity.comp_copy_run`, `Complexity.LogProg.register_update_le`, `Complexity.comp_last_address`, `Complexity.comp_bit`, `Complexity.LogProg.vword_whole₁`, `Complexity.LogProg.drop_canon`, `Complexity.comp_preS`, `Complexity.LogProg.AReach.step`, `Complexity.LogProg.AReach.trans`.
