<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/CleanSweep.lean :: Complexity.LogProg.ccfg_mark -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Marked Tape Reading

**Claim.** In the configuration formed by placing the first tape family before the second, the symbol read from tape $k+i$ is the second family's $i$th tape content at its head position.

**Proof.** By definition, the combined tape family is the append of the first family and the second. The index $\mathrm{Fin.natAdd}(k,i)$ selects the second family, so the combined tape at that index is $M_t(i)$. The combined head-position family selects $M_p(i)$ at the same index. Evaluating the tape at that head position therefore gives $M_t(i)(M_p(i))$, as claimed.
