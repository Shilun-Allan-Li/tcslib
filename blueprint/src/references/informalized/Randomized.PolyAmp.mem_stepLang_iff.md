<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplifyPolyCode.lean :: Randomized.PolyAmp.mem_stepLang_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Step language characterization

**Claim.** For a reachable configuration $C$ on input $x$, the encoded input, code of $C$, candidate code $c'$, and space bound $S$ belongs to the step language exactly when $c'$ is the code of a one-step successor of $C$ for some choice bit.

**Proof.** Choose a choice word $u$ witnessing that $C$ is reachable, and let $D$ be the configuration obtained by running $u$ from the initial configuration. The space-use hypothesis and the bound $sp(|x|)\le S$ imply that $D$ lies in the $S$-window. Since $D$ and $C$ have the same core data, their configuration words and codes agree (`cfgWord_congr`). Unfolding the step-language characterization (`mem_stepLang`), membership supplies an $S$-window configuration $E$ with the same code as $D$, and a successor $E'$ reached from $E$ by some choice bit $b$. The window-code injectivity theorem (`coreSum_eq_of_code_eq`) identifies the core data of $E$ and $D$; together with reachability, this gives equality of their core data. A fixed choice preserves equality of core data (`coreSum_stepWith`), so the code of the $b$-successor of $C$ equals the code of $E'$, namely $c'$. Conversely, suppose $c'$ is the code of the $b$-successor of $C$. Use $D$ as the step-language witness and take its $b$-successor as the next configuration. Its code agrees with the successor code from $C$, again because equal core data are preserved by a fixed step. It lies in the $S$-window: apply the run-space bound to the concatenated choice word $u++[b]$, and use the run concatenation identities to identify that run with the stated successor. Thus all fields required by the step-language characterization hold.

**Key facts.** `Complexity.Codec.cfgWord_congr`, `Complexity.Codec.mem_stepLang`, `Randomized.BPLInP.coreSum_eq_of_code_eq`, `Randomized.BPLInP.inWin_run`, `Turing.NDTM.coreSum_stepWith`, `Turing.NDTM.runWith_append`, `Turing.NDTM.runWith_cons`, `Turing.NDTM.runWith_nil`.
