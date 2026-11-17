<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Bridge.lean :: Complexity.Codec.mem_of_codePath -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Code Path Implies Acceptance

**Claim.** If $u$ codes the initial configuration within window $s$, a finite path of valid windowed one-step transitions leads from $u$ to $v$, and $v$ codes a halted configuration with output $[1]$ within the window, then $x\in L$.

**Proof.** First use the initial-language characterization (`Complexity.Codec.mem_initLang`) to identify $u$ with the code of the initial configuration. We prove along the given finite path that each reached code $c$ has a choice string $w$ and a windowed configuration $D$ coded by $c$, such that the run on $w$ has the same core data as $D$. At the reflexive start, take the empty choice string and the initial configuration, which is in every window (`Turing.Cfg.inWindow_init`). At a path extension, the one-step-language characterization (`Complexity.Codec.mem_stepLang`) provides windowed configurations $C,C'$ with the indicated codes and a choice bit taking $C$ to $C'$. Since the predecessor run and $C$ are windowed and have equal codes, their encoded configuration words agree: binary expansion recovers each word from its code (`Complexity.Codec.bits_cfgCode`), and equal codes therefore give equal words. The codec's core-data theorem (`Complexity.Codec.coreSum_eq_of_cfgWord_eq`) identifies their core data. Appending the chosen bit to $w$ then advances the run to data matching $C'$, using the stability of core data under a fixed choice (`Turing.NDTM.coreSum_stepWith`). This proves the induction claim.

At the endpoint, the acceptance-language characterization (`Complexity.Codec.mem_acceptLang`) supplies a windowed configuration $C$ coded by $v$, halted and with output $[1]$. The endpoint run configuration and $C$ have equal core data by the same code-to-word argument. Thus the run on the constructed choice string is halted and has output summary corresponding to exactly $[1]` (`Turing.outSummary_eq_accept_iff`). This is an accepting run, so the decision property yields $x\in L$ (`Turing.FinNDTM.DecidesInSpace.mem_of_acceptsWithin`).

**Key facts.** `Complexity.Codec.mem_initLang`, `Turing.Cfg.inWindow_init`, `Complexity.Codec.mem_stepLang`, `Complexity.Codec.bits_cfgCode`, `Complexity.Codec.coreSum_eq_of_cfgWord_eq`, `Turing.NDTM.coreSum_stepWith`, `Complexity.Codec.mem_acceptLang`, `Turing.outSummary_eq_accept_iff`, `Turing.FinNDTM.DecidesInSpace.mem_of_acceptsWithin`.
