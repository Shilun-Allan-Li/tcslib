<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_extract_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Halting of Pair Extraction

**Claim.** For any decomposition $x=pre\mathbin{++}rest$ and work word $a$, the pair-extraction machine halts within $3|rest|+2|a|+5$ steps and produces the specified output when pair decoding succeeds, or the empty word when it fails.

**Proof.** Use two-step induction on $rest$, matching the decoder's consumption of bits in pairs. If $rest$ is empty, one transition reads the end of input and halts with empty output. If it is a singleton, the machine first reads that bit and then halts; either bit pattern leaves pair decoding undefined, and the output is empty. For $rest=b::c::rest'$, first apply the two-step configuration calculation: equal bits are appended to the work word and return the machine to its initial scanning state; the pattern $false,true$ moves it into the rewind/finish phase; and $true,false$ halts immediately with empty output. In the equal-bit case, the induction hypothesis applies to the remaining suffix with prefix extended by $[b,b]$ and work word extended by $[b]$. The two preceding steps and the decoder's recursive equation give the required output, while the added work bit and two input bits fit the stated time bound. In the $false,true$ case, apply the finish-phase halting bound to the remaining suffix; the decoder returns that suffix as its second component, and the two initial steps plus the finish bound fit the claimed estimate. The $true,false$ case halts after those two steps, as required. The decomposition of $x$ ensures each transition reads the corresponding bit of the suffix.

**Key facts.** `Turing.FinTM.f2_extract_block`, `Turing.MultiTapeTM.runFrom_add`, `Turing.FinTM.f2_extract_first`, `Turing.FinTM.f2_extract_finish`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.FinTM.f2_extractCfg_read`.
