<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean :: Complexity.comp_call_return -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Oracle Call and Return

**Claim.** When the machine instruction at $l$ calls oracle $j$ in whole-input mode using register $r$, it halts with that oracle's answer on $\langle h,\mathrm{bits}(v(r))\rangle$, while maintaining the prescribed configuration invariant.

**Proof.** One machine step from the call instruction forms its virtual query. In whole-input mode with the single argument register $r$, that query is precisely $\operatorname{pairEncode}(h,\mathrm{bits}(v(r)))$ (the whole-input query identity, `Complexity.LogProg.vword_whole₁`). The instruction therefore moves to the positive-answer state if the oracle answers true and to the negative-answer state otherwise. In either case, the corresponding answer state halts with that Boolean answer, by the answer-state run lemma (`Complexity.comp_ret`). The initial configuration satisfies the prescribed invariant: `Complexity.comp_preS` supplies its instruction-side condition, and the assumed register bounds supply its register condition. Prepending the call step to the answer-state run using the one-step halting principle (`Complexity.LogProg.AHalt.step`) proves the result.

**Key facts.** `Complexity.LogProg.AHalt.step`, `Complexity.LogProg.vword_whole₁`, `Complexity.comp_preS`, `Complexity.comp_ret`.
