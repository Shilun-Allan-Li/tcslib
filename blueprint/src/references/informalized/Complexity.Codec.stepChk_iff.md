<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Checks.lean :: Complexity.Codec.stepChk_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Encoded Checks Characterize Machine Steps

**Claim.** The step-check predicate holds exactly when the two words encode configurations inside the radius-$s$ window and the second configuration follows from the first in one machine step.

**Proof.** Suppose first that the step-check predicate holds, with nondeterministic choice $b$. The configuration-code characterization `validChk_iff` extracts a configuration $C$ inside the window whose code is $w$. The action identification `aI_cfgWord` says that the verifier’s action on the scan of this code is the actual action prescribed by the machine for $C$ and choice $b$; it also identifies the scanned head summary with the summary of $C$. The local scan characterization `sDone_step`, together with the assumed successful scan, then gives both the updated window condition and equality of the proposed output configuration cells with those of $a.apply C$. The input-position equation and the code layout complete the identification of the entire output word with the code of $a.apply C$. By `stepWith_eq_apply`, this is a genuine machine step, so take $C'=a.apply C$.

Conversely, suppose configurations $C,C'$ witness a machine step and both window conditions. By the definition of a nondeterministic configuration step, choose $b$ with `stepWith b C = C'`. The same action identification `aI_cfgWord` identifies the transition used by the check with the action for this step. The code-layout facts `cfgWord_take`, `cfgWord_pos`, and `cfgWord_last`, together with the length fact `length_cfgWord`, give the required output length, terminal bit, and input-position field. The padded binary representation preserves its encoded integer (`bitsVal_padBits`), and `val_moveInputPos` translates the configuration’s input-head movement into the numeric position equation. Finally, `sDone_step` turns the equality of the output code’s configuration portion with the updated cells, and the assumed window condition on $C'$, into the successful local scan. These are exactly the clauses of the step-check predicate.

**Key facts.** `Complexity.Codec.validChk_iff`, `Complexity.Codec.aI_cfgWord`, `Complexity.Codec.sDone_step`, `Complexity.Codec.cfgWord_take`, `Complexity.Codec.cfgWord_pos`, `Complexity.Codec.cfgWord_last`, `Complexity.Codec.length_cfgWord`, `Complexity.Codec.bitsVal_padBits`, `Complexity.Codec.val_moveInputPos`, `Complexity.Codec.stepWith_eq_apply`.
