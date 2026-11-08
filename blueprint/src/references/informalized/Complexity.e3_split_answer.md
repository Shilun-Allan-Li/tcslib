<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.e3_split_answer -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pair Loader Computes the Verifier Indicator

**Claim.** The deterministic pair-loader associated with $N$, on the split emitter’s output for $C,c,y$, computes the indicator of whether $y$ admits a split and choice word satisfying the stated length, concatenation, and accepting-run conditions, within $3(2|y|+3)$ steps.

**Proof.** Split according to whether the exponential split search at $|y|$ fails. If it fails, no concatenation $y=xu$ can have the required choice-word length: such a split would give an index satisfying the defining equation. The indicator is therefore false, and the empty-input pair-loader computation returns false in one step (`Complexity.e3_choice_no_split`, `Complexity.cont_pair_empty`). This is within the claimed bound. If the search returns $i$, its specification gives $i\le |y|$ and the equation $i+C\cdot 2^{(i+1)^c}=|y|$ (`Complexity.e3_split_spec`). Set $x=y.take\ i$ and $u=y.drop\ i$. Their lengths give $|u|=C\cdot 2^{(|x|+1)^c}$, and the take-drop identity gives $y=xu$. The verifier-membership characterization then identifies the indicator with the Boolean test that $N$, run on $x$ using $u$, halts with output $[1]$ (`Complexity.e3_choice_append`). The pair-loader computes this test on the encoded pair in $3(|\mathrm{pairEncode}(x,u)|+1)$ steps (`Complexity.cont_pair_computes`). The split-word length bound makes this no greater than $3(2|y|+3)$ (`Complexity.e3_split_length`), so monotonicity of computation time yields the claimed bound (`Turing.FinTM.ComputesInTime.mono`).

**Key facts.** `Complexity.e3_choice_no_split`, `Complexity.cont_pair_empty`, `Complexity.e3_split_spec`, `Complexity.e3_choice_append`, `Complexity.cont_pair_computes`, `Complexity.e3_split_length`, `Turing.FinTM.ComputesInTime.mono`.
