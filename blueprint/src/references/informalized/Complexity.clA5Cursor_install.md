<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5Cursor_install -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Clean cursor installation module

**Claim.** There are a finite Boolean Turing machine and natural numbers $a,r$ such that the machine has at least one work tape and, on every input $x$ and argument $v$, first halts within $a(|v|+1)^r$ positive steps with tape zero containing the pair encoding of the empty word and $v$, all other tapes blank, heads at their initial positions, and empty output.

**Proof.** The fixed-prefix pairing map $v\mapsto\operatorname{pairEncode}([],v)$ is polynomial-time computable: the fixed-prefix pairing machine computes it in linear time (\texttt{computesFunInTime_pairEncodeFixed}), and hence it is polynomial-time computable (\texttt{clNative_linear}). The clean-installation lemma (\texttt{clA5Clean_install}) turns any polynomial-time computable map into a finite machine that computes it with empty emitted output, has at least one work tape, and first halts in positive time bounded by a polynomial in the argument length. Applying that lemma to this pairing map gives the stated machine and constants.

**Key facts.** `Turing.FinTM.computesFunInTime_pairEncodeFixed`, `Complexity.clNative_linear`, `Complexity.clA5Clean_install`.
