<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.b2_finish -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Timed completion of verification

**Claim.** If the verifier halts on $x$ followed by $u$ after $T$ steps with output $[b]$, then every choice word of length $|x\mathbin{+	}u|+2+(T+1)$ makes the host started from the guessing configuration determined by $c$ and $u$ halt with output $[b]$.

**Proof.** Split the choice word after its first $a=|x\mathbin{+	}u|+2$ bits. Its prefix has length $a$, and its suffix has length $T+1$, by the given total length. The assembly property (`b2_assembly`) shows that the prefix takes the host from the guessing configuration to the verifier configuration initialized on $x\mathbin{+	}u$, with the correct inherited tape data. The timed verification property (`b2_verify_timed`) then shows that the suffix makes the host halt with output $[b]$. Running on concatenated choice words is the same as running first on the prefix and then on the suffix (`Turing.NDTM.runWith_append`); the prefix and suffix together are the original word (`List.take_append_drop`). Thus the full run has the asserted halting state and output.

**Key facts.** `Complexity.b2_assembly`, `Complexity.b2_verify_timed`, `Turing.NDTM.runWith_append`.
