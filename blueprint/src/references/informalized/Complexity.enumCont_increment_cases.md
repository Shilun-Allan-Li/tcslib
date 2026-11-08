<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.enumCont_increment_cases -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cases for the increment output

**Claim.** Writing $v=(\operatorname{incFixed}(s)).getD\,[]$, either $v$ is empty and the defaulted increment returns $s$, or $v$ is nonempty, has length $|s|$, and the defaulted increment returns $v$.

**Proof.** The length-preservation fact for the defaulted increment (`Complexity.enumCont_step_length`) gives $|(\	ext{incFixed}(s)).getD\,s|=|s|$. If the increment returns no output, its default is $s$, so the first alternative holds. If it returns some word $v$, then the defaulted value is $v$ and the length fact gives $|v|=|s|$. If $v$ were empty, this equality would force $s$ to be empty; but the fixed-width increment of the empty word returns no output, contrary to this case. Thus $v$ is nonempty and the second alternative follows.

**Key facts.** `Complexity.enumCont_step_length`.
