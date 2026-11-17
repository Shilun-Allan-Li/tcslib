<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.exists_installCallTM -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Install-Mode Call Machine

**Claim.** Given a finite Boolean machine computing $f$ within $T(|a|)$ steps, there is a finite call machine that, from a clean seam with argument $a$ on its first work tape, reaches a clean seam with $f(a)$ installed on that tape, preserves the other tapes as blank, and avoids its exit state before a positive completion time bounded linearly by $T(|a|)+|a|+|f(a)|+1$.

**Proof.** Choose the call machine with emission disabled, its initial state as entry, the designated state numbered $5$ in its call-state component as exit, and coefficient $24+13M.k$. For each pair $(x,a)$, apply the first-exit call lemma to the computation of $M$ on $a$, taking its output cap to be $f(a)$ and its time bound to be $T(|a|)$. The lemma supplies a positive time within the required bound, excludes the exit state at every earlier time, and gives the final configuration with $f(a)$ installed in place of $a$ and with the clean-call tape and head arrangement. Since emission is disabled, the output component is empty as required by the clean install configuration. The lemma’s exclusion includes time zero, which implies the required exclusion at earlier positive times as well.

**Key facts.** `Turing.FinTM.emCall_first`.
