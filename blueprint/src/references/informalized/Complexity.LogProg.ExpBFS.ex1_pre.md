<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Relax.lean :: Complexity.LogProg.ExpBFS.ex1_pre -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Concatenation of Guarded Runs

**Claim.** If $a$ reaches $b$ in finitely many steps with the guard holding at every time strictly before arrival, and $b$ similarly reaches some $f(y)$ with $Q(y)$, then $a$ reaches that same $f(y)$ with the guard holding throughout and $Q(y)$ still true.

**Proof.** Choose $y$ and a guarded run from $b$ to $f(y)$ witnessing the assumed existential. Concatenate it with the guarded run from $a$ to $b$: the first run supplies the guard before reaching $b$, and the second supplies it at each subsequent time before reaching $f(y)$. Thus the concatenated run is guarded, and the chosen witness still satisfies $Q(y)$. This is precisely the concatenation property of guarded finite runs (`MReach.trans`).

**Key facts.** `Complexity.LogProg.MReach.trans`.
