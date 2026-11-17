<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Relax.lean :: Complexity.LogProg.ExpBFS.ex2_pre -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Concatenation of Guarded Runs with Two Outputs

**Claim.** If $a$ reaches $b$ in finitely many steps with the guard holding at every time strictly before arrival, and $b$ similarly reaches some $f(y,z)$ with $Q(y,z)$, then $a$ reaches that same $f(y,z)$ with the guard holding throughout and $Q(y,z)$ still true.

**Proof.** Choose $y,z$ and a guarded run from $b$ to $f(y,z)$ witnessing the existential hypothesis. Concatenate this run with the guarded run from $a$ to $b$. The guard holds along the first segment before arrival at $b$ and along the second segment before arrival at $f(y,z)$, so the concatenation is guarded. The same witnesses $y,z$ retain the property $Q(y,z)$. The concatenation step is the guarded-run transitivity property (`MReach.trans`).

**Key facts.** `Complexity.LogProg.MReach.trans`.
