<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/NSPACE.lean :: Complexity.SPACE_subset_NSPACE -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Deterministic space is contained in nondeterministic space

**Claim.** For every function $s:\mathbb{N}\to\mathbb{N}$, every binary language decidable by a finite deterministic Turing machine within a constant multiple of $s(n)$ is decidable by a finite nondeterministic Turing machine under the corresponding space bound.

**Proof.** Take a language in $\mathrm{SPACE}(s)$, witnessed by a constant $c$ and a deterministic machine $M$. On each input $x$, the witness provides a halting computation of length $t$, producing the indicator output for membership in the language and using at most $c s(|x|)$ space. Regard $M$ as a nondeterministic machine whose two choices implement the same deterministic transition. The simulation lemma says that every branch halts within time $t$, and that acceptance by this machine is equivalent to membership of $x$ in the language (Turing.FinTM.toFinNDTM_haltsWithin_and_accepts_iff). For any choice sequence $w$ of length $t$, its space usage equals the deterministic machine's usage after $t$ steps (Turing.MultiTapeTM.toNDTM_spaceUsedWith). Hence every branch respects the same bound, proving membership in $\mathrm{NSPACE}(s)$ with constant $c$.

**Key facts.** `Turing.FinTM.toFinNDTM_haltsWithin_and_accepts_iff`, `Turing.MultiTapeTM.toNDTM_spaceUsedWith`.
