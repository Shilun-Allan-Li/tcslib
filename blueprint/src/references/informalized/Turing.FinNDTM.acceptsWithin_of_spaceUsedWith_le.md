<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ConfigGraph.lean :: Turing.FinNDTM.acceptsWithin_of_spaceUsedWith_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acceptance under a Space Bound

**Claim.** If a finite nondeterministic Turing machine accepts an input using a choice word of length exactly $T$, and every choice word of that length uses at most $s$ work-tape cells in total, then it accepts the input using a choice word of length exactly $3(|Q|+1)(|x|+2)3^{k(2s+1)}(2s+1)^k$.

**Proof.** If $T$ is already at most the stated bound, the given accepting computation can be extended to a choice word of the required length: acceptance within a length bound is monotone in that bound (`Turing.FinNDTM.AcceptsWithin.mono`). So suppose $T$ is larger. Consider accepting choice words whose every prefix configuration lies in the coding window determined by the space limit $s$. The original accepting word is one such word: the space hypothesis and the fact that every prefix configuration is included in the space-use estimate ensure this (`Turing.NDTM.runWith_take_inWindow`). Choose a shortest such word, say $v$, of length $t$.

We claim that no two distinct prefix configurations of $v$ have the same summary vertex. Indeed, suppose the prefixes at positions $a<b$ have equal core summaries. Splicing out the choices between those positions, by taking the first $a$ choices followed by the choices after position $b$, preserves the final core summary and represents every new prefix summary by some old prefix summary (`Turing.NDTM.splice_vertices`). The final summary still certifies that the new computation halts with output $[\mathrm{true}]$: the output summary characterizes acceptance (`Turing.outSummary_eq_accept_iff`). Each new prefix configuration remains in the coding window, since equality of core summaries transfers that property from the corresponding old prefix (`Turing.NDTM.inWindow_of_coreSum_eq`). The spliced word is strictly shorter, contradicting the choice of $v$. Thus its $t+1$ prefix summaries are all distinct.

The finite count of possible windowed summary vertices now bounds the number of these distinct summaries: the counting lemma gives $t+1\leq 3(|Q|+1)(|x|+2)3^{k(2s+1)}(2s+1)^k$ (`Turing.FinNDTM.count_windowed_vertices`). The chosen word accepts in exactly $t$ steps, so monotonicity extends this to an accepting word of exactly the stated length.

**Key facts.** `Turing.FinNDTM.AcceptsWithin.mono`, `Turing.NDTM.runWith_take_inWindow`, `Turing.NDTM.splice_vertices`, `Turing.outSummary_eq_accept_iff`, `Turing.NDTM.inWindow_of_coreSum_eq`, `Turing.FinNDTM.count_windowed_vertices`.
