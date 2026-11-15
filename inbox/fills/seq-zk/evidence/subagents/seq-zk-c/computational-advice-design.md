# Computational hybrid advice design

Author: seq-zk-c, read-only API/design work, then the lead-approved generic selector.
No original target, sibling source, frozen file, or machine semantics were changed here.

## Quantifier problem and selected route

At each input length n, the reduction needs one bounded metadata value a (input x,
verifier auxiliary input z, full fixed verifier tape, phase j, and earlier message prefix)
that works uniformly over all witnesses y. Witness lengths are unbounded by the target.
Selecting an attained maximum over pairs (a,y) is therefore unjustified. The selected
route requires neither witness-length bounds nor attainment.

For each finite a, let g(a,y) be the actual local distinguishing gap when the metadata
and witness are valid, and zero otherwise. Its values are at most one, by the existing
ColZK.distAdv_le_one. Set score(a)=sup({0} union range(g(a))). The set is nonempty and
bounded above. Finite.exists_max chooses a* maximizing these real scores. This choice
precedes the base-ZK negligible function epsilon. Base ZK, applied to the single advised
reduction for a*, bounds g(a*,y) for EVERY y by abs(epsilon(n)). Conditional completeness
then bounds score(a*) by that same nonnegative value; every other gap is at most its
score and hence at most score(a*). The Advice.exists_uniform_bound_selector theorem
packages exactly this implication. No witness is encoded in advice or computed by a
machine, and no relation-membership test is performed by a machine.

## Nonempty bounded metadata and encoding

Use x as Fin n -> Bool; bounded z and encoded prefix words as dependent sums of lengths
at most their polynomial bounds; full verifier tape as its fixed finite Bool tuple; and
j as Fin(Q(n)+1). The extra j=Q(n) value ensures metadata is nonempty even when Q(n)=0.
The proof-only validity predicate excludes j>=Q(n), malformed/noncanonical prefix data,
incorrect lengths, and false relation witnesses. Invalid g values are zero. The machine
only uses the existing total decoders. Actual metadata is injected by List.ofFn_get and
published encoding bounds. Repeated phases have at most Q(n)*k(n) slots, each of size at
most B(n), so the prefix encoding bound is Q(n)*k(n)*(2*B(n)+2). Nested pairEncode and
unary j give an explicit syntactic polynomial advice bound. Choices at different n are
assembled by ordinary classical choice, then fed to exists_withAdvice.

## Existing machine APIs to reuse

- NUPPT.exists_withAdvice, Complexity/Randomized/Closure.lean:358: one polynomial-length
  beta(n) is paired with each argument, same coin polynomial, exact runAtL equation.
- NUPPT.exists_compParam at241 and exists_comp at272: deterministic polynomial-time
  pre/post-processing, with explicit parameter-aware version. Use to canonicalize a
  phase view and decode metadata, not to simulate fresh suffix randomness.
- NUPPT.exists_seq at421: fresh independent coins for randomized suffix generation
  followed by D, with input pass-through paired to the first output. Precompose D with
  pairSndD via exists_comp when only the suffix output should be tested.
- exists_withAdviceOn, Games/Forwarding.lean:192, is the oracle/codec variant and is
  unnecessary for a plain view distinguisher using runAtL.
- b's SuffixMachine.phaseSuffix_poly and phaseSuffix_raw_poly provide the total uniform
  polynomial-time normalized suffix. It preserves arbitrary initial prefixes and
  appends bounded normalized messages; no raw simulator output size enters the prefix
  invariant. The root and b retain ownership of its source/checks.

## Remaining concrete reduction obligations

1. Use the efficient phase verifier with phaseAux encoding (x,z,fixed full verifier tape,
   phase,prefix); original base ZK returns one uniform simulator S for this adversary.
2. Define the machine that normalizes the one raw phase view using advised metadata,
   adds empty padding, simulates the remaining Q-j-1 phases with independent S blocks,
   replays the final repeated view, and calls the given distinguisher D. This computation
   uses no witness. Keep all concrete preprocessing total on malformed inputs.
3. Prove its runAtL/readers on valid metadata, with public coin-split/equivalence readers.
   Apply exists_withAdvice only after choosing a*(n), before requesting epsilon from ZK.
4. Apply the base-ZK bound at selected valid metadata uniformly in y; invalid metadata
   contributes zero. Use abs(epsilon) for the selector nonnegativity premise.
5. Actual prefix distributions may depend on unbounded witnesses, which is harmless:
   every valid conditional gap already has the same uniform bound. Average sections
   with the existing absolute-expectation inequality, then telescope Q hybrid gaps via
   abs_sub_le_sum_hybrids. Negligible.polyExpr_mul closes Q(n)*abs(epsilon(n)).
6. Handle zero repetitions and zero original rounds at their endpoint readers; do not
   manufacture a phase index or use a false nonempty Fin 0 instance.

## Search, overlap, reuse, and promotion

Nearest finite selector: ColZK.exists_hidingView_bound in
ZeroKnowledge/ThreeColoring/ColZKMachine.lean:323 (Finite.exists_max application at336).
That theorem maximizes over a finite triple of colour vectors and bounded advice; all
its hidden indices are finite. It does not handle an arbitrary witness domain and its
specialized commitment conclusion cannot supply the new general implication. No proof
was copied. Advice directly reuses Mathlib Finite.exists_max, le_csSup, and csSup_le;
there is no duplicate maximum or supremum proof. Promotion request: this general
bounded-family selector belongs in a future shared order/probability helper if accepted.
It stays in the topic helper because all existing files are frozen.

Nearest hybrid examples: ColSimLemmas.exists_hybRed_ge in ThreeColoring/SimulatorLemmas.lean
uses exists_hybrid_gap and a worst finite prefix; exists_colHidingRed in ColZKMachine.lean
uses exists_comp/reparam/withAdvice. The present route reuses their PUBLIC closure APIs,
not either protocol-specific proof. ColZK.distAdv_le_one and Negligible.polyExpr_mul are
published general bounds and should be reused directly (no duplicate supporting lemma).

New precise direct imports for Advice are Mathlib.Data.Fintype.Lattice and
Mathlib.Data.Real.Archimedean. Both pinned .olean files already existed in the shared
cache. The lead approved the imports and owns roots/pin/cache verification; seq-zk-c
ran no Lake/cache command. All Lean checks use the shared slot wrapper and own tree.
