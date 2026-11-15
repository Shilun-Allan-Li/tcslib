# Computational helper record (future work after checkpoint3)

Author: seq-zk-c. The lead owns main, frozen files, final merge/checks/axioms/seals,
commits and delivery. This record concerns only c-owned helper modules and isolated native
checks. Checkpoint3 source is04c253e48d9c0ebb73943f39412365cd4d8e02db. The first10 c helpers
match that source exactly; the five helpers below are future checked source outside it.
checked-source-snapshots.json and its exact15 snapshots record this distinction.

## Checked contributions and architecture

HybridRecursion.lean:90lines, SHA5277132bb0013c9e290f17272947624e6fd33f17fb9029608d9821affe1e92da.
The public hybrid_recursion_gap_le uses arbitrary state and continuation potential, only
finite nonempty real coin type A, supplied initial/snoc family readers, and conditional
potential drift<=epsilon at every actual prefix. It concludes end-to-end difference
<=q*epsilon. It directly reuses the existing telescope, snoc equivalence, product averaging,
and abs_uexp_sub_le. No finite state/witness bound, new iteration host or new telescope.

SuffixLaws.lean:122lines, SHA4415c221a7d3273f02c22572a20f7033071a504364cb0b5dc855c35e281f3971.
phaseStep_eq_simStep reads a supplied typed block; phaseSuffix_front separates the first
update of b's existing suffix; phaseSuffix_congr_blocks depends only on its own range;
phaseSuffix_update_before ignores an overwritten earlier table coordinate. There is no
new suffix machine or duplicate execution-phase induction. This module owns no definitions.

ComputationalAdvice.lean:74lines, SHAf7a61a8277300e179d2df45c2be4261c90429d8ad7142583ef75e967ad26cffc.
exists_uniform_negligible_bound takes finite nonempty A(n), arbitrary witnesses W,
gap<=1, a validity predicate, and one negligible bound for every selected metadata function.
It chooses metadata before epsilon by the checked Advice selector and concludes one
negligible epsilon uniformly bounds every valid gap by abs(epsilon(n)). Invalid gaps are
zero only inside the proof. No machine decides validity or witness membership. No
nonnegative-gap premise, witness encoding, witness maximum attainment, or bound on W.
Old Advice source is unchanged.

ContinuationProbability.lean:320lines, SHAa5922afe075adffb6349ba1801857125ac76ec158d4bca3faa8fc5289ee03d32.
- acceptProb_prod, acceptProb_update_tuple, acceptProb_postprocess_fst expose exact opaque
  product/update/unused-factor acceptance laws from published probability readers.
- continuationProb(+_eq) is the existing suffix acceptance potential, sampling a full
  typed table of independent S tapes and using only the suffix range.
- continuationProb_bellman uses the published acceptProb_update to reseed the current
  table entry, the front-step reader to consume it, and update_before to remove it from
  all later phases. It is exactly a fresh current simulator coin and independent suffix.
- continuationProb_real directly uses a's normalizePhaseMsgs_viewV fixed point with the
  supplied padded-prover original message count and caller's uniform prover bound. It
  removes the wrapper's zero verifier tape by opaque public averaging/projection laws.
- continuationProb_sim is the matching raw S call identity from the Bellman law.
- phaseGap(+_eq) is the SINGLE shared local raw original-view/S gap through b's
  phaseContinuation, with coin product (Fin Q -> S.Coins) x Dcoins. b's
  ComputationalPhaseBound consumes this public definition/reader; no duplicate gap.
- phaseGap_eq_drift states its exact absolute potential drift under the real next phase.
Final source has the required sim proof sketch and major-step comments. Only docs changed
between passing03 and passing04; no statements, definitions or tactics changed.

ComputationalHybrid.lean:197lines, SHA07e9f3beeaca0c2d2c4d5aa4e166cda4833412ad6b9bf5b5aba62aa888fa9bb1.
prefix_distAdv_le assumes the shared phaseGap bound for each ACTUAL realPrefix before q,
plus d, numeric p count, nonnegative epsilon and honest-message bound. It concludes the
canonical real/simulated prefix view advantage<=Q(|x|)*epsilon at fixed verifier tape.
The real/sim endpoint identities and generic potential theorem do all the work.
prefix_distAdv_joint_le averages verifier tapes. distAdv_reindex directly uses public
acceptProb_comp_equiv and supplied readers. distAdv_view_endpoints equates actual encoded
repeated-view/SQ advantage with the joint typed prefix advantage, reusing stable Endpoint.
No metadata validity, finite witnesses, weakened target or extra cryptographic assumption.
The q=0 case is included by the generic telescope; no Fin0 index is fabricated.

## Coordination and source provenance

The lead approved every new helper/API before coding. c alone edited these files. a owns
NormalizedStep and RealPrefixBounds; b owns SuffixMachine, ComputationalReduction,
ReductionAdvantage and ComputationalPhaseBound; root owns main and transfers. No helper
ownership overlap or foreign-tree edit/check occurred. In particular, a supplies ALL real
normalization and prefix-size proofs, b supplies ALL machine/advice construction and
NUPPT reduction-coin transport, and c does not duplicate them.

Only stable checked source bytes were copied from b/a, then compiled in c's own tree.
Hybrid prerequisite source manifests record exact hashes. A source-copy assertion caught
b's comment-only update from0095... to32d8... before copying; c waited for b's successful
final native check, then copied32d8... unchanged. This was provenance checking, not a proof
failure. SuffixMachine, ComputationalReduction, ExecutionBounds and a's corrected
NormalizedStep all passed native own-tree prerequisite checks. No sibling olean was used.

## Search, overlap, reuse, and promotion

Raw searches are in hybrid-searches.log; earlier advice/endpoint searches remain complete.

Nearest generic hybrid: Foundations/Probability.abs_sub_le_sum_hybrids. HybridRecursion
USES it directly; only conditional-prefix averaging and the snoc reader are new. Nearest
specialized hybrid is ColSimLemmas.exists_hybRed_ge (ThreeColoring/SimulatorLemmas), whose
protocol-specific coordinate/prefix proof does not supply the conditional state-potential
contract. Promotion request: generic conditional-family hybrid in shared probability if
accepted; frozen modules were not edited.

Suffix front/block readers are consequences of b's published phaseSuffix_succ/zero and
phaseStep_eq. None existed in the searched closure. The finite-table update proof uses
canonical FunFamily.ofFn_blocks plus Equiv.apply_symm_apply, not an entrywise copy of
GI.coinSlice_blocksEquiv. This same canonical specialization also appears as a local
reader in RepeatedSoundness; it is disclosed and directly reuses the public window law.
No independent block/window arithmetic is re-proved.

ComputationalAdvice directly reuses Advice.exists_uniform_bound_selector. Nearest existing
finite selector is ColZK.exists_hidingView_bound, which cannot cover an arbitrary witness
domain. Its finite maximum proof was not copied. Promotion request: the length-indexed
logical lifting belongs with a future shared advice/reduction helper.

acceptProb_prod's nearest relative is the local hX product computation in ColZK.exists_fixSeed;
no exact public sampler-factor averaging reader was found. It directly reuses acceptProb_def,
uprob_comp_equiv and uprob_prod. acceptProb_update_tuple SPECIALIZES the existing public
acceptProb_update (Indistinguishability.lean:103), dropping Unit via acceptProb_fst; it does
not construct/re-prove a uniform update bijection. postprocess_fst uses acceptProb_bind,
the product reader and HardcoreBit.uexp_fst. Promotion requests: these generic acceptance
readers belong in shared Experiments/Indistinguishability, which are frozen here.

continuationProb/phaseGap are topic-specific semantic leaves, with canonical_eq readers.
Bellman uses published acceptProb_update and owned suffix readers; real identity uses a's
published fixed point; sim identity uses b's phaseContinuation_eq. These helpers introduce
no probability distribution host, simulator loop, or normalization proof.

The actual q*epsilon theorem directly reuses HybridRecursion, PrefixLaws, phaseGap_eq_drift,
and both suffix endpoints. Nearest specialized bounds are the ThreeColoring hybrid and
coordinatewise pair-hybrid theorems in Commitment; they do not supply this adaptive real
prefix/simulated suffix contract. No specialized proof was copied. distAdv_reindex is only
acceptProb_comp_equiv plus supplied function equalities; promotion to shared sampling is
requested. Endpoint transfer reuses stable EndpointSampling, not a second coin induction.

## Native validation and corrections

All attempts use LEAN_SLOT_TAG=seq-zk-c, the shared lean-slot.sh wrapper, /usr/bin/time -l,
scripts/lean_check_tree.sh ONE module, and c's private seq-zk-c olean tree. All Python uses
python3 -I. Every raw output, source-attempt snapshot and structured result is retained.
No interruption, timeout, sampling, resource exception or Lake command in this task.

- HybridRecursion01: rewrite could not infer a product integrand through projections.
  Supplied it explicitly to the public expectation-equivalence reader. Attempt02 passed,
  0diagnostics,2.23s,maxRSS2,116,681,728.
- SuffixLaws01: omega saw an opaque Fin.mk.val term. Exposed its concrete value by change.
  Attempt02 passed,0diagnostics,2.53s,maxRSS2,227,847,168.
- ComputationalAdvice01 passed,0diagnostics,2.17s,maxRSS2,006,581,248.
- ContinuationProbability01: implicit product/fst reader matches and update_self name;
  fixed through explicit functions and the published correct reader. Attempt02: explicit
  Fin value and bind postprocessor needed. Attempt03 passed the complete shared gap/drift
  module. Attempt04, doc-final only, passed0diagnostics,2.35s,maxRSS2,243,788,800.
- ComputationalHybrid01: after suffix_zero, an own local realView alias goal remained;
  closed it by rfl. Attempt02 passed all four complete declarations,0diagnostics,2.33s,
  maxRSS2,231,697,408. No target or premise change.

Endpoint's separate record includes its final canonical-reader check02. The old read-only
NormalizedStep diagnostic suggestions are corrected by normalized-step-diagnosis-correction.md:
the actual cause was a missing direct Defs import, found by a/root with with_reducible.
The initial closed evidence remains byte-identical, preserving the full chronological record.
