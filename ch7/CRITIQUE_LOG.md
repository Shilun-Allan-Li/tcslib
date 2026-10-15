# Chapter 7 critique log

## U5 (math half, PrimalityMath.lean) — round 1 — VERDICT: PASS
Small-case checks: N=9 → 2 liars, N=15 → 2, N=561 → 80 (≤ 280), N=13 → all pass. Proof covers prime powers (witness 1+N/p) and squarefree composites (CRT).
- [Advisory] PrimalityMath.lean:410,417 — private bitsVal_lt / bitsVal_injective_of_length_eq duplicate Codec/Word.lean:458,341, BinaryArith/Basic.lean:56, Fingerprint.lean:79 → U11: move bitsVal_lt_two_pow + injectivity into Machines/Bin.lean.
- [Advisory] PrimalityMath.lean:407 — `open Complexity.LogProg (bitsVal)` collides with U6's Randomized.bitsVal (Fingerprint.lean:71) → unify onto LogProg.bitsVal.
- [Advisory] :495,522 — class half must decide N=2 / even N deterministically, and pad ℓ*2 bits to polyLen (randProb_take).
- [Advisory] :26–33 — Main definitions omits jacobiSymZMod.

## U10c (NARMProb.lean) — round 1 — VERDICT: PASS
Abstract side = one fair coin per `choose` (nastep det ignores bit); T genuinely free; LHS ≡ FinNDTM.outputProb (PTM.lean:127). Positive-control axiom sweep caught planted sorry.
- [Advisory] NARMProb.lean:59–107 — randProb_const/drop/one_eq/succ are area-wide helpers → U11: move to Randomized/Classes.lean; randProb_succ = b=1 case of RandomWalk.lean:101 randProb_append.
- [Advisory] SpaceComplexity.lean facade lacks NARMProb import → orchestrator registers.
- [Advisory] :305–312 — optional corollary stated with FinNDTM.outputProb.
- [Advisory] :350–364 — T per input, unbounded; if BPL/RL needs poly time, a config-counting argument is needed; uniform neighbour needs power-of-2 degree.

## U3 (Median.lean) — round 1 — VERDICT: PASS
Strict-partition divergence verified against the printed step 4 ("ai ≤ x"): on [a,a], k=1 the printed algorithm loops forever. Expectation is the full ∑' over a PMF (no lost mass); recurrence proved, not assumed.
- [Advisory] Median.lean:39–42 — add the [a,a], k=1 non-termination example to the divergence note.
- [Advisory] Median.lean:314–339 — findKthElement_comparisons_le (24 lines) lacks a proof sketch.
- [Advisory] Median.lean:230–234 — findKthElement docstring 5 lines → trim.

## U1 (PTM.lean, Inclusions.lean) — round 1 — VERDICT: REVISE
- [Blocking] Inclusions.lean:156-188 — mem_NP_of_inRP_polyTimeModel (~30 lines) lacks a proof sketch.
- [Blocking] Inclusions.lean:43-50 — Ex 7.4 is stated for PTMs in print; certificate-form divergence unrecorded.
- [Advisory] PTM.lean:40-44 — output convention: non-0/1 outputs; class equality secured by U2.
- [Advisory] PTM.lean:45-46 — record c=0 / T=0 degenerate case and the n^c+1 padding.
- [Advisory] Inclusions.lean:130-134 — add unconditional InCoRP.inBPP_polyTime.
- [Advisory] PTM.lean:58-65 — exists_ofFn_of_randProb_pos belongs in Classes.lean (U11).
- [Advisory] PTM.lean:240-259 — sketch for BPDecidesInTime.flipOutput.
- [Advisory] Inclusions.lean:190-258 — BPP⊆EXP, NP=P⇒BPP=P, 3SAT corollary certificate-only → PTM forms after U2.
Sent back to the U1 formalizer.

## U7 (math half, MatchingMath.lean) — round 1 — VERDICT: PASS
det ≠ 0 ⇔ perfect matching holds over every nontrivial comm ring (incl. char 2); n=0 consistent; hypotheses of lovasz_test_zmod satisfiable (n=3,k=3,p=11,m=27).
- [Advisory] :326–381 — bitBlock/blockEquiv/randProb_bitBlock duplicate Fingerprint.lean blockVal/blocksEquiv/randProb_blocks → U11 hoist one copy.
- [Advisory] :543 — exists_prime_two_mul_lt_le unused and not suitable (p ∈ (2n,4n] needn't exceed 2^k) → delete unless used.
- [Advisory] :305–322 — two_mul_card_eval_eq_zero_le → move to SchwartzZippel.lean (added lemma).
- [Advisory] :466–472 — trim lovasz_test sketch.

## U10b (RandomWalk*.lean) — round 1 — VERDICT: REVISE
Math verified: missProb = Pr[τ>j], hitTime = E[min(τ,N)], energy argument finite and non-circular, mult_symm encodes reversibility, padGraph valid, 100n⁴ walk matches the book.
- [Blocking] RandomWalkPad.lean:162 — Randomized.bitsEquiv duplicates Fingerprint.lean:103; importing both fails.
- [Advisory] RandomWalk.lean:101 — randProb_append → Classes.lean (U11); NARMProb randProb_succ is its b=1 case.
- [Advisory] RandomWalk.lean:65 — card_filter_cast duplicates Mathlib Finset.natCast_card_filter.
- [Advisory] RandomWalk.lean:175 — cross-reference Expander.mulVec_uniform.
- [Advisory] RandomWalkHitting.lean:156 — returnTime definition vs docstring.
- [Advisory] RandomWalkHitting.lean:356 — add [AB09, Exercise 7.11(d)] tag.
- [Advisory] RandomWalkPad.lean:165 — record that the walk is on padGraph.
Sent back to the U10b formalizer. NOT_FORMALIZED additions: Ex 7.11(b); Ex 7.11(e)'s probability transfer.

## U6 (math half, AlgCircuit.lean, Fingerprint.lean) — round 1 — VERDICT: REVISE
Fingerprint arithmetic re-derived and correct; error 1−(15/16)(3/4) < 1/3; Eff obligation true for polyTimeModel; ZEROP orientation matches InCoRP.
- [Blocking] AlgCircuit.lean:50-51 — divergence wrongly claims the book's value bound ignores additive doubling (it holds for X ≥ 2).
- [Advisory] AlgCircuit.lean:24-26 — record last-node output / dead nodes.
- [Advisory] Fingerprint.lean 609 lines → split random-bit helpers into RandomBits.lean (also the dedup hub).
- [Advisory] duplicates: bitsVal_lt (Codec/Word, BinaryArith, PrimalityMath), blockVal/blocksEquiv/randProb_blocks vs MatchingMath bitBlock, randProb_append_ge vs RandomWalk randProb_append.
- [Advisory] :343-367 sketch for prob_exists_not_dvd; :435-488 boundary comments.
Sent back to the U6 formalizer.

## U1 — round 2 — VERDICT: PASS (orchestrator re-check)
All round-1 items verified in source: sketch at Inclusions.lean:167; Ex 7.4 in the certificate-form divergence bullet; output convention and c=0 notes in PTM.lean; InCoRP.inBPP_polyTime added (:140); flipOutput sketch. `lb.sh …Inclusions` BUILD EXIT 0 (build-052654-42685.log).

## U10b — round 2 — VERDICT: PASS (orchestrator re-check)
bitsEquiv now only in Fingerprint.lean:101 (RandomWalkPad imports it; joint build EXIT 0 per formalizer); card_filter_cast removed; Expander cross-ref (RandomWalk.lean:49); 7.11(d) tag (Hitting:356); padGraph walk divergence (Pad:46); returnTime docstring reworded.

## U6 (math half) — round 2 — VERDICT: PASS (orchestrator re-check)
False divergence removed; book's exact bound added as AlgCircuit.abs_eval_le_pow (X ≥ 2), abs_eval_le now its corollary; single-sink divergence recorded; random-bit helpers split into RandomBits.lean (Fingerprint 609 → 458 lines); prob_exists_not_dvd sketch (Fingerprint:184). Rebuild of RandomWalkPad + Fingerprint: BUILD EXIT 0 (build-053002-47481.log).

## U2 (PTMEquiv.lean + Nondeterminism.lean additions) — round 1 — VERDICT: REVISE
Equivalences genuine both ways; BPP_PTM neither empty nor everything (UHALT ∉, P ⊆); mask contract honest; RP soundness transfers; Ex 7.4 statement implies the book's. Nondeterminism.lean: 126 insertions, 0 deletions.
- [Blocking] PTMEquiv.lean:59 — Randomized.randProb_succ collides with Coins.lean:61 (U8) → private now; hoist in U11.
- [Advisory] :138,144 indicator lemmas duplicate TQBFHardBridge/ARMKit/Codec → U11 hoist.
- [Advisory] randProb_drop_take/length_maskSelect/maskSelect vs NARMProb/RandomBits/contSelect → U11.
- [Advisory] :353 page 126 → 131.
- [Advisory] :317–340 p must be positive.
- [Advisory] Nondeterminism.lean:4415–4420 sketch in English; :4381 blank line.
Sent back to the U2 formalizer; U8 told to make its randProb_succ private.

## U2 — round 2 — VERDICT: PASS (orchestrator re-check)
randProb_succ now private; page tag, positivity note, English sketch, blank line fixed. Build EXIT 0 (build-053912-57722.log). Nondeterminism.lean: additions only.

## U8 (ExpectedTime.lean, Coins.lean) — round 1 — VERDICT: REVISE
ExpTimeLe faithful to E[T] (prefix stability via runWith_of_halt); Def 7.7 faithful; Markov truncation matches §7.4.2; Lemma 7.13 exact and bound matches print; Lemma 7.12 coin-level (divergence accepted).
- [Blocking] ExpectedTime.lean:55-59 — Ex 7.6(a)/Thm 7.8 tie for Def 7.7 ZPP missing; cheap half (ZPP_PTM, ZPPAbort_PTM ⊆ InZPP polyTimeModel; ZPP_PTM ⊆ RP_PTM ∩ coRP_PTM) needs no new machine.
- [Blocking/orchestrator] converse directions need hosts: (i) restart host (2–4k lines), (ii) three-valued host (0.5–1k), (iii) clocked runner (0.6–1.2k) — assign or SKIP.
- [Advisory] truncation two-sided; class-level §7.4.2; Lemma 7.12 time content (∑ i^c 2^-i); Lemma 7.13 limit; sketches; biasedProb vs biasedProbability; randProb_succ_cons dup.
Sent back to U8 for the cheap half + advisories. Converse hosts assigned to a new unit U8b.

## U9 (Reductions.lean) — round 1 — VERDICT: REVISE
NP/poly standard (inputs count toward size ⇒ certificate length polynomial); printed Def 7.16 has B/C swapped (recorded); amplification arithmetic correct at every n.
- [Blocking] :103 le_randProb_append duplicates RandomBits.randProb_append_ge.
- [Blocking] :150 blockCount_add_not duplicates Space.lean:333 (facade clash).
- [Blocking] 900 lines → split NPPoly.lean.
- [Advisory] amplify_concrete reuse; union bound → Classes (refactor adleman); dead have at :711; "3SATᶜ" wording; NP_subset_NPPoly tag; SURVEY rows 45–47, Ex 7.7/7.8 update; NOT_FORMALIZED row for Ex 7.8 collapse.
Sent back to U9.

## U4 (ClassP/BinaryArith/*) — round 1 — VERDICT: REVISE → fixed by orchestrator
Every PolyTimeComputable statement is about the intended function; orbit bounds discharged unconditionally; loop termination via measures; positive-control identifier sweep.
- [Blocking] ModPow.lean:337 gcdLoop docstring "|z|+2 rounds" vs 2(|z|+1) → FIXED by orchestrator (docstring only).
- [Advisory] Basic.lean:78, AddSub.lean:111 docstrings; Basic.lean:332 sketch; Iterate.lean Main definitions; iterate_invariant ≈ Function.Iterate.rec; lt/le/beq_mem_P wording; facade intro trim; generic names (gcd) ambiguous under `open`; bitsVal_lt_two_pow 4th copy (U11 hoist to Bin.lean); register facade in ClassP.lean.
Advisories relayed to the U4 formalizer (after DetMod).
## U4 core — round 2 — PASS (orchestrator: the only blocking item was the docstring fixed above)

## U9 — round 2 — VERDICT: PASS (orchestrator re-check)
Split into Reductions.lean (376) + NPPoly.lean (522); duplicate le_randProb_append removed (uses RandomBits.randProb_append_ge); blockCount_add_not private; dead have removed; 3SATᶜ wording; tag added. `lb.sh …NPPoly` EXIT 0; no sorry. Formalizer's co-import check (NPPoly+Space+RandomBits+RandomWalk) clean.

## U10a (Space*.lean) — round 1 — VERDICT: PASS
Printed Def 7.18 has no running-time clause; all-branch halting with a uniform T forces poly time (not formalized, not needed). RL soundness faithful. amp_outputProb honest (independent blocks, fresh tapes, rewinds), space O(s) for constant r.
- [Advisory] Space.lean:333 blockCount_add_not — duplicates (Reductions private copy, NPPoly inline) → U11 hoist into Classes.lean.
- [Advisory] Space.lean:46-50 reword halting reading (AB leave halting implicit); note poly-time consequence.
- [Advisory] Space.lean:55-58 → NOT_FORMALIZED rows: Ex 7.9; polynomial-repetition (2^{-n^d}) error reduction in log space.
- [Advisory] Space.lean:73,85,344 machine lemmas placement; SpaceAmplifyRun.lean:47 halted_of_le ≈ HaltsWithin.mono; tags on amp/amp_haltsWithin/amp_outputProb.

## U8 — round 2 — VERDICT: PASS
Round-1 blocking resolved (ZPP_PTM, ZPPAbort_PTM ⊆ InZPP polyTimeModel ⊆ RP∩coRP). BPDecidesInExpTime faithful (sup reading) and non-vacuous; BPP_ExpPTM = BPP_PTM. Co-import with Space, NPPoly, RandomWalkPad, aggregator clean.
- [Advisory] ZPPEquiv:126 title; ExpectedTime:589-611 InZPP.restart sketch; Main results list; BPTIMEExp helper; RP_ExpPTM = RP_PTM analogue (cheap); ExpectedTime 613 lines.

## U5 (class half, Primality.lean) — round 1 — VERDICT: PASS
Orientation correct (N=2 false, odd primes never flagged, non-primes <2 or even accepted w.p. 1); liarRound = IsEulerLiar via BinArith; 8N ≤ 2^(|x|+3).
- [Advisory] :37–38 explain why trailing-zero encoding preserves the class (P-decidable restriction / poly-time normalization); optional canonical corollary.
- [Advisory] :18, :62 "composite" → "not prime".
- [Advisory] :213–223 eff_boolVerifier_of_test → hoist to PolyTimeModel.lean/PTMEquiv (U6/U7 need it).
- [Advisory] :232 eulerLiarRounds_two_take → PrimalityMath.

## U4b (BinaryArith Words/PrimeFind/DetModMath/DetMod) — round 1 — VERDICT: PASS
Determinant genuine (#eval spot checks incl. rotations, singular, 0×0); rotation sign and zero-column finish sound; prime finder correct for n=0..11 and polynomial (unary input recorded); Words generic.
- [Advisory] DetMod 686 lines — optional split at :312.
- [Advisory] generic helpers to hoist (evenLength, isNilB_pairEncode, lt_of_mem_zipWith, getD_* vs core lemmas).
- [Advisory] PrimeFind clog bounds duplicate MatchingMath lovaszBits lemmas → move lovaszBits to PrimeFind, MatchingMath reuses.
- [Advisory] public loop internals with generic names (zipStep clash with Basic private, listStep, …) → private/specific names.
- [Advisory] register BinaryArith in ClassP.lean.

## U8b (Build/NDCombinators, NDClockHost, NDClockHostRun; Randomized/ZPPHosts, ZPPHostsClasses) — round 1 — VERDICT: PASS
Reset-without-erasure sound (ReadyAt + write-locality + AgreeShift); input head returns; no output leak; renewal bound s₀ + 16(m+1) normalized; never wrong; coin split exact with answer prob ≥ 1/4; Thm 7.8 for Def 7.7 ZPP faithful.
- [Advisory] randProb_one_eq_singleton / randProb_append_le → hoist (U11).
- [Advisory] rename Randomized.ZDecidesInTime.exists_abortDecidesInTime → Turing.FinNDTM namespace; rename poly_normal_form; tag Ex 7.6(b); coinBranch_stepWith₁ sketch pointer.
- [Advisory] stale docstrings in ZPPEquiv.lean:42–43, ExpectedTime.lean:59 → orchestrator.

## U10d (UPath*.lean) — round 1 — VERDICT: REVISE
Soundness (malformed/non-symmetric/unreachable ⇒ every branch rejects), completeness (100n⁴ walk, D ≤ 2n, ≥ 3/4), uniform coin index, log space, narm_mem_RL honest, PSem semantics right, UPATH faithful.
- [Blocking] UPathLoops.lean:44-85 psem_addOnce lacks proof sketch.
- [Advisory] sketches ups_mul/ups_lt; 6 lines > 100 chars; instance docstring; PSem/NSem dedup → Machines/ (U11).
Sent back to U10d.

## U10d — round 2 — VERDICT: PASS (orchestrator re-check)
psem_addOnce sketch added; ups_mul/ups_lt sketches; no UPath line > 100 chars; instance docstring. Comment/line-break-only changes; build EXIT 0 per formalizer.

## U7 (class half, Matching.lean, MatchingWords.lean) — round 1 — VERDICT: PASS
Axiom sweep with positive control (FormulaKit.Emit sorries detected, not reached). lovasz_test_zmod hypotheses discharged; soundness pointwise (det = 0); InRPWeak route valid incl. n = 0 (empty graph accepted w.p. 1); matrix order verified.
- [Advisory] eq_of_bitsVal_eq dup (PrimalityMath) → hoist to RandomBits; zipWith_map_map → core lemmas; lovaszRows via blockVal; adjWord shared with Path.lean; private/rename tU…tDet.

## U6 (class half, ZeroPKit/Eval/Run/ZeroP/ZeroPPIT) — round 1 — VERDICT: REVISE → fixed by orchestrator
Specs fully proved (zeropW/pitW_pairEncode, evalModW_spec, validW_iff); #eval probes agree; orientation right; sweep with positive control (FormulaKit.Emit sorries not reached).
- [Blocking] ZeroPRun.lean:58,59,404 — three new linter warnings → FIXED by orchestrator (dropped unused simp arg, split `<;>` into bullets, simpa→simp). Rebuild of ZeroPPIT chain EXIT 0, no warnings in ZeroP* files.
- [Advisory] testLen_le_polyLen_of_le dup (Fingerprint); eq_pairEncode_of_decode via eq_pairEncode_of_pairFstD_ne; hoist forLoop/getW/uHead/uRest/hasFalse/polyTimeComputable_app/_ltLen to ClassP/BinaryArith; inBPP_PITLang tag; 8 lines > 100 chars; double blank lines; Fingerprint:53-55 future tense; NOT_FORMALIZED row for the code(C−C′) map.
## U6 class half — round 2 — PASS (orchestrator: blocking items were the lint fixes above)

## U12 — round 1 — VERDICT: PASS
- [Advisory] Yap.lean:1-612 — 612 lines (target 150–600, below ~1000 split) → hoisting PolyBound lemmas brings it under 600.
- [Advisory] Yap.lean:466-507 — private polyBound_add/comp/mono/lin/const/smul duplicate private clA5Poly_add/call (CookLevin/Hardness.lean:7182,7194) → public `Complexity.PolyBound.*` next to ClassNP/PolyTime.lean:63.
- [Advisory] Yap.lean:287-302 — private lenEq_poly_mem_P/lenLe_poly_mem_P generalise KarpLipton pred_len_eq/le → public in ClassNP/PClosure.lean.
- [Advisory] Yap.lean:526,590 — [Yap83] tags lack a precise location.
- [Advisory] Yap.lean:37-38 — module doc lists Data.Core/Check but not checkLang / checkLang_mem_P.
- [Advisory] Yap.lean:62 — References cite AB09 Theorem 6.19 but no declaration uses the tag.
- [Advisory] Yap.lean:92-96 — ofFn_get_cast possibly List.ofFn_congr + List.ofFn_get.
(Advisories queued for the phase-2 cleanup pass U17.)

## U13b — round 1 — VERDICT: REVISE
- [Blocking] BPPHard.lean:42-47 — Divergences falsely says only deterministic one-tape codes exist (NDCodes.lean has CodeNDTM/NDMachineCode/EffectiveNDMachineCode; Codes2Tape has MachineCode2) and that PTMCode has "the same laws" (missing decode_encode_pad) → rewrite with the justification (fixed 2 tapes; no probability-preserving k→2 reduction), add pad law or drop claim.
- [Advisory] BPPHard.lean:132-156 — NDTM.relabelState is generic infrastructure → later move to TuringMachine/StateRenaming.lean.
- [Advisory] BPPHard.lean:84-121 — say plainly no effective PTM scheme exists.
- [Advisory] DirectedWalk.lean:73-82 — note why RegularMultigraph.hitProb isn't reused.
- [Advisory] DirectedWalk.lean:94-95 — mention Digraph.Reachable.
- Row 43 (undecidability): stop confirmed infeasible within ~600 lines (needs effective PTM scheme, code-level s-m-n, clocked universal PTM, search; est. 1300+ lines). Lawful-scheme counterexample shows the statement is false without effectivity.

## U13b — round 2 — VERDICT: PASS
- [Advisory] BPPHard.lean:147-171 — NDTM.relabelState + lemmas → later move to TuringMachine/StateRenaming.lean (queued for U17).
(Blocking fixed; axiom sweep re-run clean: DirectedWalk 35, BPPHard 63 constants; pad law verified at m>0.)

## U14 — round 1 — VERDICT: REVISE
- [Blocking] BPLInPWords.lean:50-56 — length_bits_le_of_lt / length_bits_le_self duplicate Complexity.LogProg.length_bits_le (Bin.lean:123) and Turing.length_bits_le_self (Encoding.lean:269) → delete, use originals.
- [Advisory] BPLInPCount.lean:54-63 — fixCoin is rfl-equal to fixChoice lifted → define/document as such.
- [Advisory] BPLInP.lean:118-124 — pt_app/pt_test copy BinaryArith/Loops lemmas → import Loops.
- [Advisory, cross-track] U16's SpaceAmplifyPolyCode duplicates inWin_run / coreSum_eq_of_code_eq / haltsWithin_of_codes → U16 imports BPLInPCount (sent to U16).
- [Advisory] haltsWithin_of_codes lacks an [AB09,…] tag.
- [Advisory] Space.lean:51-52,60 stale (Ex 7.9, poly-time halting now formalized) → orchestrator (U17).
- [Advisory] ch7 md files list Ex 7.9 as not formalized → orchestrator.
(Math, DP correctness, polynomial bounds, axioms (with positive control), faithfulness all verified. maxHeartbeats 0 is mandated by policy.md:105-110.)

## U14 — round 2 — VERDICT: PASS
(No findings. Blocking fixed; local notations ptA/ptT verified not to leak; axiom sweep with positive control clean: 37/34/67 constants.)

## U15 — round 1 — VERDICT: REVISE
- [Blocking] RandomWalkMixingPad.lean:54-62 — relHitProb/relDegree duplicate DirectedWalk hitProb/outNbrs (equality proved by critic) → reuse.
- [Blocking] RandomWalkMixing.lean:324-354 — cover_reach lacks proof sketch.
- [Advisory] exists_even_word sketch; k=2n corollary for D ≤ n^5 so n^{−10n} is meaningful; split the double-cover block (file at 598 lines).
- [Advisory, orchestrator] RandomWalkPad.lean:43-46 stale + direction backwards; RandomWalkHitting.lean:50-51 stale → U17.
(Faithfulness of (b), (b)(a), (b)(b), (e) verified; axioms clean.)

## U13a — round 1 — VERDICT: REVISE
- [Blocking] BiasedCoinHalting.lean:160-194 — haltCoin_mul_pow_hlJ lacks proof sketch.
- [Blocking] BiasedCoinHalting.lean:396-428 — iterate_pow4Step lacks proof sketch.
- [Advisory] BiasedCoin.lean:254-303 duplicates PTMEquiv.lean:213-260 construction → factor a structural lemma in PTMEquiv (assigned).
- [Advisory] onesW third copy of ones-filter transducer (MeyerVerifier trues, TQBFHardVerifier keepTrue, BinaryArith/Basic inline) → deferred (rebuild cascade).
- [Advisory] haltDigit restates Code.haltingSet (UHalt.lean) → cite/reuse.
- [Advisory] exercise_7_1 / exercise_7_5 not descriptive names → rename.
- [Advisory] Ex 7.1 statement lacks explicit range conjunct; two short sketches; trailing whitespace; N = A_{J−1} prefix optional; stale Scratch_U13a artefacts.
(Ex 7.1/7.2/7.5/Note 7.11 faithfulness and arithmetic hand-verified; axiom sweep with positive control clean.)

## U15 — round 2 — VERDICT: PASS
(No findings. (e) restatement proved equivalent to round 1; k=2n corollary verified incl. n=1; RandomWalkCover no duplicates; sweep with injected positive controls clean: 24/53/47 constants.)

## U13a — round 2 — VERDICT: PASS
- [Advisory] UniformSample.lean:270-271 — sketch cites `normBits`; should be `BinArith.polyTimeComputable_normBits` (U17).
- [Advisory] PTMEquiv.lean:248-252/:280-284 — hsel length computation repeated; optional conjunct.
- [Advisory, carried] onesW hoist; optional simpler Ex 7.5 language.
(PTMEquiv pre-existing statements verified unchanged; haltingSet reuse sound; facade build EXIT 0; sweep with positive control clean.)

## U16 — round 1 — VERDICT: REVISE
- [Blocking] SpaceAmplifyPoly.lean:17,31 — "space form of Thm 7.10" without recording the 2/3 vs 1/2+n^{-c} hypothesis divergence.
- [Blocking] SpaceAmplifyPolyMachine.lean:60 — PSem.of_areach (45 lines) lacks sketch.
- [Blocking] SpaceAmplifyPoly.lean:197 — polyAmp_setting (29 lines) lacks sketch.
- [Advisory] narm_logspace_ptm copies ~85 lines of narm_mem_RL → move to NARMPSem, re-derive (authorized).
- [Advisory] PSem.of_areach/of_reach/call/dec, searchUp/Down_run belong in Machines/ (authorized).
- [Advisory] 7 private ptc_* copy ZeroPRun → make public there (authorized).
- [Advisory] InRP.of_polyTimeReducible repeats InBPP's first 30 lines → shared lemma in Inclusions (authorized).
- [Advisory] PITLang_mem_coRP_PTM_of_reduction same type as PITLang_mem_coRP_PTM; AlgGate.shift_zero namespace; length_uHead_add_uRest_le placement/colon; subW sketch; script-wrapped Reg literals; stronger (1/2)^{(n+1)^d} bound.
- [Note] Space.lean:58-60 and ZeroPPIT Divergences stale → U17.
(Coin semantics, O(log n) space bound, quantifier order, malformed-input branch, U14 reuse all verified; 798-constant sweep with injected control clean.)

## U16 — round 2 — VERDICT: PASS
- [Advisory] ZeroPRun.lean:66-116 — public ptc_* names not Mathlib style → rename polyTimeComputable_* (U17).
- [Advisory] NARMPSem.lean 631 lines → optional split of the logspace bridge (U17).
- [Note] Space.lean:58-60 and ZeroPPIT Divergences stale (U17).
(narm_mem_RL / InBPP.of_polyTimeReducible statements verified unchanged by type-checking round-1 statements; stronger bound verified; 934-constant sweep with control clean; Randomized+SpaceComplexity facade build EXIT 0.)

## U11 — cross-track pass — DONE (orchestrator record)
Full `lb.sh TCSlib` BUILD EXIT 0 (logs/build-120445-83029.log, 4320 jobs); module-index axiom sweep of all 57 campaign modules + Yap + NPPoly: 0 constants outside {propext, Classical.choice, Quot.sound}; positive control TuringMachine.Nondeterministic reports sorryAx. Tracked files changed by additions only.

## U17 — phase-2 cleanup — DONE (orchestrator record)
Full `lb.sh TCSlib` BUILD EXIT 0 (logs/build-152843-9368.log, 4336 jobs; re-run after the Classes.lean docstring fix: logs/build-162537-62556.log, EXIT 0). Axiom sweep over 79 campaign modules (6292 constants): 0 bad; positive control FormulaKit.Emit reports sorryAx; 27 headline theorems ⊆ {propext, Classical.choice, Quot.sound}. `git diff --numstat 8c23f3bc -- '*.lean'`: 0 removed lines in tracked files (Classes.lean docstring edit by orchestrator afterwards: 3 comment lines). Deferred (rebuild cascade): NDTM.relabelState → StateRenaming; Yap PolyBound/lenEq/lenLe hoists → PolyTime/PClosure; onesW dedup.

## Completeness grader — round 1 — GRADE: INCOMPLETE
P1 Lemma 7.9/Thm 7.10 abstract only (→ U18); P2 Ex 7.11(d) weaker bound (→ U19); P3 RP expected time (→ U18); P4 p.129 ∏(1+xᵢ) example (→ U20); P5 BP·P = BPP (→ U18), BPP=P ⇒ BPP ⊊ DTIME(n^{log n}) and BPP=P ⇒ complete problem (→ U20); P7 NOT_FORMALIZED not exhaustive (orchestrator, done); P8 web-draft numbering + false "Erratum" in pre-existing files (→ U21 after U18–U20); P9 ℚ-only uniqueness (→ U19); P10 stale SURVEY rows 15/50, CRITIQUE_LOG lacks U11/U17 (orchestrator, done).

## U19 — round 1 — VERDICT: REVISE → fixed by orchestrator (comment-only) → PASS
- [Blocking] RandomWalkHitting.lean:436-468 — hitTime_sub_le lacked a proof sketch → added (critic's suggested text).
- [Advisory] nested backticks in two docstrings → replaced by `Pr[τ_b > M]`.
- [Advisory] vague D ≤ 100n justification → made concrete (E_{a,c} ≥ D on the 3-vertex path).
Rebuild: lb.sh RandomWalkHitting BUILD EXIT 0 (logs/build-165058-91635.log); no line > 100 chars. Statement invariance, math (first passage, triangle inequality, 1000n³ Markov, ℝ uniqueness), and axiom sweep with positive control verified by the critic.

## U18 — round 1 — VERDICT: PASS
- [Advisory] BPPAmplify.lean:120-154 — inBPPWith_of_mem_BPP_PTMWith / mem_BPP_PTMWith_of_inBPPWith copy PTMEquiv's inBPP_of_mem_BPP_PTM / mem_BPP_PTM_of_inBPP → re-derive the 2/3 case from the With form (→ U21).
- [Advisory] RPExpected.lean:83-125 — InRPWith.inRP_of_const repeats OR-amplification; legitimate (InRPWeak cannot hold a constant 5/8 at n=0) → note in sketch.
- [Advisory] BPPAmplify.lean:43-47 — note the n=0 advantage-1/6 patch and ⌈c⌉ for real c (→ U21).
- [Advisory] RPExpected docstring links to ZPPEquiv names outside import closure; BPOperator size (keep separate; Reductions is the alternative home); exists_majority_count could be private.
- [Record] Classes.lean:66-69 stale "future work" (→ U21).
(Lemma 7.9 direction verified not weaker than the book; Thm 7.10 stronger; RP truncation one-sided; BPdot_NP_eq_BPNP meaningful; sweep with positive control clean.)

## U20 — round 1 — VERDICT: REVISE
- [Blocking] BPPEqP.lean:60-72 — univ_mem_P/empty_mem_P duplicate Complexity.univ_mem_P/empty_mem_P (PClosure.lean:110,114).
- [Blocking] QuasiPolyHierarchy.lean:58-65 — bits_two_pow duplicates Turing.bits_two_pow_eq_replicate.
- [Blocking] QuasiPolyHierarchy.lean:181-185 — iterate_drop_one duplicates BinArith.iterate_drop_one.
- [Advisory] privatize generic helpers; doc credit to diagLang halves; three proof-sketch labels; IsOp → isOp; DTIME_const_mul_subset later hoist to ClassP/DTIME.lean (deferred, tracked file); BPPEqP keep separate.
(TimeConstructible honestly met; P = ⋃ DTIME(n^c+1) comparison right; hierarchy halves sorry-free; sweep with positive control clean.)
