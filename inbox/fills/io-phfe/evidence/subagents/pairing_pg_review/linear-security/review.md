# Linear semi-adaptive security draft handoff

Status: statements-only M0 draft; no Lean/lake/build command was run by this agent. All
substantive theorem bodies are term `sorry`; all definition readers use term `rfl`.
Exact?/apply? probes remain deferred to the parent under the single-slot check route.

## Files and interpretation

- Data.lean: typed scalar challenge, group-matrix key query, bounded next-move adversary,
  deterministic refusal protocol, fixed polynomial scalar tape and actual coordinate readers.
- Keys.lean: masked ciphertext, honest-key basis decomposition, high projections and actual
  semisimulated group key formula.
- Games.lean: six explicit Games 0--5 handlers, deterministic interpreter and sampled laws.
  Only Games 2--5 return false on singular H; the endpoints and Game 1 remain unfiltered.
- Reductions.lean: finite fixed-prime scalar advice, canonical encoding, explicit first
  ciphertext and second adaptive-key L2 handlers and reduction functions.
- Theorems.lean: advice, adaptive-law, computational-hop and combined inequality statements.

The real and ideal sampled endpoints use the common padded tape, whose coordinate
restrictions supply the actual honest or simulator algorithm draws. The endpoint reader
`game0_real_accept` currently only names the two padded presentations; the substantive
fresh-core-plus-draw endpoint correspondence must be connected when the outer generic raw
interface is assembled. Do not count that named theorem alone as proving the fresh-oracle
coupling. The relevant intended proof route is Games.Tapes + per-query relational simulation.

## Exact semantics

Budget counts ALL oracle calls and is passed to buildComp/runDet without +1. Keys before
challenge, repeated challenges, and keys beyond the cap return none without modifying the
state. Accepted keys consume one previously unused padded block. q padded key blocks suffice
because the entire interaction has at most q calls. Function-dependent node coordinates
are embedded using PG.mCoord/PG.tCoord and mCount_le_mBound, with no new Sigma Fintype.

First challenge is MDDH with one response column and three base rows. The second challenge
has ell response columns and mBound*q base rows, shared across all adaptive keys. Row
(node,query) is node*q+query. Its two base coordinates supply GROUP R; response coordinates
supply GROUP uhat. No handler samples, extracts exponents, or decodes group words.

The exact rank failure is charged once by a common-good-event comparison of both endpoint
acceptances. The first hop is unfiltered. Every middle Game 2--5 is good-filtered. On bad H,
the difference of endpoint conditional acceptance values is at most one; this avoids the
invalid naive triangle that adds two rank losses. Core theorem has two MDDH advantages and
one Linear.linearSlack. It quantifies forall typed A, exists advice, forall realisers, forall
kappa. No realisability assumption quantifies over all typed adversaries.

Lemma 3 uses the triangular exact change of variables U'=U, W'=W+a*z*,
V'=V+a*((c^T U)X(x*)). The unchanged latent U is required to compute the V shift; both public
projections and adaptive challenge selection are fixed, and subtracting the same shifts
is the inverse. Proof must track this conditional law rather than claim that U itself
is determined by public projections. Lemma 5 uses exact partial garbling privacy; group
representatives may be chosen only inside a proof, never returned by an algorithm.

## Source reading

Verified and visually inspected Wee20 complete pp. 12--14 (Appendix B, Games 0--5 and
Lemmas 2--5), in addition to all earlier source pages. No PDF was copied. Source notes and
page images remain under /private/tmp/io-phfe-source-review/pairing/.

## Reuse and search inventory

- OracleSpec, Move, QueryLog, buildComp: Games.Machines, published buildComp readers.
- FE.Run runDet and simulate_buildComp_detImpl_eq_pure: reused, no second interpreter.
- Games.Relational expect_simulate_rel/prob_simulate_rel/expect_sample_rel: adaptive coupling.
- Games.Tapes freshImpl, tapeImpl and expect_simulate_tapeImpl: fresh padded coordinate law.
- LamportReduction.exists_expect_sample_le and shared abs-expect bound: advice fixing.
- Pairing.Exponents groupMatMul/matMulGroup/groupVecMul/groupDot: all group actions.
- PartialGarbling.Raw recVec, rec_spec, reconstruct, mCoord/tCoord, mCount_le_mBound and
  exactPrivacy: no local privacy interface or reconstruction definition.
- MatrixDH.Parameters order_eq_of_publicParams/orderSchedule_neZero: prime schedule casts.
- Mathlib ZMod.ringEquivCongr/ringEquivCongr_val: scalar advice transport.
- Encoding.Modular.encodeVector and readers: no scalar codec variant.
- Asymptotic.Realization RealizesOn and verdict readers: no local realisation predicate.
- Parent-authorized BB1Machine.order_le_two_pow (via MatrixDH.SelfReduction import): only
  width reuse; undesirable low-level-to-IBE dependency already disclosed for promotion.

Full-name searches for SecurityDraw/securityCount/securityAt/paddedDrawIndex/challengeUhat,
red0Handler/red1Handler/linear_saSimAdv_le and conclusion-shape searches were run against
TCSlib and pinned Mathlib. No prior full name was found. Short generic names Advice,
SAAdv, saSpec, game and red0 are namespace-local and their nearest analogues are the shared
FE games and this draft's sibling modules. No new generic probability lemma is introduced.
The exact?/apply? stage is pending parent-only Lean checks, not silently marked complete.

## Parent check attention

These are unelaborated M0 drafts. Check dependent Bool oracle matches and Fin product
coordinate arithmetic first. The public PG node-bound spelling is mBound with
mCount_le_mBound; the reconstruction field is recVec. Before copying older scratch Pi
files ensure this same rename remains present. All substantive sorries need ordinary
proofs after statement review; no correctness or security claim is reported proved here.
