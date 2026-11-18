# Quadratic semi-adaptive security draft handoff

Status: statements-only M0 draft. No Lean, lake, build, proof-check command, git mutation or
extra agent was used. Definition readers are term rfl; the sixteen substantive obligations
are term sorry with sketches. Exact?/apply? probes and elaboration are deferred to the root.
The root's incoming compile findings were applied: reserved local `at` became getScalar;
PolyExpr.const is explicit in dotted receivers. No source-group matrix uses matrix `*`.

## Files

- Data.lean: scalar (x,z1,z2) challenge, function-only key queries, dependent packed answers
  as DATA, exact total-budget SAAdv and deterministic once-challenge refusal protocol.
- Games.lean: actual five handlers and exact laws, with two distinct leakage formulas.
- Advice.lean: finite fixed-prime outer and linear tapes, hp-based public-order casts,
  numeric n1/n2 headers, canonical modular encodings and polynomial bounds.
- Derived.lean: pure typed replay, ciphertext/key response translation, and toLinear.
- Reductions.lean: crossLeakLeft/crossLeakRight plus actual red2/red3 handlers and functions.
- Fresh.lean: ACTUAL Quadratic.setup/enc/keyGen and simSetup/simEnc/simKey calls, threaded
  through the common oracle simulator. Ideal encryption saves the returned simulator state.
- Theorems.lean: advice/endpoint/derived-run laws, exact arithmetic hop, two MDDH hops and
  typed core. The endpoint statement compares different definitions, not two padded aliases.
- Composition.lean: dimensions, mddhSlack sum, and combined typed raw canonical-DLIN bound.

Current line/width/admission totals are in static-review.txt. All files are below 600 lines
and all lines are at most 100 columns. declarations.tsv lists all new declaration headers.
No Lean success, axiom census, Rule-10 seal, exact?/apply? result or proof completion is
claimed by these purely static checks.

## Actual games and leakage

Game 0 calls honest outer Enc core and honest Pi Key core. Games 1--4 use actual Pi simulator
cores. Game 1 supplies Linear.leak on the known scalar signal (s1 tensor z2 | y1 tensor s2)
and the fixed PUBLIC group matrix M. Game 2 rewrites that source-group value to

  g^((y1 tensor y2) eval_f(x)) / g^((z1 tensor z2) eval_f(x)).

Game 3 replaces y1 by a fresh scalar vector; Game 4 replaces y2. Game 4 is connected to the
actual stateful simulator by a substantive fresh-law endpoint theorem. No outer game filters
on singular Pi H: Pi's first computational/conditional proof already charges its bad event.

Both padded endpoints now have separate actual fresh raw-law definitions. The outer
saGame_eq_freshSaGame must prove their acceptance equality via shared Games.Tapes and
coordinate restriction. It is not satisfied by the definitional padded saGame selector.
Likewise the inner LinearSecurity.Endpoint bridge is consumed by game0_game1_le and the
Pi bound is Linear.linear_freshSaSimAdv_le. This avoids proving security only for a pair
of padded presentations detached from the raw algorithm bundle.

## Deterministic derived Pi adversary

A fixed mask tape supplies known A1,A2,s1,s2 (unused uniform y coordinates are harmless).
The derived typed next-move function reconstructs the outer log from the Pi answers by
replaying A.next on the accumulated outer log. It translates accepted ciphertexts by
adjoining the two known scalar masks, translates keys by retaining fixed PUBLIC M, and
forwards the scalar signal and each (f,M) query. It ignores foreign query payloads only
on malformed histories; reachable histories have precisely the translated queries, and
mismatched oracle indices or an impossible earlier return cause false.

Coins and TOTAL budget are preserved exactly. No +1 is introduced. Refused calls consume
one total move, but leave the committed challenge and accepted-key counter unchanged.
No function equality decision or group-word decoder is required for typed replay. This is
an internal typed adversary; the generic machine-derived adapter and alias-preserving wire
codec remain the parent/FE agent's assembly task.

## Explicit L2 reductions and dimensions

In core order the four matrix assumptions are:

  D0: one response column, 3 base rows (Pi ciphertext hop);
  D1: ell response columns, mBound*q base rows (Pi adaptive-key hop);
  D2: one response column, n1 base rows (outer first mask);
  D3: one response column, n2 base rows (outer second mask).

red2 receives GROUP A1 and GROUP response, adds known z1 in the group, and retains known
scalar y2=s2*A2+z2. crossLeakLeft computes the source-group tensor using only powers of
GROUP y1 by y2 coordinates. red3 receives GROUP A2/response and retains known uniform
scalar y1, using crossLeakRight. Both supply exactly those source-group values to Pi's
simulator and never sample or extract exponents. Random response plus adaptively selected
z remains uniform by Equiv.addRight, because z is selected from the fixed public history
before the hidden response is revealed. The same reasoning holds at zero dimensions.

quadratic_saSimAdv_le states forall typed A, exists mask advice, exists two Pi-advice
families, exists two outer-advice families, forall four realisers, forall kappa. Its left
side is ACTUAL freshSaSimAdv. There is no hypothesis over every typed adversary. All four
realisability premises display the concrete functions Linear.red0/Linear.red1/red2/red3.
The typed core can later be specialized to a machine-derived outer adversary only.

quadratic_saSimAdv_dlin_le then chooses four L1 advice families after the four MDDH
machines but before ANY DLIN realisers. Response-column factors are 1,ell,1,1. Its loss is

  quadraticSlack = Linear.linearSlack + 3*mddhSlack(p,1) + mddhSlack(p,ell)
                 = ONE exact unconditioned 3x3 rank failure + 4*(ell+3)/p.

The direct canonical-JLS column reduction already accounts for zero-coordinate failures.
Do not add Linear.dlinMatrixSlack a second time. This is the explicitly disclosed
polynomial-loss column route, not a claim to reproduce the source's cited tight reduction.

## Source fidelity

The verified Wee20 PDF was read IN PLACE, all fourteen pages rendered and inspected.
Section 3.1 and equations (4)--(5) are p6; simulator section 3.2 is p7; section 3.3 Games0--2
are p7 and Games3--4 are p8. This corrects earlier broad p7 citations for all five games.
The source's unused s0 is omitted. Its source/target group tags are read as authorized W2--4:
all allowed Pi leakage and cross terms are SOURCE-group values. In the symmetric setting
both public source copies of A1 coincide, so canonical DLIN supplies the bilateral use.
No new source-level obstruction was found. The already disclosed source 1/p rank error,
canonical DLIN matrix-presentation discrepancy, latent-U change of variables and positive
source-domain efficiency guard remain as previously reported by the root.

Raw algorithms and security remain total at zero n1,n2,ell and q. No source-domain positivity
hypothesis or efficiency target has been inserted into the typed raw security statements.

## Overlap/reuse inventory

- Uses Games.Machines Move/QueryLog/buildComp and their bounded-run semantics.
- Reuses FE.Run runDet and its published bridge; no second oracle interpreter is defined.
- Uses Games.Relational and Games.Tapes for adaptive fresh-draw and state-abstraction laws.
- Fixes finite advice via LamportReduction.exists_expect_sample_le and shared absolute
  expectation/advantage inequalities; no new averaging/hybrid/triangle lemma is introduced.
- Uses the already drafted LinearSecurity actual handlers, advice and two reductions,
  especially its fresh-law Endpoint theorem. No partial-garbling proof is copied.
- Reuses Quadratic mixGroup/signalScalar/value and QuadraticCorrect tensor identities;
  scalar representations occur only for known sampled/advice scalars.
- Reuses Pairing.Exponents groupDot/group products/exponent transport for mixed leakage.
- Uses shared Parameters.order_eq_of_publicParams/orderSchedule_neZero and Mathlib's
  ZMod.ringEquivCongr; no local order-cast lemma or group-to-scalar primitive is defined.
- Uses Encoding.Modular.encodeVector and published length/injectivity results. Existing
  BB1Machine.order_le_two_pow remains the authorized width dependency through MatrixDH;
  the previously requested promotion to a common pairing file still applies.
- Uses shared RealizesOn and MatrixDH.mddhAdv_le/dlinToMddh/mddhSlack as-is.

Disclosed near-copies: the outer two-branch typed refusal protocol is the same four-case
shape as Linear.protocolHandler, with distinct challenge/key/response families; no generic
protocol abstraction was added. Scalar advice transport and vector-encoding metadata mirror
Linear.adviceDraw/adviceEnc for a DIFFERENT tape length and include separate n1,n2 headers.
These are interface glue definitions with new readers; no existing mathematical theorem is
re-proved. Generic helper promotion is left for a later scope opening if requested.

Searches were run against TCSlib and pinned Mathlib for MaskAdvice/maskAdviceDraw,
maskAdviceEnc/maskAdviceLen, replayLinear/toLinear, crossLeakLeft/crossLeakRight,
publicFromMasks/maskedVectors, derived_run_endpoint, quadratic_saSimAdv_le and
quadratic_freshSaSimAdv_le. No existing full Quadratic namespace name was found. Mathlib
has unrelated toLinear/toLinearMap methods in algebra namespaces; they are never used
unqualified here. Readers are attached to every new def/abbrev, and replay has nil/cons
readers. exact?/apply? is explicitly PENDING ROOT rather than silently marked passed.

## Suggested first elaboration attention

Check dependent simultaneous Bool/Sigma matches in replayLinear, then the function-dependent
key packs in fresh handlers. Check scalar positive-order coercions at Pi calls, although
these new files do not multiply PG.L0/L1 matrices. All multiplication of source-group
MATRICES was avoided here; only group VECTOR multiplication occurs. Numeric dimension
headers and the advice encoding bounds need the standard published word-length readers.
