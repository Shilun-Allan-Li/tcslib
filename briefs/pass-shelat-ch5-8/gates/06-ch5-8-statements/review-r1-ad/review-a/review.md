# Gate06A round 1 — independent intake review

**Accepted: 0 additional blockers / 0 majors / 0 minors.** The incoming 0B/0M/2-minor statement-gate verdict is supported at frozen `3f6db40e1688c4a0bb922c9575dd3bd2157a650b`, records `c81baa7712ab1b43357276ef5df138d02616c9d0`, exchange `5928e06c02b382b63b9b384db89d0458b520f351`. Its limited 06A closure is defensible. This is not security-proof completion, clearance of other prongs, or PR merge clearance.

The 46,660-byte findings match SHA-256 `03782b01b654595b437ebfd408bd6b7a628dbdf2bb2b47e0280f2fd3e13e8bd5` and the verbatim blob at intake commit `9db11986edfce462d91958856a763577ee15457f`. I read the full report as data and inspected frozen Authentication definitions, correctness and security statements/sketches with the relevant sampler, OWF, handler and advice contracts. The companion JSON pins those sources.

## A-01 — accepted sampler correction

The frozen construction draws `w` by `sampleBelowL m (Nat.size m) n n`, uses fallback0 and sets `y=g^w`. It is not generally exactly uniform. Independent enumeration of three values from `{0,...,7}` at n=3,m=4 reproduces all 512 tape outcomes: `(176,112,112,112)`, or `(11/32,7/32,7/32,7/32)`. Total variation from uniform is 3/32, below 2^-3. The group instance p=5,g=2,m=4 preserves that bias under its exponentiation bijection. More generally, pushforward never increases statistical distance; ideal uniform exponents give uniform group elements.

The existing `dlHash_crh` sketch230–233 already pays the sampler's 2^-n error, and its compression claim is eventual with valid full-group indices. Changing the module gloss to “within 2^-n of uniform” is the needed correction; no theorem premise, game, domain, compression claim or algorithm changes. The source's prime-order/full-group distinction remains explicit.

## A-02 — accepted coupling and machine route

For n>=1, first sample an honest Lamport key and honest adversary execution, then independently choose a planted pair(i,c). Equivalently, replace that key entry by an independently sampled OWF challenge; conditional on(i,c), all other preimages retain their honest independent distribution. On a successful queried run with fresh m', the favorable pairs are exactly `m_i != c = m'_i`. There is one favorable c per differing coordinate, so their fraction is `Hamming(m,m')/(2n) >=1/(2n)`. On a no-query successful run, one c works at every coordinate, giving exactly1/2. Thus for mixed runs:

`Pr[invert] >= epsilon_query/(2n) + epsilon_noquery/2 >= epsilon_total/(2n)`.

This counts a joint event in the honest-run coupling. It does not multiply probabilities after conditioning on non-abort, where independence would be false (query0^n implies c=1 on non-abort). Extraction needs any preimage of y; no injectivity assumption on f is necessary. The n=0 exception is finite for negligibility and does not weaken all-parameter correctness.

A best position i(n) can maximize the *unconditional* fixed-position inverter's success over the random challenge, other key entries, A's coins and fair c. It is chosen per n,A,f before the random challenge; it cannot depend on the observed challenge. Its success is at least the uniform-position average. The advice costs O(log(n+1)) bits and is permitted by `StrongOneWay.hard`, which quantifies over every NUPPT. There is no need for exact uniform sampling from[n] with a fixed bit tape or an unaccounted sampler loss.

The initial proposed step5 did not spell out how the handler receives this position: `PolyHandler.advIn` sees `seedIn(n,z,omega)`, not an implicit advice slot. Root incorporated the precise existing route into the revised comment: T1 on extended input`<y,i(n)>`, followed by `NUPPT.exists_withAdvice` (`Closure.lean:360–363`). That wrapper supplies bounded advice, preserves the coin schedule and adds no hypothesis. Independent finite checks verified the favorable-pair identity for 5,334 fresh ordered message pairs and126 no-query messages over n=1,...,6; these checks support the counting only, not a formal cryptographic proof.

## Proposal identities and noncomment preservation

- Initial six-file patch SHA-256: `157964e06e8cd6da8f48ca0be44a47f5eeceebfaa412dad2b4a7ef453653bf0d`, retained under `corrections/initial-proposal/`.
- Final six-file patch SHA-256: `3c5c98acb21f7e252105a1f64be04fea760d2388b60d1fd22dfa954b25c5987a`, current `corrections/minor-prose-corrections.patch`.
- Both Authentication hunks were independently applied to frozen bytes in memory, with every context/removal byte and hunk count checked. Old and proposed noncomment byte streams are exactly equal. Consequently the algorithms, declarations, theorem headers, proofs and admissions are unchanged. Proposed DLHash hash: `c1df149e6a978d3491314108665349dd93747d86fe980f0f36e4f41da4303bf7`; proposed Lamport hash is pinned in JSON.
- The four non-Authentication patch sections are byte-identical between the initial and final proposals. They are not substantively reviewed here. No patch was applied to a checkout or committed by this reviewer.

## Closure and retained qualifications

The source-only manifest was independently checked against frozen Git: exactly124 modules in the Authentication import closure plus `TCSlib.lean` context, all125 path/revision/length/raw-hash rows matching; root was not recursed or elaborated. A source count independently matches53 written definitions/abbreviations/structures and96 written theorems across the five constituent modules. This supports report coverage, not proof validity by counting.

The historical axiom JSON has278 Authentication actual identities and exactly five sorryAx-dependent names: four direct substantive security statements plus derived `exists_oneTimeSecure_of_crh_owf`. I inspected that JSON, not a fresh kernel census. The short correctness constructions remain distinct from those substantive admissions. The report correctly keeps other source seal failures, inherited reads and legacy C3 pairs as observations, not passes.

Preserve A-03: `hdom` is sufficient but not logically minimal; the current strong full-domain hypothesis must remain in downstream uses. Preserve A-04: the existential result is for `H.domLen(n)`-bit messages under D-3, with no supplied arbitrary-string construction. Freshness is checked over every logged query; budget1 permits zero or one query, and the corrected Lamport sketch covers both.

No new primary-source access/comparison is claimed. The incoming auditor's PS10, Goldreich/PSV version/access statements remain that auditor's claims with their recorded limits; this review uses supplied report and frozen Lean/evidence bytes. No Lean/native/build/cache/apps or received programs were run. The proposed comments remain unapplied; final combined post-S2 reconciliation and other gate resolutions are separate.

**Not yet clear to merge — this review supports only the pinned Gate06A closing disposition and its two proposed prose corrections.**
