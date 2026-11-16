# Canonical fake message and fixed uniform Bob simulator

## Result and consumer API

FakeMessage.lean adds only FakeObjects.message and its exact message_eq reader. The
formula is the actual encoded table/key0/decoding-pair expression already proved efficient
by FakeProgram.message_poly. It is the shared semantic endpoint for c's gate hybrids.
The separately frozen early API snapshot was sent to the lead and c with source/olean hashes.

FakeSimulator.Data contains polynomial bound/input/output counts, polynomial-time E1/E2 and
unary generator, a circuit/output family with canonical generator shape, input/output bounds,
fan-in, and a seed family depending only on n and raw tape. Its key/nonce/XOR equations hold
on every raw tape. There is no fakeMessage or activeAnswers PTC assumption.

The raw parameter is the length of NUPPT.inParam. The generator is always called on the
normalized unary parameter, so its canonical shape holds even for malformed raw fields.
Result bits come from snd(inArg), and seed coins from inCoins. Count and bound efficiency
are derived from public unary polynomial evaluation. message_poly and answers_poly apply
the complete actual FakeProgram contracts to these selectors and supplied seed readers.

simulator d coins specializes the existing BobSimulator to those derived leaves. The same
machine, data and coin polynomial are fixed before every input and distinguisher.
simulator_uniform, simulator_coins, simulator_runAtL, simulator_runAt and idealB_eq expose
uniformity, exact coin budget and exact actual simulated views; the ideal endpoint retains
Alice's true functionality output. No Bob simulator implementation was re-derived.

messageAt/answersAt package Nat-indexed dependent circuit/seed data before canonical layout
normalization, avoiding dependent transport. Data.make has generated non-simp projection
readers and direct make_messageAt/make_answersAt word readers. The latter expose all dependent
fields together. Four downstream consumer probes, with the entire imported TCSlib closure
sealed, prove the public constructor word reader usable in all A/B by strict/coe variants.
messageAt_ofFn exposes a genuine prescribed-output vector without padded bit reads.

For coin transport consumers can use the existing NUPPT.coinsEquivPoly with simulator_coins,
and its public coinsEquivPoly_ofFn reader. No new coin-equivalence construction is needed.

## Reuse and scope

Existing FakeProgram, BobSimulator, NUPPT layout/run readers, public unary polynomial
computation and encoded list lookup are consumed. No real Yao definition or probability
proof was copied. No frozen or lead-owned source was edited. BobSimulator source and olean
were seeded by the lead; its public contracts are the only machine interface used.
New helper imports are within the approved helper tree and existing dependency closure.
The generated structure projection readers carry isSimp=false; no simp attribute was added.

## Verification and retained iterations

FakeMessage01 and FakeSimulator13 are final normal PASS, zero errors and warnings.
All eight new whole-file seal variants PASS with maxErrors=0, full imported TCSlib closure,
and both diagnostic forms counted. Four positive controls PASS and four deliberate negative
controls each have exactly one error. Four public-constructor consumer seals also PASS.
The complete fourteen-owned-module trace covers 283 stored constants, including generated
and private declarations: no transitive sorry closure; only propext, Classical.choice and
Quot.sound. Final style lint reports zero findings.

Raw source/log versions for every failed iteration remain. Initial grouped structure field
syntax was split into separate fields. The first idealB specialization tried rewriting the
machine under its dependent Coins argument; direct specialization of BobSimulator.idealB_eq
fixed it. No timeout or resource failure was used.

The final style pass required only documentation additions and joining a multiline attribute
for the linter; every declaration token is identical to the sealed version, mechanically
recorded in documentation-only-comparison.json. The exact final documented source then
passed ordinary FakeSimulator13, producing the matching final olean.

## Next assigned obligation

The lead separately assigned CoordinateSwap after this handoff. Read-only reuse search found
acceptProb_comp_equiv, acceptProb_fst and acceptProb_update; no partial-family coordinate-swap
law. b owns the concrete SelectedSeed.fill, pick/place and cryptographic sampler identities.
This handoff contains no CoordinateSwap code.
