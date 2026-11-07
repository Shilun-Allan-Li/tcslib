# Retained tagged forwarding driver

The retained `Turing.FinTM.fwdMapVirtual_run` is a third member of the specific unrestricted,
one-source-step/one-host-step **existential valid-tag propagation** driver. The first two are
`bufferedSecondCfg_run` and `vhostEmitTM_runFrom`, now repointed to existing Mathlib invariants.
The forwarding member still contains the same induction: choose the initial valid tag; obtain a
new valid tag from its one-step theorem; carry that tag's validity and the host/source run equality
to the next time. This is more mathematical structure than the ledger's scalar induction tiles.
A mechanical existing-invariant repoint is appropriate before claiming this specific driver family
retired. No new API, import, controller, admission or public statement is needed.

## Exact retained contract and route

Primitives lines 3296–3311 retain the private frozen statement
`∃ tag', VirtualTag (M.tm.runFrom c t).inputPos tag' ∧ host.runFrom encodedStart t = encodedEnd tag'`.
The encoded configuration additionally preserves the physical input head, first component buffer,
and emitted prefix. Its same-home `fwdMapVirtual_step` supplies the corresponding one-step witness
for an arbitrary source configuration and valid tag, including halting and the stationary halted
tail. No liveness premise or source/host time stretch occurs.

Let `P n` be precisely that existing conclusion at time `n`. `runFrom_zero` proves `P 0` with
`tag` and `hb`. Given `P n`, `fwdMapVirtual_step` and the two `runFrom_succ_eq_step'` equations prove
`P (n+1)`. Thus the already-used `Set.MapsTo.iterate` route on `n ↦ n+1`, normalized by
`add_right_iterate`, has the exact premises required for this third consumer. This paragraph is a
source-level route assessment; no new probe or source implementation was run in this review.
The newly authorized isolated prototype belongs in its separate review folder.

## Bounded all-TCSlib candidate enumeration

`tagged-run-candidates.json` preserves the complete source blocks/headers of **16 candidates**
found by an identifier-bounded scan of all current TCSlib: all **22** files containing `VirtualTag`
in code, then theorem/lemma headers containing `VirtualTag`, `runFrom`, and an existential.
An additional body scan for `VirtualTag` + `runFrom` + induction found one further declaration;
its inductions are `Fin.lastCases`/`Fin.addCases` field calculations, and its hosted run already
uses `vhostSilentTM_runFrom`. This is a complete execution of those lexical candidate filters,
followed by contract inspection; it is not an assertion of exhaustive semantic closure through
arbitrary aliases or hidden relations.

| Candidates | Contract inspection |
| --- | --- |
| `bufferedSecondCfg_run`, `vhostEmitTM_runFrom`, `fwdMapVirtual_run` | The three core unrestricted deterministic, equal-time drivers. The first two already use the Mathlib invariant route; the third is the retained member requiring the mechanical repoint. |
| `vhostSilentTM_runFrom`, `emCall_eval_run` | Run-trajectory wrappers already consuming canonical run APIs. Silent hosting uses `vhostEmitTM_runFrom` and `embedSilentTM_runFrom`; evaluation uses `bufferedSecondCfg_run` plus `capture_run` and explicit pre-halt liveness. Neither repeats the tag-propagation induction. |
| `emCall_eval_first`, `b2b_vhost_rewind`, `hostedLoopTM_run`, `certCore_run` | Consumers packaging a selected first/halting endpoint, rewind bound, hosted macro loop, or deadline. Their existential time and additional guards/frames differ from an unrestricted equal-time trajectory. |
| `choiceCore_run`, `b2_verify_run` (Nondeterminism) | Broader tagged inductive drivers remain outside the exact three-member contract: the first consumes a bounded nondeterministic choice prefix, proves `runWith (u.take (t+1))` using append/getElem, and advances a choice index; the second inducts over a choice word under all-prefix liveness and uses `NDTM.runWith_cons`. They are not direct instances of the unrestricted deterministic source/host `runFrom` contract. No abstraction impossibility, debt waiver, repair or colleague-code permission is inferred for these richer variants. |
| `clTrack_round`, `clRec_advance`, `clRec_prefix` (Hardness) | Variable-cost macro simulation: existential host times, width-dependent bounds, records and counter updates. The prefix proof composes copy/tick/advance blocks and sums their times; it is not a one-host-step per source-step driver. |
| `Meyer.loop_run`, `Meyer.walk_run` | Strong induction over a counter value with variable sweep/borrow/return time and changing counter contents. The walk theorem returns an answer after iterated `wstep`; these contracts are distinct from equal-time tag propagation. Colleague-owned sources were read only. |
| Additional body candidate `NTimeDiag.dz_clock_exists` | The found inductions are finite-index constructor field calculations; its local hosted trajectory is obtained by calling `vhostSilentTM_runFrom`. No extra tagged run induction was found in that candidate. |

Within the **current twelve changed files**, the other relevant tagged trajectory wrappers therefore
already reuse the canonical driver. Outside them, the two Nondeterminism proofs remain explicit
broader variants and must not be silently included in a global retirement claim. This review makes
no global tagged-family or duplication clearance claim.

## Ledger boundary

The ledger's lines 363–375 explicitly exclude one `rewindTM_run_ofCfg → a2_mapSetup_run` hit:
84 characters in two scalar run-by-induction tiles, with no shared setup argument. It lists the
other short scalar/frame idiom matches. That narrow exclusion does **not** describe the existential
fresh tag, `VirtualTag` validity, and encoding-equality propagation in `fwdMapVirtual_run`.
`fwdMapSetup_run` is the moved scalar setup member; it is distinct and remains outside this repair.

The historical Catalog row at line 41 names `a2_mapVirtual_run` as an adaptation member. That
records its old membership/provenance, not a blanket exemption for this tagged driver after the
move to its canonical home. The route uses existing published Mathlib machinery and existing
same-home step equations, so the requested repoint is mechanical reuse under the standing rules.
Any claim about richer nondeterministic or variable-cost families needs its own bounded analysis;
none is authorized or settled by the scalar exclusion or this source freeze.
