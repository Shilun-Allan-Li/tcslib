PASS — 0 blockers, 0 majors, 2 minors; 3 notes.

External statement audit of U2, 2026-10-15. Input: `u2-statements-bundle.md`, SHA-256
`9013579aae127306c2406f1505407d932b1ad8be0414531b2241aff7db079e07`.
The hash matches and there are exactly **70 distinct sections**, beginning with
`audits/u2-statements-pack.md`. The claimed repository base is
`fba93e7ecfdf15baa3b58fe275af4da8460966c6`.

No false contract, vacuous effectiveness assumption, or changed received signature was found.
This is a statement verdict, not completion of the four admitted proofs. The two minors concern
the evidence checker and host registration. Human design decisions remain for the maintainer;
the recommendations below do not record those decisions as already approved.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| m1 | minor | `audits/evidence/u2/gate/scripts/check_diag.py` · axiom classification in `main` | The checker does not reject every unexpected axiom. | Its first classification branch accepts any axiom set containing `sorryAx`. I ran it on a matching warning and the print `'Turing.probe' depends on axioms: [propext, sorryAx, UnexpectedAxiom]`, with `sorryAx=Turing.probe`: it returned **exit 0, CHECK: PASS**. The supplied actual raw axiom lists contain only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`, so this is not evidence of an extra axiom in this unit. | Reject every axiom outside the standard set, allowing `sorryAx` additionally only for declarations classified that way; separately require its presence for that class. Add this mixed-axiom negative control. |
| m2 | minor | `machine-library-design.md` §14 · H2 registry row | The registry has not been updated for the new forwarding host. | The supplied H2 row records `roundTM` and H2-L's `loopTM`/`hostedLoopTM`, but contains neither H2-F nor `forwardLoopCfg`/`exists_forwardLoopTM`. The pack and design note describe the new host; the designated registry does not. | At landing, extend H2 with the selected home, both exact names, statement-gate status, time/visited-set contract, and U2-U/U2-E/B6/U-1 consumers; do so before issuing consumer fill briefs. |
| N1 | note | `UniversalK.lean` · `EffectiveCodeK` and both `toK` definitions | This is an effective decoding interface, not an enumeration interface. | It has no encoder, surjectivity, or padding law; a constant decoder is allowed. This does not weaken simulation of the machine a code actually denotes. The hierarchy probe obtains representability separately from `EffectiveMachineCode2.encode` and `decode_encode`. | Keep the interface. Do not infer representability of every machine from an arbitrary `EffectiveCodeK` alone. |
| N2 | note | `SelfUniversal.lean`; `Codes2Tape.lean`; `Universal.lean` · preserved surface | The received signatures are preserved, with the stated promotion exception. | Independent freeze and reconstruction checks pass. The probe's `universal` example has the received signature byte-for-byte after changing only the declaration prefix from `example` to `theorem universal`; the supplied cut log reports successful specialization. | Retain the existing proof of `Turing.universal` until U2-E is filled. No signature repair required. |
| N3 | note | `UniversalK.lean` · duplication ledger | The four new directed screen matches are interface/adapter boilerplate, not copied proofs or machine constructions. | Independent v3 runs reproduce both supplied logs exactly: 37 → 41 pairs, with 4 new and 0 removed. The two structure matches cover the same 89 target characters; the two adapter matches cover 84 characters each. The shared adapter text includes the constructor prefix as well as the argument tail. | Recommend acceptance without a proof-refactoring payback. Record the maintainer's disposition of Q2; do not treat this audit as their acknowledgment. |

**Literal definitions and fidelity.** These restatements follow the declaration bodies and
types. They agree with the accompanying prose, with the enumeration distinction in N1.

| Definition | Mathematical content |
|---|---|
| `EffectiveCodeK k` | Every binary string selects a natural number and a binary `k`-work-tape machine on `Fin (numStates α + 1)`. A bundled finite machine halts on every code and outputs that machine's fixed `serializeK` serialization within the stated length-dependent bound. There is no efficiency requirement on that bound. |
| `EffectiveCodeK.toFinTM` | Bundles exactly the selected machine, its `k` tapes, and its finite nonempty state type; it performs no simulation or conversion. |
| `EffectiveCodeK.ofSerialize` | Composes a supplied decoding with its machine/state-count projections and retains its canonizer and time function. Equality of the supplied serialization with `serializeK` transports the canonizer's specification. |
| `EffectiveMachineCode.toK` | Forgets the one-tape scheme's encoding/padding data while retaining its decoded machine and canonizer, using `oneTapeMachineFormat.serialize_eq`. |
| `EffectiveMachineCode2.toK` | The same operation at two tapes, using the promoted serialization equality. |
| `StepBlock.forwardLoopCfg` | Copies the input position, all source work cells and heads, and the entire output. It appends the canonical table tape and a summary tape with a blank cell at 0 and the unary source state starting at 2; both auxiliary heads are at 0. Control is `some entry` precisely when the source is live, otherwise `none`; the halted state word is empty. |

`ComputesFunInTime` quantifies over **every** code and requires halting, so a nonterminating
canonizer cannot inhabit the interface. An arbitrary total computable decoding is enough for
startup; an encoder is not needed there. Both `toK` views preserve the actual machines
definitionally, as also recorded by the four projection lemmas. The promoted
`Code2TM.serialize_eq_serializeK` states equality of the two serializers; its proposition and
proof body are unchanged.

For fixed `M`, the forwarding encoding retains sufficient information: its control distinguishes
halted from live configurations, and `unaryFin q = true^q.val ++ [false]` distinguishes every
live source state. Thus even state 0 is distinguished from halt. Arbitrary, potentially
unreachable or infinitely supported source tapes are copied without a support assumption;
`StepBlock.Rep` and `roundTM_effect` impose none on those tapes.

The source comparison supports the table-scanning simulation architecture and the distinction
between fixed-tape linear simulation and the later general-machine logarithmic overhead.
The deviations are explicit and acceptable here: constants depend on the **code**, self-application
uses the same paired input on both sides, zero-space cases receive an additive 1, and the eventual
general-machine theorem uses the adopted equivalent-machine code quantifier. Here `k` counts the
**simulated** work tapes; neither universal-machine theorem asserts `U.k = k`.

**The four admitted contracts.** The following are constructive audit arguments, not Lean fills.

1. **H2-F — `exists_forwardLoopTM`.** Apply `roundTM_effect` to the source configuration
   with output replaced by `[]`, keeping the actual output prefix in the representing physical
   configuration; `Rep` deliberately leaves physical output unrestricted.
   The round therefore leaves the physical prefix unchanged and places exactly the current
   optional emission in summary cell 0, because `summaryEmit none a.output = a.output`.
   A finite leaf emits that bit, blanks the cell, moves no head, and either re-enters the round
   or halts; the successor word is already empty on a halting transition, so the result is the
   **exact** prescribed encoding, including output and all tapes.
   The round's positive time, strict interior cut, and visited-set bounds give the claimed
   lockstep and space ledger after summing rounds.
   The existential constant is fixed before the table and input, and cannot conceal
   input-dependent work; positive costs also prevent zero-time simulation of an infinite run.

2. **U2-S — `exists_selfStartupTMK`.** Parse only the self-delimiting code prefix, run its
   total canonizer on a buffered copy, and capture its emissions; these computations depend
   only on the code, not the suffix.
   Parse the fixed serialization, install the table and unary initial state, clean the
   finite scratch region, return all work heads to 0, and rewind the physical input head to 1.
   A fresh exit state gives the first-exit clause, and suppressed administrative emissions
   give silence throughout; the finite startup run supplies a code-dependent space bound.
   At `k = 0`, the table and summary occupy distinct tapes 0 and 1 and every other tape is
   scratch, so the exact configuration remains consistent.
   The cited rewind quantity is an upper bound; neither an exact rewind duration nor a
   computable bound on `canonizerTime` is needed by this existential statement.

3. **U2-U — `exists_selfUniversalK`.** Compose the startup with H2-F, embedding its first
   `k + 2` tapes and leaving the remaining scratch heads stationary.
   For a run known to halt by `t`, use its **first** halting time `h ≤ t`, so the
   live-before-time hypotheses of both the lockstep and visited-set clauses really hold.
   With startup bounds `Tα, Bα` enlarged to include fixed handoff work, and per-round bound
   `D = 50 · (|tableBitsK M.tr| + 1) + C_L`, choose
   `C ≥ max (Tα + D) (Bα + 4D + 2 + 1)`; the calculations below give both conclusions.
   Once halted, the configuration is frozen, so evaluating space at the larger budget
   `C · (t + 1)` does not add visited cells.
   Conversely, a divergent source stays live through arbitrarily large simulated times,
   since every cost is at least 1; the cuts exclude any completed universal output on that run.

   \[
   \begin{aligned}
   T_\alpha+\sum_{u<h}\operatorname{cost}(M.\operatorname{runFrom}(M.\operatorname{initCfg},u))
      &\le T_\alpha+Dh\\
      &\le T_\alpha+Dt\\
      &\le (T_\alpha+D)(t+1)\\
      &\le C(t+1),\\[2pt]
   \operatorname{spaceUsed}(U,C(t+1))
      &\le B_\alpha+s+2(2D+1)\\
      &=s+(B_\alpha+4D+2)\\
      &\le C(s+1).
   \end{aligned}
   \]

   Here the last inequality uses `C ≥ 1` and `C ≥ Bα + 4D + 2`.
   The startup bound already counts scratch heads that remain stationary; the simulation adds
   only source-head visits and the two auxiliary intervals.

4. **U2-E — `universalK`.** The encoded header has length `ℓ = 2|α| + 2 > 0`; parsing and
   canonizing it and installing the ruler require code-dependent work only.
   The ruler host simulates H2-F directly on the suffix, charging at most
   `C_R · (ℓ + 1)` per H2-F step, so the total is bounded by a code-dependent startup cost
   plus `C_R · (ℓ + 1) · D · t`, absorbed into `C · (t + 1)`.
   No scan or copy of the whole suffix is necessary, including when the suffix is empty.
   The ruler host's cut and lower bound on simulated time, together with H2-F's positive
   costs, establish the converse as well as the forward bound.
   Absence of an explicit `0 < C` does not trivialize the claim: a halting source instance
   excludes `C = 0`, while a scheme that always diverges still forces divergence by the converse.

**Adversarial instantiations.** These are semantic checks against the literal contracts;
I did not compile new Lean sanity proofs.

| Instance | Check and result |
|---|---|
| `k = 0`, one state, no work tapes | The source's work-space sum is 0 at every time. U2-U allows the fixed startup and auxiliary space through `C · (0 + 1) = C`. H2-F's mirrored-head clause is empty, but its two auxiliary-head clauses remain substantive. U2-S's tapes 0 and 1 are valid and distinct. |
| Constant decoder | Choose the same finite machine for every code and a finite output-chain canonizer for its fixed serialization. For a machine that halts and emits `false`, both forward simulation clauses have actual instances; for a constantly diverging machine, the converses prohibit false halting. The interface is inhabited without surjectivity, intentionally. |
| Immediate halt, `t = 1` | Use one state whose transition has successor `none`, stationary heads, and emission `some false`. The round's temporary summary becomes `some false`; the forwarding leaf emits `[false]`, erases the summary, and halts with an empty state word. U2-U/U2-E have budget `2C`, sufficient to include startup. The same check with `none` and `some true` distinguishes all three summary cases. |
| Unreachable configuration and nonempty output | Start with arbitrary work cells/heads and output `[true, false]`. Only the summary for the current emission is reset; the physical prefix survives, and the halting example above ends with `[true, false, false]`. No initial-configuration hypothesis has been smuggled into H2-F. |
| Already halted source; zero rounds | `forwardLoopCfg` is halted with the source output unchanged. The summed cost is 0; the visited sets contain just their initial heads, satisfying the mirror and auxiliary bounds. A live self-loop cannot exploit this case because its costs must be positive. |

Useful permanent sanity lemmas are: the encoding's halt equivalence and output projection;
its injectivity for a fixed machine; its `Rep` relation to the source with erased output;
the startup-to-forwarding configuration equality after restriction/relabelling; and concrete
zero-tape, constant-decoder, and three-way immediate-emission instances. The existing `k = 0`
probe examples establish type compatibility only, not these behavioral checks.

**Signature and duplication verification.** I reran the supplied freeze on the recovered base
and proposed files: 10 received declarations in `StepBlockLoop`, 15 in `Codes2Tape`, 2 in
`SelfUniversal`, and none in the facade. The promotion is the sole visibility/name exception;
its proof is identical and `twoTapeMachineFormat` merely changes its reference. The five proposed
files also reproduce byte-for-byte from the 17 asserted edits and the new module. At `k = 1`,
the startup's tape indices become 1 and 2; U2-U yields B6's space theorem by taking
`t' = C · (t + 1)` and weakening its source-space bound. Both received signatures remain exact.

The v3 screen has 260 → 267 screened declarations and 12,126 → 12,472 pair-counted matching
characters. Cumulative totals by target file are:

| Target file | Before | After |
|---|---:|---:|
| `Build/StepBlockLoop.lean` | 0 | 0 |
| `Build/StepBlock.lean` | 5,364 | 5,364 |
| `SelfUniversal.lean` | 0 | 0 |
| `Codes2Tape.lean` | 429 | 429 |
| `Encoding.lean` | 1,126 | 1,126 |
| `UniversalStartup.lean` | 2,796 | 2,796 |
| `Build/InputDevice.lean` | 0 | 0 |
| `CodeSimulator.lean` | 2,411 | 2,411 |
| `UniversalK.lean` | absent | 346 |

These are directed screen charges, not distinct copied-character counts. The new file's distinct
matched target positions total `89 + 84 + 84 = 257` characters: about 7.48% of its 3,437
non-whitespace, comment-stripped code characters. This supplemental metric does not replace the
campaign's copied-material review. Inspection finds no new copied proof or host construction;
the substantive relabelling proof remains probe-only and is addressed by Q4. Thus the template's
major-debt rule for wholesale copied proved material is not triggered by these field and
constructor-application matches. Existing matches are unchanged, not newly approved by this audit.

**Rulings on the five questions.**

| Question | Ruling |
|---|---|
| Q1 — H2-F's home | **Prefer `Build/StepBlockForward.lean`.** H2-L and H2-F are distinct loop contracts, and the estimated H2-F fill would take the current 595-line combined file well beyond the policy's preferred size. The sibling also avoids the extra `CodeSimulator` replay during B5a work. This is an organizational recommendation, not a mathematical defect in the submitted home. If the maintainer keeps `StepBlockLoop`, serialize the merge with B5a and address size when filling. |
| Q2 — disclosed matches | **Recommend acceptance as interface/adapter boilerplate, with no payback**, for the reasons and exact counts above. Preserve the frozen received scheme structures. Record the human disposition; an auditor recommendation is not that disposition. |
| Q3 — field `machine` | **Keep it.** Its value is a transition machine, whereas the received `decode` fields return bundled code objects. |
| Q4 — `exists_code2TM` | **Use a `k`-generic finite-state relabelling lemma**, with the one- and two-tape results as corollaries, after the coordinated MIG-1 S window. Preserve both per-run time and the existing one-tape space equality. Keep the shared lower-level lemma independent of `CodeTM`/`Code2TM` to avoid an import cycle; do not land the probe's mirrored proof as another permanent copy. |
| Q5 — U2-E fill timing | **After the ruler-host fill.** Gating its statement now is sound. The self-application hierarchy route can proceed independently, and U-1's proof replacement should wait for a filled U2-E. |

H2-F is the right public host boundary: its control varies with `k` alone, while tables,
state counts, inputs, starting configurations, and emitted outputs remain general. It supplies
exact configurations, positive bounded macro-step times, cuts, and visited-set clauses for all
named consumers. U2-E can wrap it with the public ruler host without changing the native-input
round contract. No additional consumer-specific private interpreter is required by this design.

**Evidence checked and limits.**

- Verified the outer SHA-256, all 70 unique section names, and **49 available internal hash
  comparisons**: four base files, 44 gate files, and the pack. Preserved the pack's two final
  newlines when checking its internal hash. `BUNDLE-FILES.txt` is listed in the internal manifest
  but is not an attached section; the section inventory itself was independently enumerated.
- Independently reran reconstruction, freeze, widths/hygiene, and both full-population v3 copy
  screens; checked the v3 script's advertised hash. Read the definitions, four contract types,
  their sketches, `Rep`, `roundTM_effect`, `roundTM_visited`, `Lockstep`, the ruler-host contract,
  the received universal statement, and the consumer interfaces. No tactic-correctness review.
- Read the supplied precheck, graph, elaboration, axiom, lint, and negative-control records and
  relevant scripts. The reported nine elaborations, seven negative controls, 724-blob base
  precheck, full-tree name search, and ten-module replay closure remain **supplied evidence**;
  this bundle does not contain their complete repository/snapshot environment. Independently
  enumerated the axiom names appearing in the raw axiom log and exercised m1's counterexample.
- Lean could not be run: `/root/.elan/bin/lean --version` returned
  `error: failed to locate application`. I did not run a fresh Lean build or claim kernel
  verification. The four contracts remain admitted, and the B6 corollaries inherit `sorryAx`
  through them. The probe's hierarchy conclusions remain conditional on `G5Interface` and U2-U.
- Source comparison used indexed original-author draft text: [Theorem 1.9 and its table-scanning
  proof](https://www.cs.princeton.edu/courses/archive/fall07/cos433/modelchap), and the
  [space-universal exercise in the Arora–Barak draft](https://users.cs.duke.edu/~reif/courses/complectures/books/AB/spacechap.pdf).
  Full-page retrieval returned HTTP 403. The latter draft numbers the exercise differently;
  I therefore do not claim independent verification of the published 2009 exercise numbering
  or every surrounding textbook convention. The formal contract analysis rests on the supplied
  Lean definitions and explicitly stated campaign deviations.

**Notation used in the audit calculations.** `M` is the machine decoded from `α`; `t` is the
given source time budget; `h` its first halting time; `s` its work cells visited by time `t`;
`Tα, Bα` are startup time/space bounds; `C_L` is H2-F's fixed additive constant; `D` is its
per-round upper bound; `C` is the chosen overall simulation constant; `ℓ` is the encoded header
length; `C_R` is the ruler-host constant. Input and initial configuration arguments abbreviated
in the displayed calculation are the same `pairEncode α w` throughout.
