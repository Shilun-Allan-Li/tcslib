# U2 statement gate: resolutions (round 1; gate CLOSED)

**Gate:** the `k`-generic universal machine (`TuringMachine/UniversalK.lean`: the scheme interface
`EffectiveCodeK`, U2-S, U2-U, U2-E), the forwarding round-loop host H2-F
(`StepBlock.forwardLoopCfg`, `StepBlock.exists_forwardLoopTM`), B6's two statements re-proved
in place as the `k = 1` corollaries, and one promotion (`Code2TM.serialize_eq_serializeK`)
(`audits/u2-statements-pack.md`; bundle SHA-256
`9013579aae127306c2406f1505407d932b1ad8be0414531b2241aff7db079e07`, 70 sections, dispatch folder
26; evidence `audits/evidence/u2/gate/`, inputs `ba0b6c0b`).

**Round 1** (`audits/u2-statements-findings.md`, verbatim): **PASS, 0 blockers, 0 majors, 2 minors,
3 notes. The gate closes.**
- **No false contract,** no vacuous effectiveness assumption, no changed received signature.
- **Each sorried contract is argued true as stated** by a constructive outline: H2-F's exact
  lockstep from `roundTM_effect`, U2-S's startup, U2-U's constant choice
  `C ≥ max (Tα + D) (Bα + 4D + 2 + 1)`, and U2-E's suffix-free bound through the ruler host.
- **The adversarial instances hold:** `k = 0`, a constant decoder, an immediate halt at `t = 1`,
  an unreachable configuration with nonempty output, and an already halted source.
- **H2-F is the right public host boundary.**
- **Independent re-runs agree:** the freeze, the reconstruction from the 17 asserted edits, and
  both v3 screens.

The auditor could not run Lean. The elaborations, negative controls, name search and replay
closure remain supplied evidence. The landing's fresh run and replay remain landing obligations.

## Findings

| # | Severity | Finding | Resolution |
|---|---|---|---|
| m1 | minor | `check_diag.py` accepts any axiom set containing `sorryAx`, so `[propext, sorryAx, UnexpectedAxiom]` passes; the real logs show only the standard three and `sorryAx` | **Fixed for the landing.** A declaration classified sorried may print the standard axioms plus `sorryAx`, and must print `sorryAx`. Every other declaration may print only the standard axioms. Any other axiom fails. The auditor's mixed-axiom print becomes a negative control that must fail. |
| m2 | minor | The §14 registry's H2 row lists neither H2-F nor its names | **At landing, before any consumer brief:** H2's row in `machine-library-design.md` §14 gains H2-F with its home (`Build/StepBlockForward.lean`, below), both names, gate status, its time and visited-set contract, and its consumers U2-U, U2-E, B6's `U₀` and U-1. |
| N1 | note | `EffectiveCodeK` is a decoding interface, not an enumeration: no encoder, surjectivity or padding law | Kept as is. Representability comes separately, from `EffectiveMachineCode2.encode`/`decode_encode`, as in the probe. |
| N2 | note | Received signatures preserved; the probe's `universal` example matches the received signature | `Turing.universal` keeps its proof until U2-E is filled (U-1). |
| N3 | note | The 4 new screen matches are interface and adapter boilerplate (257 distinct characters) | Accepted by the user (Q2 below). |

## The user's decisions on the pack's questions (2026-10-15)

1. **Q1, H2-F's home: a new `Build/StepBlockForward.lean`,** following the auditor's preference.
   It imports `Build/StepBlock` and `Build/Contract/Basic` and holds `forwardLoopCfg` and
   `exists_forwardLoopTM`. `UniversalK` imports it in place of `Build/StepBlockLoop`, which is not
   edited.
   - **Why:** `CodeSimulator` imports `StepBlockLoop`, and the B5a canonizer continuation 4 owns
     `CodeSimulator`. A sibling keeps `CodeSimulator` out of U2's replay and out of that fill's
     way.
   - **The auditor's other reason is discounted:** file size is not a driver (standing rule).
   - The landing is rebuilt and re-checked for the new home. The statements are unchanged, so no
     new gate round is needed.
2. **Q2: the four disclosed pairs are acknowledged as accepted interface and adapter boilerplate,
   with no payback.** Two are `EffectiveCodeK`'s fields mirroring the received schemes (89
   characters, 70%); two are the `toK` adapters' shared constructor application (84 characters,
   about 54%).
3. **Q3:** the field name `machine` is kept (pack and auditor agree).
4. **Q4:** `exists_code2TM` goes through a `k`-generic finite-state relabelling lemma in
   `StateRenaming`, with the one- and two-tape results as corollaries. It is independent of
   `CodeTM`/`Code2TM`, preserves per-run time and the one-tape space equality, and comes now that
   MIG-1 stage S has landed (#98). The probe's mirrored proof does not land.
5. **Q5:** U2-E's fill waits for the ruler-host fill. U-1 waits for a filled U2-E.

## Suggestions recorded for the fills (not gate conditions)

Sanity lemmas the auditor proposes:
- the encoding's halt equivalence and output projection;
- its injectivity for a fixed machine;
- its `Rep` relation to the source with erased output;
- the startup-to-forwarding configuration equality after restriction and relabelling;
- concrete zero-tape, constant-decoder and three-way immediate-emission instances.

The existing `k = 0` probe examples establish type compatibility only.

## Landing

One PR:
- the new `Build/StepBlockForward.lean`;
- `UniversalK.lean`;
- `SelfUniversal.lean`, with B6's corollaries;
- the `Codes2Tape.lean` promotion;
- the facade entries.

It is rebuilt for Q1 and re-checked fresh at the landing tip with m1's stricter checker, and the
registry row of m2 goes in with it. Its replay no longer includes `CodeSimulator`.
