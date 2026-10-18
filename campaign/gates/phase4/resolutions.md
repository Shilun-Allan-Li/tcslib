# Phase 4 — audit loop resolutions (CLOSED)

Protocol: `AroraBarakChapter1Plan.md` §5 "Audit protocol". External auditor:
cross-vendor LLM per decision log.

## Round 1 (`phase4-pack.md` → `phase4-findings.md`, audited at `49d25a27`)

**Zero blockers, zero majors — the first phase to clear its audit loop in a single
round.** All 18 new declarations were blind-restated in agreement with their
statements; both headline assembly arguments — the `UC` diagonalization over an
arbitrary `MachineCode` and the `HALT → UC` reduction — were independently
re-derived end-to-end from the stated interfaces, confirming the skeleton's design
goal that the fill is assembly, not new mathematics ("no missing
machine-construction interface"). The repository attestations were corroborated
source-side (sole-parent commit relation, matching blob hashes for all six touched
modules, insertion-only comment-stripped diffs, unchanged carried sorries, and the
`14 + 7 = 21` sorry count). One minor and seven notes, resolved in the closing
commit:

| Finding | Resolution |
|---|---|
| 1 minor — the diagonal-pairing sketch's `3n + 6` step count undercounts the doubled first pass (one emitted symbol per transition forces `2n` steps); the described schedule takes `4n + 5` | Sketch corrected to the auditor's explicit schedule (`2n + 2 + (n+2) + n + 1 = 4n + 5 ≤ 6(n+1)`); the theorem's existential linear bound is unchanged |
| 2 note — the arbitrary-`MachineCode` generality of Theorem 1.10 survives the noncomputable-meaning attack; no runtime encode/decode occurs | No change; no effectivity hypothesis is to be added. The auditor's full derivation is on file for the fill |
| 3 note — `exists_comp_partial`'s iff is the right contract; the construction must make the buffer rewind's first left move unconditional (the head rests on the blank right of the written word) and initialize the boundary tag for an empty buffer | Both details added to the sketch |
| 4 note — `exists_cond`'s register/rewind construction verified (head calculation `j ↦ max(j−1,0) ↦ 0 ↦ 1` from every valid position; append-only singleton output forces exactly one emission, so early emission is harmless) | No change |
| 5 note — the bare `∃ T` of `Computes.exists_computesFunInTime` suffices (`one_work_tape_binary` imposes no regularity on the bound; empty alphabets vacuous) | No change |
| 6 note — `HALT`'s off-image totalization is correct and immaterial to Theorem 1.11, but convention-dependent elsewhere (`HALT c [] = false`) | Docstring now warns downstream clients: keep the convention or prove inputs are genuine pairs. **Carried obligation** |
| 7 note — the reduction assembles entirely from stated declarations; the forward universal clause suffices, no timed partial composition and no globally named evaluator needed | No change; the auditor's assembly derivation is on file for the fill |
| 8 note — the zero-error elaboration attestation was not independently reproduced (no Lean in the audit environment); source-history checks corroborate the additive-change and sorry-count attestations only | Standing practice: repository-side verification continues; fill rounds must ship elaboration evidence from the pinned toolchain, and neither this audit nor a sorry-accepting elaboration is completed correctness |

## Gate status

**CLOSED.** With phases 1-4 all gated, **Chapter 1's critical path is fully
specified and audited**: every headline definition and theorem of [AB09, §§1.2-1.6]
is stated, with 21 audited-true sorries. Carried obligations, tracked in the plan:

- **Fill campaign** (the remaining critical-path work): 21 sorries, each with an
  audited sketch. Beyond the earlier construction manuals, the phase-4 findings add
  the explicit diagonal-pairing schedule (`4n + 5`), the completed-output ↔
  halted-state equivalence proof (with its space witness), the rewind head
  calculations, and complete assembly derivations of both phase-4 theorems.
- Downstream uses of `HALT` on arbitrary (non-pair) strings must keep the off-image
  `false` convention or prove their inputs are genuine pairs (finding 6).
- Fill rounds ship build/elaboration evidence from the pinned toolchain
  (finding 8).
- Phase 5 remains deferred to a much later effort (plan §5); no pack will be
  prepared for it in the current push.
