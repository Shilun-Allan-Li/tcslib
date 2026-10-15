# External audit pack — Chapter 3, phase P3.2 (relativization), round 2 (re-audit of the round-1 repairs)

Campaign: Arora-Barak chapters 3-4 (`AroraBarakChapters3-4Plan.md`), phase
P3.2, round 2. Round 1 (`audits/ch3-p32-findings.md`, attached verbatim)
returned **1 blocker, 0 majors, 2 minors, 2 notes**; per `workflow.md` §3
the gate did not close. This round audits the repairs. The gate closes on
zero blockers and zero majors.

Audited at commit `9a92fa1a` (branch `complexity/arora-barak-ch3-4`). The
complete repair is the attached diff
(`audits/evidence/ch3-p32-r2-repairs.diff`): **one new structure, one new
sorried statement, one new noncomputable definition, one definition
restated** — `Turing.UniformMachineCode`,
`Turing.exists_uniformMachineCode`, `Complexity.expCode`, and `EXPCOM`
redefined over `expCode` — plus the rewritten scheme design bullet, the
corrected uniqueness citations, the updated `EXP ⊆ P^EXPCOM` and
`NP^EXPCOM ⊆ EXP` sketches, and the repaired enumeration sketch. The four
dependent statements (`NPOracle_EXPCOM_subset_EXP` and the three
identities) are **unchanged in shape**, now over the repaired oracle. The
inventory grows from 17 to **18 sorried statements** (OracleAgreement 7,
EXPCOM 6, Relativization 4, NotTimeConstructible 1).

**Layering update since round 1**: the P3.1 gate closed before round 1 ran
(`audits/ch3-p31-resolutions.md`); its clock-convention deviation (round-1
note 4) is retained as declared. `Turing.timed_universal`'s home module
(`Universal.lean`) and the concrete-scheme construction
(`MathlibBridge.lean`, `CodeParser.lean`) are now **attached**, per round-1
note 5's request.

## Brief for the auditor

You have the round-1 report. Your deliverables:

1. **For the blocker**: audit the repair as fresh surface. Blind-restate
   `Turing.UniformMachineCode` — the two simulator clauses decide bounded
   acceptance (`(decode α).toFinTM.ComputesInTime x [true] t`) on
   `⟨⟨bits t, α⟩, x⟩` within `simDegree · (|α| + |x| + t + 1) ^ simDegree`,
   **one polynomial uniform in the code** — and check it against your own
   counterconstructions: your tagged scheme `c_H` admits a canonizer but can
   it admit this simulator? (It cannot while `H ∉ EXP` — verify that the
   interface genuinely excludes both your `EXPCOM[c_H] ∉ EXP` scheme and
   your `P ≠ NP`-relativizing scheme.) Then check the four dependent
   statements over the repaired `EXPCOM`: is `NP^EXPCOM ⊆ EXP`'s ledger now
   payable (the updated sketch charges each query
   `simDegree · (3·p n + 2^(n') + 1) ^ simDegree = 2^{O(p n)}`), and do the
   identities follow? Also audit the **declared choice-over-a-sorried
   existence**: `expCode := Classical.choice exists_uniformMachineCode`
   mirrors `TimeHierarchy.code` structurally, but its existence is sorried
   — the pack declares that `EXPCOM` and its consumers carry `sorryAx`
   through the choice until that fill lands. Is `exists_uniformMachineCode`
   itself true as stated (the chapter-1 concrete scheme with its per-phase
   polynomial ledgers assembled — the sketch names the obligations)?
2. For the **minors**: the enumeration sketch now uses a **three-state**
   well-formed default (or the `toFinOracleTM` embedding) and an explicit
   repetition coordinate in a `ℕ × ℕ × ℕ × ℕ` pairing (finding 2); the
   uniqueness citations now read `pairEncode_injective` twice plus
   `List.length` on the replicated tails (finding 3). Verify both match
   your proposed fixes.
3. Report anything the repairs broke or newly misstate — in particular
   whether the uniform-simulator interface is **stronger than needed**
   anywhere it is consumed, whether `EXP ⊆ P^EXPCOM`'s fixed-code sketch
   survives the scheme change (it now encodes via `expCode`), and whether
   any statement outside the EXPCOM cluster accidentally depends on the
   new scheme — in the round-1 findings-table format and severity scale.

Sources as in round 1 ([AB09] §3.4, Example 3.6(3), Theorem 3.7, Exercise
3.5; [BGS75] at the scanned original, link in the round-1 pack).

## Scope

| Item | Where |
|---|---|
| Under audit | the attached diff: `Diagonalization/EXPCOM.lean` (the new structure, existence statement, `expCode`, the restated `EXPCOM`, the design-bullet and sketch rewrites) and `Diagonalization/Relativization.lean` (the enumeration-sketch repair) |
| Unchanged, re-attached | `TuringMachine/OracleAgreement.lean`, `Diagonalization/NotTimeConstructible.lean` (round 1 passed both; the latter's carry-aware equality sketch was already correct), the `Diagonalization.lean` facade, and the P3.1-closed oracle surface |
| Newly attached context | `TuringMachine/Universal.lean` (`timed_universal` — the per-code contrast), `TuringMachine/MathlibBridge.lean` and `TuringMachine/CodeParser.lean` (the concrete scheme the uniform fill assembles), `ClassNP/EXP.lean` |
| Declared, out of scope | the same commit range contains the concurrent §12/P4.3/P3.3 repairs (disjoint files, own rounds); tactic proofs; round-1 items passed without change |

## Per-finding disposition (verify each)

| # | Round-1 finding | Repair |
|---|---|---|
| 1 | **blocker** — an arbitrary effective scheme bounds no decoding time; permitted schemes put `EXPCOM` outside `EXP` and even separate its relativized `P` from `NP` | `EXPCOM` is redefined over `Complexity.expCode : Turing.UniformMachineCode` — the scheme packaged with a bounded-acceptance simulator at **one polynomial in `\|α\| + \|x\| + t + 1` jointly** (your proposed "scheme together with a proved uniform complexity property", as an interface; the existence is the new sorried statement, its fill the chapter-1 concrete scheme's ledgers assembled). Your tagged schemes satisfy `EffectiveMachineCode` but not the simulator clauses — deciding the embedded `H` in the uniform budget would put it in `EXP`. The hierarchy's `TimeHierarchy.code` is untouched, per your note that fixed-code arguments never needed uniformity |
| 2 | minor — the one-state default is not well-formed; bijective pairing has singleton fibers | The sketch now uses a three-state well-formed default (or the `toFinOracleTM` embedding of a one-state machine, which adjoins the three special states) and an explicit repetition coordinate as the fourth component of the pairing |
| 3 | minor — `pairEncode_replicate_inj` has the unary word on the wrong side | All citation sites now read: `Turing.pairEncode_injective` applied twice, then `List.length` on the equality of the replicated tails |
| 4 | note — fixed-oracle clocks vs [BGS75]'s all-oracle clocks | Retained as the declared P3.1 deviation; no change, per the round-1 disposition |
| 5 | note — `timed_universal` unattached; attestation limits | `Universal.lean`, `MathlibBridge.lean`, and `CodeParser.lean` attached this round; build-artifact claims remain maintainer attestations |

## Repository-side attestations (verify or challenge)

* Fresh elaboration (`audits/logs/ch3-p32-r2-sweep.log`, revision recorded
  at start: `9a92fa1a`): all five modules, facade listed, 0 `error:` lines,
  fresh `.olean`s, exactly **18** `declaration uses 'sorry'` warnings
  (OracleAgreement 7, EXPCOM 6, Relativization 4, NotTimeConstructible 1).
* Style lint (`audits/logs/ch34-r2-repairs-stylelint.log`):
  `Diagonalization` 0 FAIL / 0 WARN over 4 files.
* Statement-freeze baseline: commit `9a92fa1a`.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`; findings verbatim into
`audits/ch3-p32-r2-findings.md`; the gate closes on zero blockers and
majors.
