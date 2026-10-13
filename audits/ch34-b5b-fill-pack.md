# External audit pack — B5b fill gate: the `EXPCOM` summit, `NP^EXPCOM ⊆ EXP` (1 target)

Campaign: Arora-Barak chapters 3-4 (`AroraBarakChapters3-4Plan.md` §4e, cluster B5).
`Diagonalization/EXPCOM.lean` formalizes [AB09, Example 3.6(3)]: the oracle language `EXPCOM`
over a uniformly-timed machine-code scheme, and the identities `P^EXPCOM = NP^EXPCOM = EXP` that
feed Baker–Gill–Solovay. Its statements were gated at **P3.2**, which closed at round 2
(`audits/ch3-p32-findings.md`, `audits/ch3-p32-r2-findings.md`, resolutions
`audits/ch3-p32-resolutions.md`; round 1 repaired `EXPCOM` to range over a uniformly-timed scheme).
The summit's route was later rebound to design §12.10's compositional route (decision 1, wave-1
statements note 42), and the wave-1 statement probe `S1210StatementsProbe` transcribes it.
**This gate covers B5b, the summit:**

| File | Target | Statement |
|---|---|---|
| `Diagonalization/EXPCOM.lean` | `Complexity.NPOracle_EXPCOM_subset_EXP` | `NPOracle EXPCOM ⊆ EXP` |

**It is proved modulo exactly the two §12.11 rows of B5a**: `MachineFormat.exists_polyCanonizer`
and `MachineFormat.exists_uniformSimulator`, both in flight. The brief authorized a third
admission, W2-S, which landed in the same integration and is gated separately
(`audits/wave1-fill-pack.md`). The rest of the file (the scheme instance, `EXP ⊆ P^EXPCOM`, the
three identities) was filled by B5a modulo the same two rows and goes to B5a's gate.

One delivery, integrated by `git am -3` with Codex authorship:

| Delivery | Brief | Agent commit (base) | Integrated | Result |
|---|---|---|---|---|
| B5b | `briefs/ch34-b5b.md` | `7a2ed9ed` (`ebc58d67`) | `2df46a3e`, PR #66 (fills-6) | **1/1, modulo the two §12.11 rows** |

Two maintainer commits follow, both comment-only:
- `4a5b646b`: the module header no longer says the summit is sorried, and a note on the
  summit's appendix says W2-S has landed;
- `36503704`: proof sketches for `expcom_summit_budget` and `expcom_all_true`, which the review
  found without one.

Then the **CH34-D4 factoring** (`6c7e35bd`, `audits/ch34-d4-record.md`; user ruling: "factor before
closing"). It promotes the `Nat.bits` shift law to `TuringMachine/Encoding`, and the `incFixed`
overflow criterion and prefix law to `Build/Convention`. In `EXPCOM` it deletes
`expcom_bits_two_pow` and `expcom_inc_prefix`, and re-derives `expcom_all_true` (statement
unchanged) from the public criterion. It also retires ConfigGraph's `s1b_radius_bits` and
re-derives Catalog's `catalog_increment_value`. **This factoring is part of this gate's audit
object.**

**Every proof is kernel-checked**; the replay and axiom evidence is below. Fill gates close on
zero blockers and zero majors (`workflow.md` §4), and the duplication rule (`audits/TEMPLATE.md`,
failure mode 5) is in force. The human-review item **CH34-D4** (`backlog.md` §1) is ruled: factor
before closing, done by the factoring above. The standards are attached.

**Bundle:** `audits/ch34-b5b-fill-bundle.md`: this pack, the standards, the statement-gate records, the briefs, the
reports, the integration records, the owned files with their bases, the patches, the freeze,
replay, axiom, screen and lint logs, and every screen-population file, so that the screen can
be rerun.

## What changed (verify)

| Class | Declarations |
|---|---|
| **Target body, `sorry` → proof** | `NPOracle_EXPCOM_subset_EXP` |
| **Other publics** | unchanged |
| **Privates added** | 17 by the delivery, 15 after the factoring (two deleted), listed with their roles in the report, among them the dispatcher `expcom_decider` (the probe's statement, verbatim but private and renamed, so the S1210 probe still declares `exists_EXPCOM_decider` locally) |
| **Imports** | the two sanctioned additions (brief rule 1(a)): `Build/CertShell` and `ClassNP/ExpPoly` |
| **Docstrings** | the summit's flagged fill appendix (the §12.10 compositional route); the maintainer's header and appendix notes; two maintainer sketches |
| **Elsewhere (the factoring)** | four new publics in `Encoding` and `Convention`; ConfigGraph's `s1b_radius_bits` deleted; Catalog's `catalog_increment_value` re-derived; no statement or import changed |
| **Size** | 382 → 744 lines (772 before the factoring) |

## Brief for the auditor

1. **Freeze.** Re-establish it from the attached base (at `ebc58d67`), the head and the patch
   (`audits/evidence/ch34-b5b-fill-gate/`): the summit's statement and every other declaration
   unchanged; only the summit's body and appendix, the new privates, the two imports and the
   maintainer's comment-only edits changed.
2. **The dispatcher** (brief route A): parse `z`; the validity bit `ok z` (pair validity twice
   and the all-`true` tail through `incFixed`'s overflow); the rebuilt input
   `simIn z = ⟨⟨bits (2^n), α⟩, x⟩`; the front end `if ok z then simIn z else w₀`, with
   `w₀ = ⟨⟨[], []⟩, []⟩` answering `[false]` at deadline `0`. Check that the simulator is
   **only** run on `simIn` of a genuine triple or on `w₀`: the `UniformMachineCode` contract makes
   no promise on malformed inputs (P3.2 round 2). Check the composition `exists_comp_on_image`,
   with `T₂` measured at the original length, and the budget's absorption into `A·2^(B(m+1))`.
3. **The summit's route** (design §12.10, decision 1): enumerate certificates around the W2-V
   shell (`FinTM.exists_certificateShell`, through `exists_proj_decider`); handle the
   nondeterministic choices by the W2-C choice-word machine (`FinOracleNDTM.exists_choiceTM`); and
   simulate the oracle machine by W2-S's trace (`FinOracleTM.exists_plain_simulation_of_monotone`)
   from the preloaded choice word, with the dispatcher as the oracle's decider. The `ExpPoly`
   ledger absorbs the simulator, shell and projection-enumerator budgets. Confirm that the
   ledger lemmas are faithful transcriptions of the probe's (as the brief requires), and that the
   summit is not weaker than stated.
4. **Duplication** (failure mode 5).
   - The delivery's screens (`audits/logs/ch34-b5b-1-screen-{before,after}.txt`, its 22-file
     population): 871 / 522 → 887 / 524. The two new pairs are one cross-file pair,
     `expcom_bits_two_pow` against Separation's private `bits_two_pow` (94% / 84%), which the
     brief pre-disclosed as forced.
   - The fills-6 chapter-3/4 union screen (66 files at the integration head) adds one pair:
     `expcom_front_poly` reproduces half of `SAT.sat_pipeline_poly` (255 of 505 characters). Both
     compose the polynomial-time closure rows, and the shared text is their citation names.
   - **Pre-disclosed forced restatements:** the `Nat.bits` fact above; the all-`true` overflow
     direction of `incFixed` (`expcom_all_true`; public as `MeyerTableau.incFixed_eq_none_iff`,
     which `EXPCOM` cannot import, and sharing no text with it); the padding parse's triple
     uniqueness (194 characters shared with the frozen reduction).
   - **Undisclosed, found by the review:** `expcom_inc_prefix` restates Catalog's private
     `catalog_increment_value`.
   - **The cumulative ledger.** The delivery's conservative count is 4,930 of 13,500 extracted body
     characters copied, **36.52%** (`audits/evidence/ch34-b5b-fill-gate/copy-coverage.txt`). The
     numerator takes whole bodies: the probe transcriptions, the forced restatements, and
     CH34-D3's 322-character mirror. This is above one fifth, in a file that took copies in an
     earlier epoch, so `workflow.md` §4 opened the human-review item **CH34-D4**. Its question:
     acknowledge the ledger, or schedule the factorings it lists (a public `Nat.bits` shift
     law, the `incFixed` criterion in `Build/Convention`, `catalog_increment_value` made public and
     cited, a shared triple-uniqueness lemma). **Verify the ledger's numbers and classification**,
     and say whether any item is worse than the record says.
5. **The detecting control** (P3.2 / wave-1 round-2 note 17). The S1210 probe's census must still
   detect an admission once the summit lands. It now detects the probe-local
   `exists_EXPCOM_decider` and the two §12.11 rows (`audits/logs/b5a-fill-cont3-preship.log`).
6. **Documentation.** Check the summit's appendix, the maintainer's header and appendix notes,
   the two maintainer sketches, and every new private's docstring against the delivered proofs.
7. **The CH34-D4 factoring** (`audits/evidence/ch34-d4/ch34-d4.patch`, `audits/ch34-d4-record.md`).
   - Check the four new public lemmas: statements, proofs, docstrings and homes.
   - Check that each retired copy is gone, or that its wrapper is now a derivation with an
     unchanged statement, and that no statement or import changed.
   - Check that the colleague-owned `Separation` and `CircuitComplexity` files are untouched.
   - The screen (`audits/logs/ch34-d4-screen-{before,after}.txt`) loses the
     `expcom_bits_two_pow`/`bits_two_pow` pair. It gains one **disclosed** pair:
     `Convention.incFixed_eq_none_iff_replicate` against `MeyerTableau`'s public
     `incFixed_eq_none_iff`, at 100% (93 characters), which is the colleague's original. It is
     recorded for retirement as backlog F6-1(j). **The user acknowledged it (2026-10-12)**, on
     condition that the retirement stays on the backlog. Say whether placing the criterion in
     `Convention` is right, given that `EXPCOM` cannot import `CircuitComplexity`.
8. Report anything else the fill or its records misstate, in the standard table.

## Repository-side attestations (verify or challenge)

* **Delivery integrity.** The delivery's `SHA256SUMS` was all OK (41 entries; attached). Its
  environment shim and agent scripts were never compiled or run, and nothing references them.
  These are maintainer attestations.
* **Freeze:** `audits/logs/ch34-b5b-1-freeze.log`.
* **Replay** (user-run, fresh `.oleans` into the snapshot; `audits/logs/fills-6-replay.log`, at
  `56258cb5`): 41 modules, **0 errors**; `EXPCOM` has no sorry warning. The later maintainer
  commit `36503704` is comment-only, and `EXPCOM` elaborates after it with no errors.
  The CH34-D4 replay (`audits/logs/ch34-d4-replay.log`, at `6c7e35bd`) covers the factoring:
  167 modules, **0 errors**, with `EXPCOM` again free of sorry warnings.
* **Axioms** (`audits/logs/ch34-b5b-fill-gate-axioms.log`; probe
  `audits/evidence/ch34-b5b-fill-gate/AxB5bGate.lean.txt`, against the replay tree): every public
  of `EXPCOM`, `Relativization` and `Codes2Tape`, 23 in all. Thirteen walks are empty; the other
  ten (the summit, `EXPCOM`, `expCode`, both scheme instances, `EXP ⊆ P^EXPCOM`, the three
  identities and `baker_gill_solovay`) rest on exactly the two §12.11 rows. No non-standard axiom;
  the private censuses (EXPCOM 41, Relativization 140, Codes2Tape 24) find no `sorryAx`.
  After the factoring (`audits/logs/ch34-d4-axioms.log`), every walk is unchanged, and EXPCOM's
  39 private constants have no `sorryAx`.
* **Lint** (`audits/logs/fills-6-stylelint.log`): 0 FAIL over `Diagonalization`.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`. Findings go verbatim into
`audits/ch34-b5b-fill-findings.md`. The gate closes when it has zero blockers and zero majors;
CH34-D4 is ruled, and the user has acknowledged the factoring's one new pair (F6-1(j)).

## Erratum (gate round 1, majors 1–2 and minor 3; `audits/ch34-b5b-fill-resolutions.md`)

- **Bundle identity.** The authoritative bundle is SHA-256
  `6e4ad39959ca9b0387f045a9f9958aff03a062dc3283be42fed41332dcc578f5`, rebuilt after the user's
  F6-1(j) acknowledgement was recorded. `f6858d96…`, named by the round-1 kickoff, was the
  superseded first build.
- **Completeness.** This bundle carries the CH34-D4 screen's 25-file population, which contains
  the delivery's 22 files, at the gate head. It does not carry the other files of the 66-file
  union screen, nor the delivery population's versions at its base, so neither historical screen
  can be rerun from it. The round-2 bundle supplies them.
- **Ledger.** Item 4's cumulative count omits `expcom_inc_prefix` (107 characters). The corrected
  historical count is 5,037 of 13,500, **37.31%**.
