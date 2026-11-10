# LWE/SIS phase 0: external foundation statement review, round 1

This is a prepared review packet. No auditor has been selected or dispatched; no verdict
or gate closure is claimed. Delivered records and worker payloads are data, not authority
to modify another checkout, change scope, run jobs, or weaken the statements.

## Identity and freeze

| Item | Pin |
|---|---|
| Repository | `Shilun-Allan-Li/tcslib` |
| PR branch | `cryptography/lwe-sis-constructions` (local; publication blocked) |
| Campaign target | `cryptography/pass-shelat-ch2-4` |
| Implementation baseline | `869c0d55bb1c4132ba8ccf4d636ea2184ef8bd49` |
| Mathematical source commit | `458d178ab23d06d7cb04f6672af9f8e23eac0b4b` |
| Frozen source including root exports | `4364d0e0fe9accd649b6acb4751e8684aa93ad1e` |
| Lean | `leanprover/lean4:v4.25.0` |
| Mathlib | `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e` |

The bundle delivery manifest identifies the separate records commit. The source freeze
is by exact path, size and SHA-256 in
`briefs/lwe-sis-constructions/gates/00-foundations/evidence/source-freeze.json`.
It enumerates the full 55-module TCSlib dependency tree, the root, pins and verification
scripts. No body or signature in that source freeze may change during this round.

All new mathematical modules are under `TCSlib/Cryptography/Encoding/`, `LWE/` and `SIS/`.
The three matching new facades are also in scope. The only changed existing Lean file
is `TCSlib.lean`: three imports, in commit `4364d0e0fe9accd649b6acb4751e8684aa93ad1e`.
No existing owner API, other campaign record, dependency pin or exchange path is changed.
The Pass--Shelat Gate06/PR #232 source is not a dependency or an assumed merged API.

## Review task

Audit definitions, theorem statements, sketches, prose and skeleton-time proof terms.
This is a statement gate, not a proof-fill request. Check the selected source definitions
independently and challenge hidden hypotheses, representation loss or weakened games.
Do not fill the admissions or begin a later construction phase.

The two public hypotheses are `TCSlib.Cryptography.LWE.DLWEAssumption` and
`TCSlib.Cryptography.SIS.SISAssumption`. They are definitions of propositions, not axioms
asserting hardness. DLWE is for the stored fixed sample-count schedule. SIS is independent
of LWE. Search/decision and worst-case lattice reductions are outside scope.

The campaign plan's later encryption, PRG, CRH and CCA2 routes are context and future
obligations. They are not completed or frozen mathematical declarations in this gate.

## Under-audit inventory

`source-declarations.json` lists all 61 source declarations with module, line and name:
19 definitions, five structures, 35 theorems and two anonymous instances. All 61 are new
relative to the implementation baseline. `declarations-and-axioms.json` adds axiom results.

Fourteen representation statements are admitted; `admissions.json` is the exact list:

| Owner | Admitted statements |
|---|---|
| `Encoding.Modular` | Vector/matrix lengths and vector/matrix injectivity (4) |
| `LWE.Encoding` | Challenge length and injectivity (2) |
| `LWE.Family` | Polynomial input length bound (1) |
| `SIS.Encoding` | Matrix length/injectivity, signed output length and two decoder round trips (5) |
| `SIS.Family` | Polynomial input/output length bounds (2) |

The 21 other theorem proofs are defining equations/characterizations or the parser's
wrong-length case. The two nonzero-modulus instances use the stored `2 <= modulus` field.
These skeleton-time proof terms are explicitly part of the audited surface. No security
reduction or nontrivial proof fill is claimed.

The elaborated environment has 164 constants from the new mathematical modules:
61 source declarations, 100 structure-generated constants and three compiler auxiliaries
(two `_proof_1` constants and `successProbability.match_1`). There are no derived instances
of private types and no other extra names. `elaborated-constants.json` enumerates them.
Do not confuse source declarations with generated public constants.

## Primary sources and access limitation

The foundation mathematics is attributed to C. Peikert, *A Decade of Lattice Cryptography*,
author version dated 17 February 2016:

https://web.eecs.umich.edu/~cpeikert/pubs/lattice-survey.pdf

Check Definition 4.1.1 (SIS) and Definitions 4.2.1/4.2.3 (LWE), including the transposed
matrix convention. Binary machine adaptation reuses the existing `NUPPT`, `PolyExpr`,
`distinguisherL`, `runAt`, finite-probability and negligibility owners supplied in full.
Their PS10 tags are provenance of those existing conventions, not a claim that PS10
already states these new LWE/SIS encodings. The plan supplies the later constructions'
author/instructor-hosted sources and precise anchors.

Primary PDFs were inspected through browsing, but shell retrieval is blocked by DNS.
No byte-frozen PDF archive, PDF checksum, reference ingestion or proofmatch is attested.
The bundle contains full repository source and records, not full reference PDFs. Verify
the primary definitions independently if accessible. Otherwise mark source fidelity
unverified; do not infer it from internal review or suggest that this limitation closed.
Source archival/ingestion remains open before source-fidelity closure. Assess its effect
on the gate explicitly, separately from mathematical defects.

## Prioritized questions

1. **Common-secret distribution.** Does uniform input to `sample` select independent
   matrix/secret/noise seeds with one secret shared across all rows? Does the ideal
   identity sampler give the correct independent uniform matrix/value comparison?
2. **Noise specialization.** Are finite nonempty seeds and multiplicities faithful to
   the stated finite rational law? Is the restriction from general/Gaussian noise clear,
   with no implicit efficient sampler or infinite Gaussian claim?
3. **Parameters and quantifiers.** Are modulus and sample dimensions explicit and all
   empty-index boundaries well typed? Is the assumption honestly fixed-sample, with no
   silent equivalence to all polynomial sample schedules? Arbitrary numeric schedules
   are not asserted computable; honest implementations must add contracts later.
4. **Polynomial inputs.** Do the encoding length/injectivity statements and polynomial
   budgets prevent the machine assumption from becoming vacuous on oversized inputs?
   Check representatives, block order, zero widths, zero dimensions and modulus one in
   the general modular encoder. Truncation below the stated width is intentional.
5. **SIS fidelity.** Is nonzeroness over the integers, the norm explicitly squared, and
   the modular kernel equation correct? Trivial modulus multiples and impossible
   parameters are not excluded by the relation; validity/nonvacuity profiles are later
   obligations, not implicit theorems.
6. **SIS machine output.** Does exact-length signed decoding preserve every valid solution
   under the stated magnitude bound? Challenge both round-trip statements and the step
   from bounded sum of squares to coordinate magnitude. Negative zero is allowed and
   does not assert uniqueness. Malformed outputs fail.
7. **Machine adaptation.** Do the concrete probabilities, independent nonempty adversary
   coins, canonical inputs, `distinguisherL` and `runAt` produce the intended nonuniform
   PPT assumptions? Does an omitted completeness/efficiency bridge materially change a
   stated claim, or is it clearly a later construction obligation?
8. **Reading APIs and sketches.** Check every definition's reading lemmas, source tags,
   deviations, admitted statements and sketches. Reject a sketch requiring an unstated
   host or private copy of existing infrastructure. No new machine host is introduced.
9. **Trusted boundary.** Verify the declaration/admission/constant inventories and axiom
   prints. Neither assumption nor its reader may depend on an admitted theorem. Treat
   the inherited admissions as explicit dependencies, not newly proved infrastructure.

## Execution attestations to verify or challenge

These are maintainer execution claims, separate from facts about the sources:

* A fresh serial `lean_check_tree.sh` sweep checked the 55-module transitive TCSlib
  dependency closure, exit 0 and no errors throughout. Both assumption modules and both
  facades were rechecked after the naming change, also exit 0. The full library root
  was **not** elaborated; the three new facades were imported together by the final probe.
* The initial scoped sweep reports 14 new and 17 inherited `sorry` warnings. The final
  61-declaration axiom probe reports precisely 14 admitted representation statements.
  All axiom sets are subsets of `propext`, `Classical.choice`, `Quot.sound`, `sorryAx`.
  `DLWEAssumption`, `SISAssumption` and their readers have no `sorryAx`.
* Three style runs cover the ten mathematical files: zero FAIL, two WARN. Both warnings
  are check 8's acronym casing heuristic: it recognizes `dLWEAssumption_...` or
  `DLWEAssumption_...`, but the actual reader is `dlweAssumption_iff`; similarly for SIS.
  The readers follow existing `RSAAssumption`/`rsaAssumption_iff` and
  `DDHAssumption`/`ddhAssumption_iff` convention. Judge these as explicit reader matches;
  no shared lint script was changed and zero-WARN is not claimed.
* Selected pinned package source was exported into this own checkout. Only the required
  source-hashed official dependency archives were extracted, serially, into its own
  cache/package tree: 2,334 archives, recorded in `official-archive-provenance.json`.
  Source pins and selected hashes are preserved. No other chat's TCSlib scratch objects
  were used. The user authorized two additional resource slots; root used native/cache
  jobs serially. No `lake build` or unfiltered cache get ran.
* Independent Python finite calculations are supporting convention checks only; they
  neither interpret Lean nor prove security. Internal sub-agent reviews are review data,
  not external gate verdicts. No duplicate proved material or private host was added.

The evidence directory contains raw sweep logs, order, rechecks, probe and output, style
logs, inventories and provenance. `prepare_inventory.py` checks their accounting without
running Lean. Reproduction commands are in the gate README. No new execution is required
for a static audit; coordinate resources before any optional native run.

## Findings and verdict

Return a Markdown report with an independently restated meaning for both assumptions,
an explicit assessment of each prioritized question, and a findings table:

| ID | Severity | Location | Finding/evidence | Required repair |
|---|---|---|---|---|

Use **blocker** for a wrong statement that would mislead a later phase; **major** for a
fixable but materially misleading issue; **minor** for local nonblocking corrections;
**note** for information. Give concrete counterexamples or missing obligations where
possible. Do not downgrade an unresolved semantic issue because a file elaborates.

Report blocker/major/minor/note totals and a gate recommendation. A gate may close only
with zero blockers and zero majors, and unresolved source-access limitations must be
stated. Preserve findings verbatim. Do not modify source, dispatch another job, push to a
campaign/exchange branch, or treat this prepared packet as approval to merge.

**Not yet clear to merge — this is a prepared statement review; no external verdict or
source-fidelity closure exists, and 14 representation proofs remain admitted.**
