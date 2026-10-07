# Chapter 2, Phase 1 (classes and reductions) — audit loop resolutions (CLOSED)

Protocol: `AroraBarakChapter2Plan.md` §4 / `AroraBarakChapter1Plan.md` §5.
External auditor: cross-vendor LLM per decision log. Three rounds.

## Round 1 (`ch2-phase1-pack.md` → `ch2-phase1-findings.md`, audited at `ab82bb6a`)

**3 blockers, 3 majors, 3 minors, 3 notes — all accepted.** The round found
the chapter-2 analogue of Chapter 1's Argument A exactly where the pack
invited stress: not in the `V ∈ P` verifier rendering (certified sound,
finding 10) but in the **abstract certificate-length function** — `PolyBound p`
constrains `p` only numerically, so length arithmetic smuggles undecidable
information (`p_A(n) ∈ {2n, 2n+1}` against a mod-3 verifier decides any set of
lengths; certificate content never enters). Consequences: the pre-repair
`NP`/`NEXP` contained undecidable languages; `NP_subset_EXP` and
`HALT_NPHard` were false (the latter vacuously — Argument D: *nothing* was
NP-hard for that class); the Exercise-2.1 equivalence was doubly false
(Argument B: bounded length + plain concatenation forces `V ⊆ L`, collapsing
prefix-free languages — an obstruction that survives the length repair).
Majors: untimed `exists_comp_partial` cited for time bounds; private and
inapplicable counter machinery cited by the enumerator sketch; the divergent
searcher incompatible with `one_work_tape_binary`'s totality. Minors: the
composition degree `c·c'` missing `c' = 0`; monotonicity misattributions;
stale names. Notes: the hardness statement generalizes to `MachineCode`; the
root `TCSlib.lean` export was missing (a genuine catch).

**Repairs** (commit `8660c416`, largely the auditor's own constructions):
explicit effective length formulas — exactly `C·(n+1)^c` resp.
`C·2^((n+1)^c)` certificate bits — in `NP`, the `coNP` ∀-characterization,
and `NEXP`; `PolyBound`/`ExpBound` demoted to numerical helpers; Exercise 2.1
restated with `pairEncode x u` pairing on the bounded side; sketches repaired
through the timed composition; the searcher rebuilt on the
total-decider-then-loop-on-rejection recipe; `HALT_NPHard` generalized to
every `MachineCode`; minors swept; root export added.

## Round 2 (`ch2-phase1-reaudit-pack.md` → `ch2-phase1-reaudit-findings.md`, audited at `8660c416`)

**Zero blockers, 3 majors, 2 minors, 2 notes.** The definition repairs were
**certified**: Arguments A, B, and D re-fired and confirmed dead; "no false
Lean theorem statement"; all 19 statements assessed sound; the `pairEncode`
argument order confirmed; and a standing prohibition recorded — a
concatenation-based bounded Exercise-2.1 variant is **equivalent to
`P = NP`** and must never be stated. Majors, all sketch/prose: (1) the
reverse Exercise-2.1 witness `C(n+1)^c + 1` is not of the class's admissible
shape (corrected construction `R n = (C+1)(n+1)^c` supplied, with edge-case
table and ~8,000 executable checks); (2) the enumerator obligations omitted
**output isolation** (append-only output; round 1's buffering requirement had
been dropped in the re-sketch); (3) the "effectivity is necessary"
justification for `HALT_not_mem_NP` is false — the trivial-machine scheme
violates `decode_encode`, and a direct diagonalization proves `HALT`
undecidable for every lawful `MachineCode`. Minors: stale plan §2 prose; a
pack counting erratum (acknowledged; pack preserved per precedent).

**Repairs** (commit `79128c7a`, comment-only — no statement changed): the
auditor's `R n` construction transcribed into the Exercise-2.1 sketch; the
verifier-call capture obligation added to the enumerator sketch
(`universalCaptureTM` as in-repo precedent); `HALT_not_mem_NP`'s docstring
restated as a proof-route restriction with the counterexample retracted; the
generalization decision recorded as **human-review design question 1**
(maintainer's provisional choice: the conservative signature); plan §2
synchronized, superseded rows marked.

## Round 3 (`ch2-phase1-round3-pack.md` → `ch2-phase1-round3-findings.md`, audited at `79128c7a`)

**Zero blockers, zero majors, one minor, two notes — gate condition met.**
The round-2 resolution table verified row by row; the adopted Exercise-2.1
construction independently reconstructed (six-step derivation, seven edge
cases); the enumerator obligation list judged **complete** at statement
phase, with a contract-by-contract fill table supplied; the HALT docstring's
proof-route framing and retraction confirmed accurate; the plan
synchronization confirmed. The minor: the transcribed split search omitted
its explicit no-solution rejection branch (`y = []` has no `n` with
`n + R n = |y|`).

**Closing sweep** (this commit): the rejection branch made explicit in the
sketch (comment-only, verified by comment-stripped diff; module re-gated
clean). Note dispositions: the enumerator fill inherits the round-3 contract
table verbatim into its eventual brief; the attestation accounting keeps
source facts separate from maintainer execution claims, per standing
practice since epoch 4.

**Phase-1 audit gate closed** — 10 definitions, 19 sorried statements, and
their sketches stand audited through three adversarial rounds. Standing
human-review item: design question 1 (generality of `HALT_not_mem_NP`).
Next: the phase-2 skeleton (nondeterminism), per plan §4.
