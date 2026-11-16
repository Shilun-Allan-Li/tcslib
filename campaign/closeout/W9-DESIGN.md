# W9 · Relativized hierarchy theorems: design note (draft for Seyoon, 2026-11-16)

D3 brought the relativized hierarchy theorems into scope, "ideally just by generalising the
existing hierarchy proofs rather than duplicating them". This note maps what the three existing
proofs depend on, proposes the shared interface, and sizes what generalizing costs. The size is
much larger than the plan assumed, so it ends with a scope decision.

Source: a read of the campaign after #325 (`20394834`); paths are under `TCSlib/Complexity/`.

## 1. The top level generalizes cheaply

Each hierarchy proof is already factored so that its final combination is abstract:

| Theorem | Top-level proof | What it uses about machines |
|---|---|---|
| Deterministic time, Thm 3.1 (`TimeHierarchy/Diagonal.lean:310`) | `DiagSimulator.time_hierarchy` | a computation predicate with `mono` and `output_unique`; the class `DTIME`; a clocked runner (`diagLangOf_mem_DTIME`, 216); a `DiagSimulator Φ` (244), itself `SelfSimulator.toDiagSimulator` (396) of a universal machine plus a normal form |
| Nondeterministic time, Thm 3.2 (`Diagonalization/NTimeHierarchy.lean:1803`) | lazy diagonalization, 75 lines | acceptance with `mono`, halting, the truncation lemma; ND codes with a normal form; the contract `exists_diagonalizer` (`NTimeDiagonalizer.lean:8418`) |
| Space, Thm 4.8 (`SpaceComplexity/Hierarchy.lean:3373`) | 15 lines | a space measure with a configuration bound; `sph_diagonal_language` (3157); `sph_code_window` (1109) without its `windowRun` conjunct |

`DiagSimulator` and `SelfSimulator` mention `FinTM` only in their field types. The oracle
side already has the matching pieces: `FinOracleTM.ComputesInTime O` has `mono` and
`output_unique` (`TuringMachine/OracleFinite.lean:113,121`), `DTIMEOracle`
(`ClassOracle/Classes.lean:83`) has the `DTIME` shape, and a plain machine embeds via
`toFinOracleTM` (so `TimeConstructible` needs no oracle version).

**Proposed interface.** One `MachineModel` structure (`Mach`, `Comp` with `mono` and
`output_unique`, the class `DT`, a `clock` field stating line 216), with `DiagSimulator`,
`SelfSimulator` and `time_hierarchy` restated over it; an ND extension (`Acc`, `Halts`,
truncation, `decode`, `normalForm`, `diag`); and a space extension (`space`, a configuration
bound, `diagLang`, `codeWindow`). The plain theorems become instances, with unchanged
statements; each relativized theorem is a second instance. The top-level proofs move almost
verbatim. This part is one maintainer refactor PR, about 300–500 lines changed.

## 2. The oracle instances are the cost

Every field of an instance is a machine construction, and the oracle layer has none of them.
It has no universal oracle machine and no effective oracle codes:
`exists_finOracleTM_enumeration` (`Diagonalization/Relativization.lean:538`) is classical
(`Fintype.equivFin`), which suffices for Baker–Gill–Solovay but gives no upper bound. Its
simulations remove the oracle (`exists_plain_simulation`, `Build/OracleSim.lean:2107`) rather
than simulate oracle machines. Per theorem:

| Relativized theorem | New oracle constructions needed | Plain counterpart (lines) | Rough size |
|---|---|---|---|
| Deterministic time | an oracle clocked runner (the fused output register must move to a tape around each query, since the answer step overwrites the state with `qYes`/`qNo`, `Oracle.lean:178`); effective oracle codes; a universal oracle machine that uses its own query tape natively, with per-code linear overhead; an oracle tape-reduction normal form that keeps the query tape | `ClockMachine` + `ClockLoop` 915; `UniversalK` 2,113 and parts of `Universal` 2,869; `Robustness/TwoTapes` 2,460; `Encoding` 799 + `CodePrefix` 277 | 6–9k lines; 5–8 fills |
| Nondeterministic time | everything above, plus an oracle ND interpreter core, a universal oracle NDTM, its exhaustive decider (`exists_choiceTM`, `OracleSim.lean:2579`, is a start), oracle ND codes and normal form, and the diagonalizer rebuilt over oracle components | `NTimeDiagonalizer` 8,465; `ClassNP/NDNormalForm` 3,229; `NDCodes`; the timed universal NDTM | a further 15–20k lines; 10+ fills |
| Space | an oracle space measure and class (none exists, `OracleFinite.lean:30`); an oracle window runner that makes real queries from inside its record window; an oracle self-universal machine with constant space overhead; space-faithful oracle normal forms | `Hierarchy` 3,438; `Build/WindowRun` 1,361; `SelfUniversal`; the `_spaceUsed` normal forms | a further 8–10k lines; 6–8 fills |

These are new constructions, not copies: each oracle version differs at every query step. A
"no duplication" route through the machine library itself (rebuild the plain constructions as
the oracle-free case of oracle ones) would rewrite the robustness, universal and clock
libraries that most of chapters 1–4 sit on, which is larger still.

**Oracle space convention** (needed only if space is in scope). Proposed: count the query tape.
It is work tape `Fin.last k` (`Oracle.lean:161`), so the configuration-generic
`spaceUsedOfCfgs` counts it with no new definition; it keeps `PSPACE^O` from asking queries of
exponential length, and configuration counting still bounds halting once `O` is fixed. The
alternative (the query tape write-only and uncounted, with a separate query-length bound) is the
other convention in the literature; AB09 does not fix one.

## 3. Decision for Seyoon

AB09 states the relativized hierarchies as a remark (§3.4: the hierarchy proofs relativize), not
as numbered theorems. Options:

- **(A) All three.** About 30–40k lines of new oracle constructions, more than twenty fills plus
  gates; the longest item left in the campaign by far.
- **(B) Interface plus deterministic time.** The `MachineModel` refactor (all three
  hierarchies restated over models, plain instances unchanged), then the oracle deterministic
  instance: `time_hierarchy` relativized for every oracle. 5–8 fills plus gates. The ND and space
  instances stay deferred, with the interface ready for them. **Recommended:** it delivers the
  relativized form of Theorem 3.1, which is the one usually cited, and does the generalization
  the ruling asked for, at a fifth of (A)'s cost.
- **(C) Interface only.** The refactor PR alone, with no fill; all three relativized
  statements stay deferred, recorded as instances still to be supplied.

The stale docstring found during the survey (`Relativization.lean:54` still says
`baker_gill_solovay` is sorried; it is proved at 962 and the file has no admission) is fixed in
the first refactor PR either way.
