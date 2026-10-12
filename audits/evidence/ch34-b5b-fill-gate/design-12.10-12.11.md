# Extract of machine-library-design.md at 1691e4d2: §12.10 (the oracle-call simulation) and §12.11 (the format-parameterized code simulator), lines 2314–2483

### 12.10 Oracle-call simulation (statements landed 2026-10-11; design W2, route and homes accepted by the user)

**Why.** §12.9 records the gap, "not yet here: oracle-call hosting". No public row lets a
plain host simulate an oracle machine by running a decider on each extracted query. Two
targets are blocked:
- B1's last, `POracle_eq_P_of_mem_P`;
- B5's summit, `NPOracle_EXPCOM_subset_EXP`, and through it three `EXPCOM` identities and
  `baker_gill_solovay`.

**The decision: one trace, and nondeterminism by choice words.**
- **The deterministic row is the only oracle-call simulation trace.** It is a plain host that
  answers each query by a clean call of the decider.
- **The nondeterministic form is a reduction, not a second simulation:**
  1. the choice-word machine determinizes the oracle NDTM along a word on a work tape;
  2. the deterministic row simulates it;
  3. the plain certificate shell and the proved `exists_proj_decider` enumerate the words.

  The total is `2^O(p)`.
- **Branchwise simulation is rejected.** Branches would consume choice bits through every
  decider run, so the only public determinization would enumerate doubly exponentially many
  words. Avoiding that needs a sparse-guess row, which is a second trace under another name.
- **Virtual input stays at the plain level, after the simulation.** An oracle machine has one
  `qQuery` state, so an oracle-level Z1 would re-prove Z1's lockstep. This forces the
  deterministic row to be stated **from preloaded starts**. The `initCfg` form, the B1b draft
  headline, is a proved corollary.

**Rows.**

| Module | Declaration | Status |
|---|---|---|
| `Build/OracleSim.lean` | `FinTM.prefixWords` (+ `_nil`, `_update`), `Cfg.init_eq_ofWords`, `OracleTM.queryString_runFrom_length_le_of_blank` (W2-0) | proved |
| | **`FinOracleTM.exists_plain_simulation`** (W2-S): from any preloaded start, a plain host reproduces the oracle machine's halting output within `a·(t+1)² + a·Σ_{r<t} [query at r]·τ(\|query_r\|)` | sorried |
| | `…_of_monotone`, `…_initCfg`, `FinOracleTM.exists_plain_decider` | proved from W2-S |
| | `FinOracleNDTM.choiceOut`, `choiceOut_eq_true_iff`, `mem_iff_exists_choiceOut` | proved |
| | **`FinOracleNDTM.exists_choiceTM`** (W2-C): the choice-word machine, `≤ 2\|u\| + 2` steps, the same queries | sorried |
| `Build/CertShell.lean` | **`FinTM.exists_certificateShell`** (W2-V): the plain shell deciding `{x ++ u \| \|u\| = C(\|x\|+1)^c ∧ out x u = [true]}` | sorried |
| | `FinTM.certificateShell_proj` | proved |

- The exact sum, "`T_D` of the query lengths", needs no monotonicity.
- Both instantiations follow from the monotone corollary:
  - polynomial `τ` gives `P^O = P`;
  - exponential `τ`, at a polynomial-time machine, gives `P^EXPCOM ⊆ EXP`, and the summit
    follows through W2-C.

**Fill routes** (binding sketches in the docstrings).
- **W2-S:**
  - the source's tapes, a shadow tape tracking the query head's side of the origin, the Z1
    bank of the clean call `exists_installCallTM`, and a scratch tape;
  - off `qQuery`, the bridge `runFrom_eq_plainEmptyOracle` plus Z5;
  - at `qQuery`, nine R2-seamed phases: bookmark, origin walk, save and blank cell `-1`,
    `copyTM`, the Z1 call at `y = []`, read the verdict, restore, walk back, answer.
- **W2-C:** lockstep by induction on `u`, in the `toOracleNDTM_runWith` shape. An exhausted
  word answers `false`, so an unhalted branch never shows `[true]`.
- **W2-V:** the native-input call R8.5e (`exists_inputCallTM`) at `splitSolve`, then Z1 inside
  the **returning** R1 capture, then a three-state scan. R8.5e is proved at the tip since PR
  #41, so W2-V's route cites no sorried row.

**Decisions.** The user took the first and third (2026-10-11); the rest are as drafted and
go to the statement gate.

1. **The route:** one trace, choice-word enumeration, no branchwise row.
2. **W2-S in preloaded generality,** with the `initCfg` form derived.
3. **W2-V in its own plain module,** `Build/CertShell.lean`, keeping plain consumers off the
   oracle module. Deduplicating the private 2B shell in `ntime_poly_subset_NP` is the shell's
   second customer, a 12.2c item.
4. **W2-C is public here.** It is the core of a relativized Theorem 2.6. It has one named
   customer, against the rule of admission's two.
5. **Time only.** The oracle layer has no space measure. This is flagged against the §12/§13
   space mandate.
6. **Sequencing.** W2-S and W2-C can be filled at once; W2-V's sorried dependency is gone.

**Mirrors, factored** (disclosed at landing; factored in round 2 of the wave-1 statement gate,
2026-10-11, user decision; `audits/wave1-statements-resolutions.md`):
- W2-0 and the private invariants `runFrom_workTapes_invariant` (`Oracle.lean`) and
  `runWith_headBlank` (`OracleNondeterministic.lean`) now all specialize the promoted
  `OracleTM.step_radius`/`OracleTM.runFrom_radius` (`Oracle.lean`).
- `certificateShell_proj` and `Nondeterminism.lean`'s split callers cite
  `append_split_unique` with `certificateLength_strictMono` or
  `expCertificateLength_strictMono` (new module `ChoiceWords.lean`). The private split lemmas
  are deleted.
- `mem_iff_exists_choiceOut` and `Nondeterminism.lean`'s acceptance argument share
  `choiceBudget_le` and `run_take_of_halted` (`ChoiceWords.lean`).

**Consumers** (derived in `audits/evidence/wave1-statements/S1210StatementsProbe.lean.txt`):
- `POracle_eq_P_of_mem_P`, which rests on W2-S alone;
- `NPOracle_EXPCOM_subset_EXP`, the summit;
- `baker_gill_solovay`.

Each is `rfl`-identical to its campaign statement, as are the three `EXPCOM` identities the
probe also derives. The probe's deterministic inclusion `POracle_EXPCOM_subset_EXP'` is
probe-local: it is derived from W2-S directly and has no campaign counterpart.

B5's own `exists_EXPCOM_decider` (home `Diagonalization/EXPCOM.lean`) is the summit's
query dispatcher. It is a B5 obligation, not a §12.10 row.

### 12.11 The format-parameterized code simulator (B5a; statements landed 2026-10-11; headline H1 by user decision, H2 in the backlog)

**Why.** Plan §4e decision 2: "B5 builds one format-parameterized uniform interpreter and
discharges ZF-B4, on top of 12.2c item 8's parameterized parse layer".
- `Universal`'s interpreter is hard-wired to one work tape, and is already copied once inside
  `Universal.lean`.
- ZF-B3's layer in `Codes2Tape` is format-specific and contains no interpreter.
- `CodeFormat` has no machine semantics.
- The two target files cannot host a layer for each other: EXPCOM's closure contains neither
  CounterLoop nor VirtualInput, and Codes2Tape is not imported by EXPCOM.

Hence a pre-issue statement module.

**Rows** (`TuringMachine/CodeSimulator.lean`).
- **`Turing.MachineFormat extends CodeFormat`** adds:
  - a work-tape count `k`;
  - a semantics `machine`;
  - two laws: `serialize_eq`, the fixed `k`-record serialization `serializeK`, and
    `skipTable_eq`, the fixed skipper `codeSkipTableK k`.
- **The generic writer layer:** `workReadsK`, `tableBitsK`, `serializeK`, `codeSkipTableK`,
  with proved bridges `tableBitsK_two` and `codeSkipTable2_eq_codeSkipTableK` to the frozen
  two-tape writers.
- **`oneTapeMachineFormat`,** public and proved. Its `decode` is `codeDecode`, and its
  machine is `CodeTM.toFinTM`, both by `rfl`.
- **`MachineFormat.exists_polyCanonizer`** (sorried): one machine computing
  `F.serialize (F.decode α)` in polynomial time. It serves the simulator's front end, the
  `canonizer` field of both uniform schemes, and, off-batch, the TMSAT concrete-scheme
  canonizer.
- **`MachineFormat.exists_uniformSimulator`** (sorried), **H1**. On
  `⟨⟨bits t, α⟩, x⟩` it answers `[true]` iff the decoded machine computes `[true]` on `x`
  within `t` steps, and `[false]` otherwise, within `d·(|α| + |x| + t + 1)^d`. This is
  field-for-field the shape of `UniformMachineCode.simulator_accepts`/`_rejects` and their
  `…2` mirrors.

**Inside H1:** exactly one private interpreter trace, a step block for one simulated
transition of a `k`-tape coded table. It is hosted by §12.7's `counterLoopTM` and Z1's
`vhostEmitTM`, built from the §12 layer, and is not a copy of `universalInterpreter`. Its
properties:
- states independent of the code;
- per-round cost `c·(|β| + 1)`, independent of `t` and `x`;
- input read only through its own head;
- silent;
- proved at the relation level.

Per-round cost independent of `t` and `x` lets stage 1, B6 and the NTIME deterministic core
reuse it under different hosts.

**Instances** (B5a fill):
- **EXPCOM:** `exists_uniformMachineCode` at `oneTapeMachineFormat`.
- **ZF-B4:** `exists_uniformMachineCode2` at a private two-tape format in `Codes2Tape`, whose
  laws are the two bridges.

The two assemblies are a forced mirror pair, as their target structures are. Both are
assembled from H1 in `audits/evidence/wave1-statements/B5aStatementsProbe.lean.txt`, resting only on the
two contracts. **NDCodes is not an instance:** ND codes denote NDTMs and need no interpreter.
A separate small parse-layer rider can handle them.

**Decisions** (from the dossier's D1–D9):
- **D1 (user, 2026-10-11).** A pre-issue statement phase. It is landed by the combined
  statement PR, under one gate.
- **D3 (user, 2026-10-11).** Headline **H1** for now. **H2** is per-code linear,
  `d·(|α|+1)^d·(t+1)` with no `|x|` term. It would serve stage 1 directly, but forces
  in-place suffix input and a suffix-input host that does not exist. H2 is recorded in
  `backlog.md`, and its corollary to H1 is proved in the probe.
- **D2 and D4–D9 are fill-brief matters**, settled when the B5a brief issues. The dossier
  recommends route Z, the generic interpreter at `k = 1`, for EXPCOM, with route W
  (Universal plus a post-processor) as an escalation fallback only. It also recommends moving
  ZF-B3's semantic layer into `CodeSimulator`, generalized, and deleting the dead ZF-B3
  privates.

**Forced writer pairs.** The generic `tableBitsK` reproduces part of the frozen writers'
text. The statement screen gives three such pairs: `oneTapeFormat` at 85%, `codeTable2Bits`
at 67% and `Code2TM.serialize` at 56%. The frozen bodies cannot be redefined, and
`tableBitsK_two` proves the equalities. This is item 8's pre-named residual watch item.

