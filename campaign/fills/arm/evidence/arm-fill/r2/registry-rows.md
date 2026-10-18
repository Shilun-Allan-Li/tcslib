# Draft rows for `machine-library-design.md` §14: the received ARM machinery (finding 5)

Draft for the maintainer to land in the design document, matching the registry's four columns
(`# | Host | Status | Named consumers`). Declaration lines are MEASURED at the tip (the Lean tree
is identical at `39bfdca4` and `e831b5b0`; `audits/logs/arm-fill-r2-registry.log`, header line of
each declaration). "Consumers today" are the direct importers outside the component, from the
tip's import graph (same log), with the named theorems that use them. Nothing here changes Lean.

**Status of these rows (user decision 3, 2026-10-14).** The received machinery is registered with
public contracts. Its first uses, the consumers named below, all inside the delivery `8c23f3bc`,
are an **accepted exception** to *hosts come first* (`policy.md` §1): they were not
statement-gated before their consumers were written. **Gate before reuse:** no further consumer
of any row below (H7–H13) is briefed until that row's public contract has passed a contract gate
(a statement gate of the contract as listed, or of its generic form). The generic forms are
ARM-2's direction (backlog §1 ARM-2): designed with Hydroxyi, not scheduled.

## The rows (registry format)

| # | Host | Status | Named consumers |
|---|---|---|---|
| H7 | **ARM compiler and its decision bridges** (Hydroxyi's `LogProg` tree, `SpaceComplexity/Machines/`): the register-tape compiler from an arbitrary seam (`compile_correct_from`), the space bridge `arm_space`, and the decision bridges at logarithmic width (`arm_decides`, `arm_decides_poly`) and at general width (`arm_decides_space`, `arm_decides_SPACE`, `arm_decides_pspace`, `_of_logspace`, `_val`); the loop and reachability kit (`GuardLe`, `ARMLoops`, `arm_reach`, `VWord`) | **received 2026-10-14 (`8c23f3bc`); public, ungated; first uses an accepted exception (decision 3).** `compile_correct_from` and the wide bridges are new; `arm_decides`, `arm_space` predate (chapter-6 campaign, `f70c57c2`). No time clause: ARM instructions are unary in register values, so time goes through H9 | `TQBF_mem_PSPACE` (H13e), `PSPACE_eq_NPSPACE` (H13a), the codec's deciders (H10), the PATH-hardness bit deciders (H13d), `searchLang_mem_PSPACE` (example); through H8/H9 every ND and time customer |
| H8 | **Nondeterministic ARM (NARM)**: `choose` instructions driven by a choice word, compiled to a `FinNDTM` by the `detPart` override; the space bridge `narm_space` and the class bridges `narm_decides_space`, `narm_decides`, `narm_decides_poly`, `narm_decides_npspace`; the termination layer `NTerm`/`NAcc`/`NSem` | **received 2026-10-14; public, ungated; accepted exception.** Supersedes for now §16b item 4's route (C2 as programs with coins; stage 2 paused) | `PATH_mem_NL` (H13c), `compl_mem_NSPACE` and through it `compl_PATH_mem_NL`, `NL_eq_coNL`, `NSPACE_compl_eq` (H13b) |
| H9 | **Memory ARM (MARM) and its time bridge**: a monotone Boolean memory tape (`mread`, `mset`, `mleft`, `mright`), compiled by the same `detPart` override; the configuration count `runFrom_count_eq` and the bridge `marm_dtime` into `DTIME` | **received 2026-10-14; public, ungated; accepted exception.** The count needs the monotone-write hypothesis `hwrite` and is valid along one run only | `NSPACE_subset_exp_dtime` (H12), hence `NL_subset_P`, `polyTimeReducible_of_mem_NL` |
| H10 | **Configuration codec and code deciders** (the fifth configuration encoding): `InWin`, `cfgWord`/`cfgCode`, the bound `cfgCode_lt`, injectivity up to `NDTM.coreSum`, the decoder; the four code languages and their `LOGSPACE` deciders; the chain bridge `mem_iff_codeChain` / `mem_of_codePath` | **received 2026-10-14; public, ungated; accepted exception.** `InWin` retires into `Turing.Cfg.InWindow` in the payback PR (D1, decided). RD-2's `ConfigCodec` has no consumer (fills held) | H13a (Savitch), H13b (inductive counting, through H13a's decider bank), H13d (PATH hardness), H12 (`ExpBFS`), H13f (TQBF hardness's verifier and machine) |
| H11 | **Indexed input access** (ours, `SpaceComplexity/Logspace/`): the input bit and length languages `inputBitLang`/`inputLenLang` read by an oracle call on a register-held index, the bounded decoder `boundedDecode_loop`, and the preimage host (`PreimageHost.compile_decides`, `mem_LOGSPACE_preimage`) | **existing (2026-10-11), public; now a host with received consumers.** The response proposes it stay under `Logspace/` (addendum 1). D7 and `decChain` (decided): one parameterized stride decoder here, with `Codec/Engine`'s as instances | every received ARM customer through its decider bank; `Codec/Engine` (D7 copy); `PathHardRegs` (`mem_LOGSPACE_preimage` for `dropIdx`); `ARMLoops`, `NARMKit`, `VWord`, `ARMWidthExample` (direct importers) |
| H12 | **Code reachability with a growing window (`ExpBFS`)**: the reachable-code sets `RCode`/`rset` per radius, the stop rule (`mem_iff_of_card_eq`, `card_rset_succ_of_le`), the window lemma `inWin_runWith_of_decides`, and the breadth-first MARM search giving `NSPACE_subset_exp_dtime_of_le` | **received 2026-10-14; public, ungated; accepted exception.** Built at ARM level, so H4's language-first route and MIG-19 are moot for this theorem | `NSPACE_subset_exp_dtime` (`ExpTime.lean`) and its two corollaries; inductive counting (H13b) uses the stop rule (`ISCountGenRadius`, `ISCountGenCorrect`) |
| H13 | **The customer machines**, one consumer each, with their own reachability notions: (a) Savitch's midpoint recursion `SavitchARM` with its code-decider bank; (b) inductive counting `ISCount*`; (c) the PATH walk `PathWalk*` with `WalkLe`; (d) PATH hardness `PathHard*` (the code graph `red`); (e) the TQBF walk `TQBFARM`; (f) TQBF hardness `TQBFHard*` (the ∀-folded midpoint formula and Tseitin after the prefix) | **received 2026-10-14; public, ungated; accepted exception.** (a)–(e) are machines over H7–H10; (f) is a reduction over H10 and the polynomial-time closure algebra | (a) `PSPACE_eq_NPSPACE`; (b) `compl_PATH_mem_NL`, `NL_eq_coNL`, `NSPACE_compl_eq`; (c) `PATH_mem_NL`; (d) `PATH_NLComplete`; (e) `TQBF_mem_PSPACE`; (f) `TQBF_PSPACEHard`, `TQBF_PSPACEComplete`. Second uses inside the delivery: (b) uses (a)'s decider bank and H12's stop rule; (b) and (d) use (c)'s `WalkLe` and `rawEdge` |

## Contracts, consumers, resource clauses and generic forms

### H7: ARM compiler and decision bridges

- **Public contracts:** `Machines/Compile.lean:123` `compile_correct_from`; `:206`
  `compile_correct` (its initial-seam case); `Machines/ARMRun.lean:259` `arm_space`;
  `Machines/ARMProof.lean:223` `arm_decides`; `Machines/ARMKit.lean:78` `arm_decides_poly`;
  `Machines/ARMWidth.lean:104` `arm_decides_space`, `:193` `arm_decides_SPACE`, `:241`
  `arm_decides_pspace`, `:303` `arm_decides_pspace_of_logspace`, `:319` `arm_decides_pspace_val`;
  class facts `:55` `LOGSPACE_subset_PSPACE`, `:62` `SPACE_succ_pow_subset_PSPACE`; kit
  `Machines/ARMLoops.lean:60` `GuardLe` (loops `move_run` `:80` … `shl_run` `:325`),
  `Machines/ARMReach.lean:197` `arm_reach`, `Machines/VWord.lean:93,101` `vword_whole₂/₃`.
- **Consumers today (direct importers outside):** `TQBFARM/Machine`, `Codec/Engine`, `Codec/Run`,
  `ExpBFS/Machine`, `Logspace/PathWalk`, `Machines/{MARM,NARM,NARMKit,NARMProof}`,
  `SavitchARM/{Machine,Reach}`, the facade; pre-existing importers of `Compile`:
  `Machines/{CleanSweep,Lib}`.
- **Resource clauses:** `compile_correct_from`: from `seam c₀` of an arbitrary program
  configuration, a finite compiled duration with the register envelope `[lo, hi]` and oracle heads
  `≤ B` throughout, given `CallOK` at each call (existence of a duration, no time bound).
  `arm_space`: cells `m (W + 2) + kD (2B + 1)`. `arm_decides_space`: digits `W ≤ C·S`, `1 ≤ S`,
  every decider's space at every virtual length `v ≤ 2n + 2 + m (2W + 2)` at most `C·S`, giving
  `L ∈ SPACE S`. `_pspace_val`: values `≤ 2^(C₀ (n+1)^c₀)`, `PSPACE` deciders.
- **Intended generic form (ARM-2):** one decision-bridge core over a step-semantics interface,
  width and oracle-space bound as parameters; `arm_decides`, `arm_decides_space`, the NARM and
  MARM bridges its instances (finding 2's twelve include four re-derivations of `arm_decides`).
- **Relation to existing rows:** this is a second compilation route into `FinTM`, parallel to the
  language-first plan (§15, stage 2, paused). H1 and H4 prescribe the language-first evaluator and
  search; the received customers instead use this route. Which route later consumers take is the
  contract gate's question.

### H8: NARM

- **Public contracts:** `Machines/NARM.lean:61` `NIns`, `:68` `NARM`, `:97` `nastep`, `:107`
  `narun`, `:213` `NHalts`, `:220` `NAns`; `Machines/NARMCompile.lean:188` `ncompileTM`, `:197`
  `ncompileFinNDTM`; `Machines/NARMRun.lean:226` `narm_space`; `Machines/NARMProof.lean:139`
  `narm_decides_space`, `:195` `narm_decides`, `:247` `narm_decides_poly`, `:280`
  `narm_decides_npspace`, `:349` `narm_decides_npspace_of_logspace`, `:60` `NSPACE.mono_const`
  (class fact, finding 12's home); `Machines/NARMKit.lean:70` `NTerm`, `:81` `NAcc`, `:87` `NSem`,
  `:321` `NSem.decides`.
- **Consumers today:** `Logspace/{ISCountGenCorrect,ISCountRegs,PathWalkMachine,PathWalkProof}`,
  `Machines/MARMCompile` (reuses the `detPart` construction), the facade.
- **Resource clauses:** `narm_space`: one budget `T` within which every branch halts; every branch
  of length `T` within `m (W + 2) + kD (2B + 1)` cells; acceptance by some branch iff
  `NAns … N true`, exactly `FinNDTM.DecidesInSpace`'s per-input clause. `narm_decides_space`: the
  hypotheses of `arm_decides_space`, with `NHalts`/`NAns` at a uniform `N`.
- **Intended generic form (ARM-2):** the nondeterministic bridge derived from the deterministic
  one through `detPart`; the one-step `NHalts` lemma once.
- **Relation:** §16b item 4 (C2 as programs with read-once coins, compiled by stage 2) covered the
  same customers; stage 2 is paused, and this row now serves them.

### H9: MARM and its time bridge

- **Public contracts:** `Machines/MARM.lean:62` `MIns`, `:75` `MARM`, `:112` `mstep`, `:130`
  `MReach`, `:136` `MHalt`; `Machines/MARMCompile.lean:141` `mcompileTM`, `:150` `mcompileFinTM`;
  `Machines/MARMTime.lean:214` `runFrom_count_eq`, `:444` `marm_dtime`.
- **Consumers today:** `ExpBFS/Machine`, the facade.
- **Resource clauses:** `marm_dtime`: one `FinTM` for all inputs, time
  `2^(C (W|x| + logSpace|x| + 1)) · (P|x| + 1)²`, for a halting MARM with logspace deciders,
  digits `≤ W|x|`, memory head in `[-P|x|, P|x|]`. `runFrom_count_eq`: valid along one run whose
  last tape is written only with `true` (`hwrite`), with the other heads in `[-B, B]`.
- **Intended generic form (ARM-2):** a configuration-count clock shared with the windowed runner
  (`coreCode_inj`'s windowed sub-argument exposed once; finding 2); the MARM bridge an instance of
  the bridge core.
- **Relation:** H3's configuration-count clock (B6's `WindowClock`, statement-gated) counts
  configurations of a fixed machine in a window; `runFrom_count_eq` counts a monotone memory as
  well. The two should be reconciled at the contract gate.

### H10: the configuration codec and code deciders

- **Public contracts:** `Codec/Word.lean:78` `InWin` (retires, D1), `:284` `cfgWord`, `:288`
  `cfgCode`, `:375` `cfgWord_congr`, `:391` `coreSum_eq_of_cfgWord_eq`, `:428` `codeK`, `:466`
  `cfgCode_lt`, `:477` `decodeCfg`, `:486` `decodeCfg_cfgCode`; `Codec/Langs.lean:62,68,74,82`
  `validLang`, `initLang`, `acceptLang`, `stepLang`; `Codec/Deciders.lean:193` `validLang_mem`,
  `:221` `acceptLang_mem`, `:379` `initLang_mem`; `Codec/StepDecider.lean:293` `stepLang_mem`;
  `Codec/Bridge.lean:167` `StepRel`, `:183` `mem_of_codePath`, `:235` `mem_iff_codeChain`.
- **Consumers today:** `ClassPSPACE/TQBFHard{Machine,Verifier}`, `ExpBFS/{Main,Radius}`,
  `Logspace/PathHard{,Machine,Regs,Run}`, `SavitchARM/{Correct,Reach}`, the facade.
- **Resource clauses:** codes `< 2^(codeK N · (s + logSpace|x| + 1))`; the four languages in
  `LOGSPACE`; `mem_iff_codeChain` for `s ≥ sp|x|`, chains of length `≤ N.configBound |x| s`.
- **Intended generic form (ARM-2 (b), K6):** one parameterized code language with one membership
  and decoding lemma and one decider lemma; the code bank (H13a's `decs`) public beside it.
- **Relation:** §14 counted four configuration encodings (`coreCode`, `cfgRecord`, B4a's bit rows,
  Cook–Levin's snapshots); this is a fifth, at ARM level. H4's "graph presented by rows (start,
  target, adjacency)" is exactly what the three single-code languages and `stepLang` present. RD-2's
  `ConfigCodec` (held) and B6's window rows (`Cfg.InWindow`) are the TM-level neighbours; D1 moves
  the codec onto `Cfg.InWindow`.

### H11: indexed input access

- **Public contracts:** `Logspace/InputAccess.lean:521` `inputBitLang`, `:524` `inputLenLang`,
  `:90` `vword_whole₁`, `:1034` `boundedDecode_loop` (private `arm_increments` `:621`);
  `Logspace/PreimageHost.lean:641` `compile_decides`, `:727` `mem_LOGSPACE_preimage`.
- **Consumers today:** direct importers `Logspace/{Mult,QueryReshape}` (ours, earlier),
  `Machines/{ARMLoops,ARMWidthExample,NARMKit,VWord}`; through the decider banks every received
  customer; `Codec/Engine` holds the D7 adaptations.
- **Resource clauses:** logspace deciders for the two languages; a call reads one input bit or
  compares one length.
- **Intended generic form:** the parameterized stride decoder and chain lemma (D7 with `decChain`,
  decided, payback PR); a public input bank and its oracle lemmas (ARM-2 (b), K2), with the oracle
  lemma's public form from `QueryReshape.drop_bit` (proposed payback row, `ledger-r2-tables.md` §3).
- **Relation:** H5 (input devices behind one interface) lists native, buffered, unary-marker and
  binary-position devices for Turing machines; this row is the ARM-level indexed device. The
  response's addendum 1 offers a move to `Machines/` if it becomes general.

### H12: code reachability with a growing window (`ExpBFS`)

- **Public contracts:** `ExpBFS/Radius.lean:129` `RCode`, `:186` `rset`, `:290`
  `mem_iff_of_card_eq`, `:311` `inWin_runWith_of_decides`, `:333` `card_rset_succ_of_le`;
  `ExpBFS/Main.lean:587` `NSPACE_subset_exp_dtime_of_le`; `ExpTime.lean:70`
  `NSPACE_subset_exp_dtime`, `:82` `NL_subset_P`, `:124` `polyTimeReducible_of_mem_NL`.
- **Consumers today:** `ExpTime` (the three theorems), `Logspace/ISCountGenRadius` and
  `ISCountGenCorrect` (the stop rule), the facade.
- **Resource clauses:** `NSPACE_subset_exp_dtime_of_le`: for `logSpace ≤ S`, `NSPACE S ⊆ ⋃ c,
  DTIME (2^(c (S n + 1)))`; the stop rule needs equal reachable counts at adjacent radii.
- **Intended generic form:** the pure bounded-reachability kit of §14 ("Pure-Lean kits": a
  `ReachWithin`, the midpoint lemma, pigeonhole shortening, bridges to Mathlib's
  `Digraph`/`SimpleGraph`), with `RCode`, `WalkLe` (H13c), `SavitchARM.Reach` (H13a),
  `TQBFHard.mid_iff_steps` (H13f) and ConfigGraph's reachability bridged to it; the MARM loop
  proofs factored (ARM-2 (b), K10).
- **Relation:** H4 (search over a graph presented by rows) prescribed a language-first search and
  MIG-19 the re-derivation of `NSPACE ⊆ DTIME(2^O(S))` as a program; the theorem is now proved
  here, so MIG-19 is moot (record correction, finding 8). H3's configuration-count clock: see H9.

### H13: the customer machines

| Part | Public contracts (file:line) | Consumer today | Notes |
|---|---|---|---|
| (a) Savitch | `SavitchARM/Reach.lean:59` `Reach`; `SavitchARM/Correct.lean:47` `decs`, `:51` `orcN`, `:98` `NSPACE_poly_subset_PSPACE`, `:135` `NPSPACE_subset_PSPACE` | `Savitch.lean` (`PSPACE_eq_NPSPACE`); `ISCountRegs` imports `SavitchARM/Correct` for its decider bank | polynomial `S` only; general `savitch` stays sorried. H1 named Savitch a consumer ("midpoint records as digits"); §16b item 1's stage-2 route is paused |
| (b) inductive counting | `ISCountGenMachine.lean:250` `igA`; `ISCountMath.lean:202` `GS`; `ISCountGenCorrect.lean:226` `compl_mem_NSPACE`, `:296` `compl_mem_NL` | `ImmermanSzelepcsenyi.lean` | needs only `logSpace ≤ S`; H4 named this a consumer |
| (c) PATH walk | `PathWalk.lean:63` `WalkLe`, `:119` `walkLe_short`, `:184` `reach_iff_walkLe`, `:275` `rawEdge`, `:280` `pathRawLang`; `PathWalkMachine.lean:90` `pathA`; `PathWalkProof.lean:557` `pathRawLang_mem_NL`; `Path.lean:128` `PATH_eq_pathRawLang` | `Path.lean` (`PATH_mem_NL`); `ISCountMath` (`WalkLe`), `PathHard` (`rawEdge`) | a sixth reachability notion (`WalkLe`) |
| (d) PATH hardness | `PathHard.lean:137` `Edge`, `:189` `red`; `PathHardDecide.lean:232` `pathRawLang_NLHard` | `Path.lean` (`PATH_NLComplete`) | logspace-computable bits by an ARM over H10's deciders |
| (e) TQBF walk | `TQBFARM/Correct.lean:171` `truth_mem_PSPACE`; `TQBFARM/Semantics.lean:64` `synStep`, `:73` `synOK` | `TQBF.lean` (`TQBF_mem_PSPACE`) | H1's machine form; `TQBFARM/Semantics`' twins of the `b4m*` block stay (D6 deletes the block) |
| (f) TQBF hardness | `TQBFHardSemantics.lean:263` `levelQuants`, `:282` `levelMatrix`, `:291` `Mid`, `:445` `mid_iff_steps`; `TQBFHardVerifier.lean:219` `predB`; `TQBFHardTseitin.lean:87` `toCNF_extension_iff`; `TQBFHard.lean:315` `PSPACE_polyTimeReducible_TQBF`; uses `Formulas/QBF.lean:282` `truth_exSuffix_of_pointwise` (ours) | `TQBF.lean` (`TQBF_PSPACEHard`, `TQBF_PSPACEComplete`) | H6's consumer, served instead by the uniform tableau and Tseitin; RD-2's `FormulaKit`/`ConfigCodec` held with no consumer |

- **Intended generic forms:** (a)–(e) are consumers; their reusable pieces (the decider banks, the
  loop kits, the reachability notions) move to H7, H10, H11, H12 and the pure kit under ARM-2. A
  further consumer of any part (for example a second QBF evaluator, or general `savitch` on (a))
  waits for the contract gate.

## Reconciliations of the existing rows (proposed text; the maintainer edits the design document)

- **H1, Status:** replace the language-first sentence and the pure-core sentence with: "The
  machine form exists, received: `LogProg.TQBFARM` (H13e) proves `TQBF_mem_PSPACE` by a
  depth-first walk with the assignment as a stack register (2026-10-14, accepted exception). The
  private pure core in `TQBF.lean`'s `b4m*` appendix is dead and is deleted by the payback PR (D6).
  MIG-22 is moot. The general AND/OR evaluator remains to be designed; its contract gate decides
  between this machine and §15's language." Consumers: `TQBF_mem_PSPACE` (served by H13e);
  Savitch (served by H13a for polynomial `S`); NP ⊆ PSPACE; `Games.lean`; §15 backtracking.
- **H3, Named consumers:** S1b stopped and its private block is deleted by the payback PR;
  Savitch and NL = coNL are served by H13a and H13b; B6 (the window route) remains, gated
  (`audits/b6-hosts-statements-findings.md`, CLOSED; landing PR #92 open). Add a pointer to H9's
  configuration count.
- **H4, Status:** replace "not built … Language first … (backlog MIG-19)" with: "Built at ARM level
  for `NSPACE ⊆ DTIME(2^O(S))` (H12, received 2026-10-14, accepted exception); MIG-19 is moot.
  The general search over row-presented graphs remains to be designed (H10's code languages are a
  row presentation)." Consumers: `NL ⊆ P` and `NSPACE ⊆ DTIME(2^O(S))` (served by H12);
  Immerman–Szelepcsényi (served by H13b); `PATH ∈ P`; §15 graph algorithms.
- **H6, Named consumers:** "TQBF hardness" is served by H13f's route (uniform tableau, Tseitin
  after the prefix), not by this kit; Cook–Levin deduplication and later machine-to-formula
  reductions remain. B4a's restatement (§16b item 2) has no consumer while RD-2's fills are held.
- **"Pure-Lean kits" paragraph:** add that the received code introduced `WalkLe`,
  `SavitchARM.Reach`, `ExpBFS.RCode` and `TQBFHard.Mid`/`mid_iff_steps`, each with one consumer;
  the bounded-reachability kit, when designed, bridges them.
- **"C1's hosts" paragraph:** unchanged.
