# Sub-agent B — cleanup-stage1 notes

Worktree `/home/user/s1/wt-b` (detached, tree `01cc6259480ccc9372181cd4d18d4511c87aa048`), olean tree
`/home/user/s1/oleans/b`. Only the seven files below were edited; every change is a pure insertion
(the inserted blocks are kept verbatim under `blocks/`, inserted with `tools/insert.py`, which checks
the anchor line's text before inserting). No import, no `@[simp]`, no `sorry`, every added line ≤ 100
characters (`tools/addedwidth.py`: `over100: 0`). Line numbers below are at the check tree (= base)
unless marked "head".

## Targets (20 declarations)

| Id | Full name | P | Home, anchor (base line) | Readers used | Proof source |
|---|---|---|---|---|---|
| S1-01 | `Complexity.IterateFind.host_dispatch_view` | – | `TCSlib/Complexity/Randomized/Build/IterateFindHost.lean`, after l. 388 (end of `host_halt`), before `end Complexity.IterateFind` | `ModuleHost.hostTMView_step_inl`, `Cfg.ofWords_state`, `hostCtrl_eq`, `if_pos`, `FinTM.controlAction_apply`, `moveInputPos_zero`, `Cfg.ofWords_def` | `hdisp`, `IterateFind.lean:373` (verbatim, `H` spelled out) |
| S1-02 | `Complexity.IterateFind.host_branch_view` | – | same block | as S1-01 plus `Cfg.workTapeSymbols_eq`, `Cfg.ofWords_workTapes`, `Cfg.ofWords_workTapePos`, `stateWord_eq`, `FinTM.bufferTape_eq`, `if_neg (by decide)`; closing `cases b <;> rfl` (core `ite` only) | `hbranch`, `IterateFind.lean:378` (verbatim) |
| S1-03 | `Complexity.IterateFind.host_halt_view` | – | same block | `hostTMView_step_inl`, `Cfg.ofWords_state`, `hostCtrl_eq`, `if_neg`, `controlAction_apply`, `moveInputPos_zero` | `hhalt`, `IterateFind.lean:390` (verbatim) |
| S1-16 | `Complexity.NUPPT.length_ofFn_coins` | P | `TCSlib/Complexity/Randomized/PPT.lean`, after l. 222 (`abbrev Coins`), in `namespace NUPPT` with its `variable (A : NUPPT)` | `List.length_ofFn`, `coinLen_eq` | `NMSim.length_ofFn_coins` (identical proof) |
| S1-14 | `TCSlib.Cryptography.PrivateKeyScheme.encodeList_eq_flatMap` | P | `TCSlib/Cryptography/Encryption/PrivateKey/EnsembleSecurity.lean`, after l. 141 (`encodeList_nil`) | `encodeList_nil`, `encodeList_cons`, `pairEncode_eq`; core `List.flatMap_nil`, `List.flatMap_cons`, `List.append_nil`, `List.append_assoc` | `MultiMsg.encodeList_eq_flatMap` (`MultiMsgOut.lean:65`), as an `induction` |
| S1-17 | `TCSlib.Cryptography.pkPredictor_apply` | – | `TCSlib/Cryptography/Encryption/PublicKey/Trapdoor.lean`, after l. 283 (end of `pkPredictor`); tag `[PS10, Theorem 104.4, proof]` | none (`rfl`, own definition) | – |
| S1-23 | `TCSlib.InformationTheory.FinDist.{map_uniform_equiv, sum_map, probTrue_nonneg, probTrue_le_one, uniform_prod, uniform_probTrue}` | P (all 6) | `TCSlib/InformationTheory/FinDist.lean`, after l. 198 (end of `FinDist.probTrue_eq`, the last declaration), before `end TCSlib.InformationTheory`; new header `/-! ### Pushforwards, products and acceptance of the uniform law -/` and `section Pushforward` with `variable {β : Type*} [Fintype β]` (α, `[Fintype α]` are the file's namespace-level variables there) | `FinDist.ext`, `map_apply`, `prod_apply`, `uniform_apply`, `probTrue_eq` (own file), fields `nonneg`, `sum_prob` | `Rejection.lean:45, :65, :93, :98, :134, :343` (same proofs, `FinDist.`-qualified) |
| S1-24 | `TCSlib.InformationTheory.FinDist.{expect_map, probTrue_map, map_apply_expect, map_map, map_prod_snd}` | P (all 5) | `TCSlib/InformationTheory/Samples.lean`, after l. 153 (`end FinDist`), before `end TCSlib.InformationTheory`; header `/-! ### Expectations and probabilities under a pushforward -/`, `section Pushforward` with exactly the brief's `variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]` | `FinDist.map_apply` (foreign reader), `FinDist.ext`, `FinDist.sum_map` (S1-23), `expect_eq`, `probTrue_eq_expect`, `expect_prod` (own file) | `Rejection.lean:81, :88, :104, :113, :122` |
| S1-25 | `TCSlib.InformationTheory.FinDist.{mixture, mixture_apply, mixture_isSource}` | P (all 3) | `TCSlib/InformationTheory/Entropy.lean`, after l. 213 (`end FinDist`), before `end TCSlib.InformationTheory`; header `/-! ### Mixtures of sources -/`, `section Mixture` with `variable {α : Type*} [Fintype α]` | `mixture_apply` by `rfl` (own definition); `mixture_isSource` through `FinDist.mixture_apply`, `hasMinEntropy_iff`, `isSource_iff_hasMinEntropy` | `Rejection.lean:395, :406, :413` |

Statements: copied verbatim from the brief (no statement change). S1-24's variables are the brief's
line verbatim; S1-23 and S1-25 reuse the home's existing `α` variable and add only the variables the
statements use (S1-23: `β`; S1-25: none), which elaborates to the same binders as the brief's line.
Module docstrings: one bullet per file (IterateFindHost, PPT, EnsembleSecurity, Trapdoor, FinDist,
Samples under `## Main results`; Entropy under `## Main definitions`, since it lands a definition).
Docstrings: each opens with the statement in words and the formula, then the glue note "Framework
glue, no textbook counterpart." (S1-17: the tag `[PS10, Theorem 104.4, proof]`). No proof has 15 or
more lines (longest: `FinDist.map_uniform_equiv`, 14; `FinDist.sum_map`, `mixture_isSource`, 11), so
no sketch is required.

Rule 10 (self-review; the canonical seals are the lead's): no foreign TCSlib definition is passed to
`simp`/`rw`/`unfold` or read by `rfl`/`show`/`decide`. Definitional steps: S1-17 `rfl` (own
`pkPredictor`), S1-25 `mixture_apply` `rfl` (own `mixture`); S1-02 `cases b <;> rfl` and
`if_neg (by decide)` on `Fin 3` literals (core only) exactly as in E1, which pass the seals there.
`simpa using hw` in S1-02 is E1's.

## Reuse searches (check 12), copy lists, further copies

Searches: `grep -rn` over `TCSlib/` and `audits/` of the worktree (= check tree) for each short name,
for the conclusion's shape, and for the proof's characteristic rewrite chain; `grep -rn` of the
short names over Mathlib (`/home/user/s1/tcslib/.lake/packages/mathlib/Mathlib`) and the toolchain
sources. No `exact?` probe was run (each target is about a TCSlib definition, so core/Mathlib cannot
hold an equal form; the name/shape searches found no Mathlib or core hit).

**S1-01..03** (`host_*_view`). Short names fresh (no hit in TCSlib, audits, Mathlib). `hostTMView`
occurs only in `ModuleHost.lean`, `IterateFindHost.lean`, `IterateFind.lean`; the only other
typed-view readers are `ModuleHost.host_call_view`, `host_clean_view`, `hostTMView_step_inl`,
`IterateFindHost.copy_clean_view` (different contents). Copy list **confirmed**:
`IterateFind.lean:373` (`hdisp`), `:378` (`hbranch`), `:390` (`hhalt`); the originals
`IterateFindHost.lean:352`, `:364`, `:380` (base lines; `theorem` lines). Uses of the `have`s inside
E1: `IterateFind.lean:464` (`hdisp`), `:469` (`hbranch`), `:493` (`hhalt`).
No further copy.

**S1-16** (`NUPPT.length_ofFn_coins`, P). Equal-form copies **confirmed**:
`Encryption/PublicKey/NonMalleability/Simulation/Rounds.lean:41` (`NMSim.length_ofFn_coins`),
`SecureComputation/ObliviousTransfer/Simulators.lean:210` (`OT.length_ofFn_coins`); both have
`(A : NUPPT)` explicit, as the promoted form (`variable (A : NUPPT)`), so Stage 2 can re-point
`length_ofFn_coins samp n ρ` call sites to `NUPPT.length_ofFn_coins samp n ρ` unchanged.
Further inline copies (same `have` with the same two-step proof `rw [List.length_ofFn,
NUPPT.coinLen_eq]`), for the Stage 2 table: `Asymptotic/CollectionsHelpers.lean:112`,
`Hashing/FromDiscreteLog.lean:97`, `:134`; inline in rewrite arguments:
`Asymptotic/Collections.lean:796`, `:804`. Longer chains that begin with the same two rewrites and
continue (not instances on their own): `Authentication/Signatures/Lamport.lean:700`,
`Encryption/PrivateKey/EncryptThenTag.lean:359`, `:363`, `:375`, `:380`,
`SecureComputation/SpecialEncryptionSecurity.lean:100`, `:103`; the `Strategy.coinLen_eq` chains in
`SecureComputation/ComposeSecurity/*` and `ObliviousTransfer/Efficiency.lean:485`, `:488` are about
`Strategy` coins (a different definition), not instances.

**S1-14** (`PrivateKeyScheme.encodeList_eq_flatMap`, P). Copy list **confirmed**:
`Asymptotic/BlockEncryptor.lean:60` (public `TCSlib.Cryptography.encodeList_eq_flatMap`),
`Encryption/PrivateKey/FromPRF/MultiMsgOut.lean:65` (public `MultiMsg.encodeList_eq_flatMap`),
`Encryption/PrivateKey/FromPRF.lean:251` (private). **E-DUP note:** the BlockEncryptor copy is
already public in an *equal* form (same statement, root `TCSlib.Cryptography`). I added the target
anyway because the brief/ledger (DL-46) designates this home beside the definition and lists that
copy for Stage 2; flagged for the lead to confirm (CS1-W candidate if not intended). Consumers of
the public BlockEncryptor form (Stage 2 re-points them if that copy is removed):
`Authentication/Signatures/Lamport/MachineSpec.lean:49`, `Authentication/Signatures/Lamport.lean:582`,
`Encryption/PublicKey/HybridMachine.lean:216`, `:217`,
`SecureComputation/Yao/HybridProof/SliceReconstruction.lean:274`. Near relative (not an instance;
different, generic `encodeList`; forbidden directory): `TCSlib/Complexity/CircuitComplexity/
UniformTableauEmitter.lean:256`.

**S1-17** (`pkPredictor_apply`, fresh). No reader of `pkPredictor` exists; `pkPredictor` is used
only in `Trapdoor.lean`. Near relative (not an instance): `owpPredictor_apply`,
`Pseudorandom/GeneratorFromPermutation.lean:96` (the predictor with the pass-through component).
Stage 2 lines **confirmed**: `SecureComputation/ObliviousTransfer/ViewB.lean:71`, `:101`;
`exists_pkPredictor` at `Encryption/PublicKey/Trapdoor.lean:337` (base; head 347);
`ObliviousTransfer/Simulators.lean:52`, `:57` (`splitLen`, `splitLen_symm_ofFn`);
`Asymptotic/EnsemblesLemmas.lean:141`, `:145` (`coinsEquiv`, `ofFn_coinsEquiv`).

**S1-23..25** (`FinDist`, all P). Copy list **confirmed**, all in
`Cryptography/Randomness/Extraction/Rejection.lean`: `:45` map_uniform_equiv, `:65` sum_map, `:81`
expect_map, `:88` probTrue_map, `:93` probTrue_nonneg, `:98` probTrue_le_one, `:104`
map_apply_expect, `:113` map_map, `:122` map_prod_snd, `:134` uniform_prod, `:343`
uniform_probTrue, `:395` mixture, `:406` mixture_apply, `:413` mixture_isSource. No other TCSlib
file declares these short names for `FinDist` (`Games/Probability.lean:134` `expect_map` is the
`ProbComp` one). Consumers of the Rejection copies (Stage 2): `Cryptography/Randomness/
Extraction.lean:168`, `:221`, `:247`, `:248`, `:325`, `:328`; `Cryptography/Randomness/Learning/
Law.lean:81`, `:82` (and docstrings `:22`, `:23`, `:73`, `:74`). Further near-copies: the three
`DyadicUniform` uniformity facts `Cryptography/Encoding/DyadicUniform.lean:83`
(`bitsToResidue_uniform`), `:148` (`bitsToVector_uniform`), `:216` (`bitsToMatrix_uniform`) are
`map_uniform_equiv` at `Equiv.ofBijective _ hb` (re-provable from it; each re-proves the fibre count
by hand); `LWE/Sampling.lean:68` (`sampleFromBits_law`) is a near relative (a pushforward of a
uniform law through a product of such equivalences).

## Name and shadow checks (my targets)
- New full names: none exists in `TCSlib/` or `audits/` at the check tree.
- Short names that exist elsewhere, all marked P by the brief and declared `protected`:
  `length_ofFn_coins` (NMSim, OT), `encodeList_eq_flatMap` (BlockEncryptor, MultiMsg, FromPRF
  private, CircuitComplexity), the 14 `FinDist` names (Rejection; `sum_map`, `map_map`,
  `expect_map` also in Mathlib/Games). No unmarked clash: `host_dispatch_view`,
  `host_branch_view`, `host_halt_view`, `pkPredictor_apply` are fresh.
- Shadow scan: modules that open `FinDist` (`InformationTheory/LeftoverHash.lean:45`,
  `Extractors.lean:53`, `StatisticalDistance.lean:40`) use none of the 14 short names unqualified;
  `ComposeSecurity/Reductions.lean:35` opens `Complexity.NUPPT` and does not use
  `length_ofFn_coins`; every selective `open PrivateKeyScheme (…)` names only `encodeList`,
  `encodeList_nil`, `encodeList_cons`. With `protected`, resolution is unchanged in any case.

## wtcheck runs (all with `/home/user/s1/tools/wtcheck.py`, one at a time; raw logs in `logs/`)

| Run | Target | Result |
|---|---|---|
| run01 | `TCSlib/Complexity/Randomized/PPT` | stopped while waiting for the lead bootstrap (no Lean process run); superseded by run05 |
| (first run05 attempt) | `PPT` | stopped while waiting for the bootstrap (no Lean run), relaunched detached as run05 |
| run02 | `TCSlib/InformationTheory/FinDist` | OK: rc 0, 0 errors, 0 sorry, empty log |
| run03 | `TCSlib/InformationTheory/Samples` | OK: rc 0, 0 errors, 0 sorry, empty log |
| run04 | `TCSlib/InformationTheory/Entropy` | OK: rc 0, 0 errors, 0 sorry, empty log |
| run05 | `TCSlib/Complexity/Randomized/PPT` | OK: rc 0, 0 errors, 0 sorry, empty log |
| run06 | `TCSlib/Complexity/Randomized/Build/IterateFindHost` | OK: rc 0, 0 errors, 0 sorry, empty log |
| run07 | `TCSlib/Cryptography/Encryption/PrivateKey/EnsembleSecurity` | OK; rebuilt 8 modules (incl. downstream `IterateFind`, `Closure`, `Repetition`, `Adversary`, `Scheme`), all rc 0, 0 errors; target log empty |
| run08 | `TCSlib/Cryptography/Encryption/PublicKey/Trapdoor` | OK; rebuilt 38 modules, all rc 0, 0 errors; one `sorry` warning in the unchanged `Complexity/Randomized/NonUniform.lean:157` (pre-existing, not ours); target log empty |
| run09 | `Probes/B_StmtAxioms` (StmtDump + `#print axioms` of the 20 constants) | OK: rc 0; axioms ⊆ {propext, Classical.choice, Quot.sound} for all 20 (`pkPredictor_apply`: none; `encodeList_eq_flatMap`: propext, Quot.sound); no `sorryAx` |

Other warnings in the logs are all in unchanged upstream modules (unused simp arguments, unused
section variables) and were rebuilt only because `PPT`/`FinDist` changed upstream.
Probe source and output: `probes/B_StmtAxioms.lean`, `probes/B_StmtAxioms.out.log` (the probe file
is also at `/home/user/s1/wt-b/Probes/B_StmtAxioms.lean`, untracked, not in the patch).

## Issues / questions for the lead
1. **S1-14 E-DUP check.** `TCSlib.Cryptography.encodeList_eq_flatMap` (`Asymptotic/BlockEncryptor.lean:60`)
   is already public with the *identical* statement. I added `PrivateKeyScheme.encodeList_eq_flatMap`
   as the brief directs (the ledger's home beside the definition, BlockEncryptor listed as a Stage 2
   copy), but under the literal E-DUP rule this is an equal-form public duplicate; please confirm it
   is intended (the brief's copy list suggests yes).
2. Seals were not run by me (lead's canonical seals). Self-review found no Rule-10 reading of a
   foreign definition; S1-01..03 use E1's proofs verbatim (which pass the seals in `IterateFind`).
3. Copy lists all confirmed at the stated lines; further copies/near relatives listed above
   (S1-16 inline `have`s; DyadicUniform for `map_uniform_equiv`).

Final patch: `B.patch` (= `B-statements.patch`; 7 files, 283 insertions, 0 deletions).
