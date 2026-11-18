# Efficiency audit r1: definitions, security reductions, axioms

Records branch `cryptography/pass-shelat-ch2-4` at tip `32a40963de5ed5f7abb472cd9d432c6561c2e833`
(2026-11-18). While the audit ran, the records tip moved to `4f3ac57f0d0ddad8c57bcaae27a28609f8c07593`, with
Markdown-only commits: `git diff 32a40963 4f3ac57f -- TCSlib TCSlib.lean audits` is empty, so every finding holds at the
new tip. This audit was requested under standing rule 15 (Seyoon, 2026-11-18;
`briefs/pass-shelat-ch5-8/MAINTAINER-HANDOFF.md` §2). It builds on `inventory-r1.md` (116 honest-algorithm
rows), which it does not repeat.

- **Uncommitted record.**
- **Method.**
  - Parts 1 and 2 are static: file reads, `git show` of the PR #377 head, `python3 -I`.
  - Part 3 is one Lean process at a time, run on a `cp -al` copy of olean snapshot #10 (§4).
- **Paths.** All paths are relative to `TCSlib/Cryptography/` unless they start with `TCSlib/`, `briefs/` or a
  plan file name.

## 0. Rule 15 and the classes used

**What rule 15 requires.**
1. Honest algorithms are proved efficient in uniform form: `PolyTimeComputable`, or `∃ A, A.Uniform ∧ A.Computes f`.
2. Every security reduction is a proved non-uniform PPT (`NUPPT`) machine.
3. Every primitive's definition carries its honest algorithms' efficiency, so no instance exists without the proof.
   A "raw" algorithm bundle may come first, but the primitive is inhabited only once efficiency is proved.

**Definition classes (Part 1).**

| Class | Meaning |
|---|---|
| **E** | Efficiency is in the definition, in uniform form. `E·s` means it is a field of the structure. `E·p` means it is a field or conjunct of the *named primitive predicate* over a raw bundle, for example `StrongOneWay.easy` over `FunFamily`, or `PRG.Secure = Easy ∧ …` over `PRG`. |
| **E-nu** | Efficiency is in the definition, but in non-uniform or bare `∃ A : NUPPT, A.Computes f` form. This violates rule 15. |
| **N** | The definition carries no efficiency. |

**Reduction classes (Part 2).**

| Class | Meaning |
|---|---|
| **M** | A proved `NUPPT` reduction: both the assumption and the conclusion quantify over `NUPPT`, and the proof closes with no `sorryAx` (§4). |
| **MH** | As M, but conditional on named efficiency hypotheses about *honest* operations: `Candidates.ArithmeticFP`, `BilinearGen.Ops`, `LevinNPHard`. |
| **F** | Function-level only: a bound for every Lean function `D`, at fixed parameters, with no machine and no asymptotic statement. |
| **G** | A gap. Either the chain stops at an F lemma, or a hypothesis *is* the reduction's efficiency, or no security statement exists. |

---

## 1. Summary

**Counts.**

| Part | Total | Breakdown |
|---|---|---|
| Definitions (§2) | 45 rows | **E 27** (E·s 18, E·p 9) · **E-nu 0** · **N 18** (1 of them partial: `BilinearGen`) |
| Reductions (§3) | 52 rows | **M 34** · **MH 10** · **F 4** (each also G at the chain level) · **G 4**: 2 smuggled-hypothesis rows on PR #377, 1 absent statement (ABO), 1 by design (pure-FHE circular security) |
| Axioms (§4) | 16,913 crypto constants in 486 modules (every non-facade crypto module but the orphan `RSA.lean`) | **0 reach `sorryAx`**. `ClassP/BinaryArith`: 731 constants, 0 reach `sorryAx`. 96 `#print axioms` targets: 94 standard, plus the 2 controls, which correctly show `sorryAx`. |

**Worst gaps first.**

1. **No lattice construction reaches an `NUPPT` security statement or a primitive interface.** This confirms inventory
   r1 §3, with refinements.
   - **Function-level only (F):** Regev symmetric, Regev PKE, phase-5 GSW and the lossy TDF hybrids.
     - Each is a per-`Parameters` bound for an arbitrary Lean function `D : … → ρ → Bool`.
     - There is no asymptotic statement and no machine.
   - **No security statement at all:** the all-but-one TDF has none, and nothing defines lossy or ABO TDFs as
     primitives.
   - **The two exceptions are M, but in raw form only:**
     - the LWE PRG (`pseudorandom_under_DLWE`, identity reduction);
     - the SIS hash (`negligible_collisions_of_SIS`, a real machine built by `exists_compParam`).
     - Neither conclusion is a primitive's predicate: the LWE PRG is not a `PRG` and the SIS hash is not a `CRH`.
2. **GSW 6b on PR #377 states the reduction's efficiency as a hypothesis.** The asymptotic theorems A1
   (`indCPA_of_dlweAssumption`) and A3 (`leveledINDCPA_of_dlweAssumption`) take `ReductionEfficient F` or
   `LeveledReductionEfficient F L`.
   - These hypotheses say "for every `NUPPT` `D` there is an `NUPPT` `D'` dominating the reduction". That is exactly
     the reduction-efficiency obligation of rule 15. They are class G.
   - The ruling behind them, P6-Q10, predates rule 15.
   - A1 and A3 are also `sorry` on the PR (proved-modulo).
   - **The hypotheses are dischargeable on TM tooling now.** Each reduction uses only binary coins and mod-`q`
     arithmetic, and the parameters can be advice, since reductions may be non-uniform (§3.3).
3. **The lattice definitions carry no efficiency (N).**
   - Affected: `LWE.Family`, `LWE.Noise` and `SIS.Family`.
   - No lattice scheme is an instance of `PrivateKeyScheme`, `BitPublicKeyScheme`, `PRG` or `CRH`.
4. **`IBEScheme` carries no efficiency (N).** This is the Q5 deferral, which predates rule 15.
   - BB1's honest algorithms are therefore unproved.
   - BB1 security is MH, on `ArithmeticFP` and `G.Ops`.
5. **`BilinearGen` is only partly E.**
   - Its generator is E·s.
   - Its group operations sit in a separate structure, `Ops`, which consumers take as a hypothesis (`O : G.Ops`).
6. **`ArithmeticFP` conditions every number-theoretic result.**
   - It conditions 25 honest-algorithm entries and 10 reduction rows (MH).
   - 7 of its 9 fields are cheap on `ClassP/BinaryArith`. That library is now confirmed `sorryAx`-free (§4), and the
     confirmation settles inventory caveat 2.
   - `xgcd` is moderate. `prime` is blocked: the library has no deterministic primality test.
7. **`SecretSharing.Scheme`, `BGW.Resharer` and `MultiEnc` are N.** The first two are information-theoretic. `MultiEnc`
   reaches efficiency through Yao's `PolyTime`.
8. **ZK for NP is MH on `LevinNPHard`.** This hypothesis is about the honest instance and witness maps.

**What is clean.**
- **No E-nu anywhere.** Every honest `NUPPT` field is paired with `*_uniform`.
- **The only non-uniform `NUPPT` fields are adversarial.** These are `MsgSampler.samp`
  (`Encryption/PublicKey/NonMalleability/Simulation.lean:120`) and the private `ShiftedMachine.machine`
  (`Asymptotic/CollectionShift.lean:41`), whose uniformity is preserved by its `uniform` field.
- **The generic [PS10] ch. 2–8 chain is M throughout,** and no crypto constant reaches `sorryAx`. So the inventory's 56
  **P** rows are unconditional, relative to their interface fields.

---

## 2. Definitions (Part 1)

The retrofit column names the instances and consumers that would change.

### 2.1 E: efficiency in the definition

| # | Primitive | Definition (file:line) | Class | Form | Retrofit needed |
|---|---|---|---|---|---|
| D1 | OWF families (strong, weak, worst-case, literal) | raw `FunFamily` `Asymptotic/OneWay.lean:94`; predicates `StrongOneWay` `:130` (`easy` `:132`), `WeakOneWay` `:142` (`:144`), `WorstCaseOneWay` `:165` (`:167`), `WorstCaseOneWayLit` `:191` (`:193`) | E·p | `FunFamily.Easy` `:109`: `∃ F, PolyTimeComputable F ∧ …` | none. Only if Q1 = B: 49 files use `FunFamily`. |
| D2 | OWP | raw `PermFamily` `Asymptotic/OneWay.lean:932`; `OneWayPermutation` `:944` (= `StrongOneWay`) | E·p | as D1 | none (Q1) |
| D3 | Hard-core predicate (function, permutation) | `HardCore` `Asymptotic/HardCore/Functions.lean:82` (`HardCore.easy` `:100`); `PermFamily.HardCore` `:114` (`.easy` `:142`) | E·p | `PolyTimeComputable` | none |
| D4 | Collection of OWFs | `Collection` `Asymptotic/Collections.lean:128` | E·s | `gen`/`sample : NUPPT` + `*_uniform` `:151–157`; `eval_poly` `:161` | none |
| D5 | One-way collection; hard-core for a collection | `Collection.OneWay` `:233`; `Collection.HardCore` (evaluator `:248`) | E·s | inherits D4; `PolyTimeComputable` evaluator | none |
| D6 | Permutation collection, TDP collection | `PermCollection` `:338`; `TrapdoorCollection` `:374` | E·s | `inv : NUPPT`, `inv_uniform` `:376–378` | none |
| D7 | Hard-core evaluator | `Collection.PredEvaluator` `Encryption/PublicKey/Trapdoor.lean:66` | E·s | `poly` `:70` | none |
| D8 | PRG | raw `PRG` `Pseudorandom/Generators/Asymptotic/Defs.lean:132`; `PRG.Secure` `:170` | E·p | `PRG.Easy` `:150` (`PolyTimeComputable`) | none. Only if Q1 = B: 27 files. |
| D9 | Length-doubling PRG | `DoublingPRG` `Pseudorandom/Generators/Asymptotic/Stretch.lean:335` | E·s | `PolyTimeComputable` evaluator `:336–338` | none |
| D10 | PRF | `PRF` (a `Prop` structure) `Pseudorandom/Functions/Asymptotic/Defs.lean:444` | E·s | `easy` `:446` | none |
| D11 | Private-key scheme; fixed-length scheme | `PrivateKeyScheme` `Encryption/PrivateKey/Scheme.lean:50`; `FixedLengthScheme` `Encryption/PrivateKey/OracleSecurity.lean:87` | E·s | `gen/enc/dec : NUPPT` + `*_uniform` `:52–62` | none |
| D12 | Public-key schemes (general, single-bit) | `PublicKeyScheme` `Encryption/PublicKey/Scheme.lean:43`; `BitPublicKeyScheme` `:65` | E·s | `gen/enc` uniform, `dec_poly` `:45–55`, `:67–77` | none |
| D13 | Fixed-length PKE | `FixedLengthPKScheme` `Encryption/PublicKey/OracleSecurity.lean:229` | E·s | `:235–245` | none |
| D14 | Group PKE (El Gamal shape) | `GroupPKScheme` `Encryption/PublicKey/ElGamal.lean:108` | E·s | `:110–120` | none |
| D15 | MAC | `MAC` `Authentication/MAC/Defs.lean:47` | E·s | `gen/tag` uniform, `ver_poly` `:53–63` | none |
| D16 | Signature | `SignatureScheme` `Authentication/Signatures/Defs.lean:60` | E·s | `:66–76` | none |
| D17 | CRH | `CRH` `Hashing/CollisionResistant.lean:56` | E·s | `gen` `:62`, `gen_uniform` `:70`, `eval_poly` `:72` | none |
| D18 | Commitment | `Commitment` `ZeroKnowledge/Commitment.lean:112` | E·s | `easy : PolyTimeComputable Com` `:114` | none |
| D19 | ZK protocol structures | raw `Strategy` `ZeroKnowledge/Interaction.lean:117`, `Protocol` `:376`; predicates `InteractiveProof` `ZeroKnowledge/InteractiveProofs.lean:126` (`efficientV` `:128`), `InteractiveProofErr` `:149`, `EfficientProverProof` `:347` (`efficientP` `:350`), `EfficientProverProofErr` `:362`; `HVZK`/`ZK` `ZeroKnowledge/Defs.lean:137`/`:157` (simulator `S.Uniform`) | E·p | `Strategy.Efficient` `ZeroKnowledge/Interaction.lean:223` = `∃ A : NUPPT, A.Uniform ∧ …` | none |
| D20 | Levin reduction; NP relation | `LevinReduction` `ZeroKnowledge/NP.lean:134` (`f_poly`, `w_poly` `:137`, `:139`); `WitnessRelation` `ZeroKnowledge/InteractiveProofs.lean:256` (`decidable`) | E·s | `PolyTimeComputable` | none |
| D21 | 2PC functionality and HBC security (OT, Yao) | raw `Functionality` `SecureComputation/Defs.lean:74`; `Functionality.PolyTime` `:152`; `HBCSecure` `:176` | E·p | `Strategy.Efficient` for both parties | none |
| D22 | Hybrid-model protocol | `HybridProtocol` `SecureComputation/Hybrid.lean:74`; `PolyTime` `:206`; `HBCSecure` `:259` | E·p | as D21, plus a `PolyTimeComputable` call map | none |
| D23 | Yao circuit family | `YaoCircuit` `SecureComputation/Yao.lean:179` | E·s | `uniform` `:201` (`PolyTimeComputable` description of `C_n`) | none |
| D24 | DL group generators (`SafePrimeGen`, `FullGroupGen`) | `ExpGroupGen` `Candidates/DiscreteLog.lean:326`; `SafePrimeGen` `:1103`; `FullGroupGen` `Candidates/DiscreteLogHardcore.lean:810` | E·s | `gen : NUPPT`, `gen_uniform` `:328–330`. These are hypothesis objects with no instance (Q6). | none |
| D25 | Efficiently samplable ensemble | `Ensemble.Samplable` `Asymptotic/Ensembles.lean:169` | E·p | `PolyTimeComputable` sampler | none |
| D26 | OT / special encryption (Yao) | OT is D21 at `otFunctionality`. Special encryption is a `PrivateKeyScheme` (`SecureComputation/SpecialEncryptionSecurity.lean:89`). | E (via D21/D11) | — | none |
| D27 | `ArithmeticFP` (hypothesis bundle, not a primitive) | `Candidates/Arithmetic.lean:314` | E·s (fields) | 9 `PolyTimeComputable` fields `:316–333` | discharge (§6, EF-H1/H2) |

### 2.2 N: no efficiency in the definition

| # | Primitive | Definition (file:line) | Class | Evidence | Retrofit touches |
|---|---|---|---|---|---|
| N1 | IBE | `IBEScheme` `AdvancedEncryption/IdentityBased/Defs.lean:106` | N | `ProbComp` algorithms; deviation `:98–105` (Q5) | instance `bb1Scheme` (`AdvancedEncryption/IdentityBased/BonehBoyen.lean:339`); 10 `IdentityBased/*` files; `Defs.lean` is in S2-A (J0) |
| N2 | Bilinear generator | `BilinearGen` `Pairing/Group.lean:283` (gen E·s `:285–287`); operations `Ops` `Pairing/Operations.lean:68` (fields `:82–92`) are **not** a field | N (partial) | `O : G.Ops` is a hypothesis of `bb1_sidSecure` (`AdvancedEncryption/IdentityBased/BonehBoyenSecurity.lean:177`) and of the BB1 machine files | 17 files (`Pairing/*`, `KeyExchange/Joux`, `IdentityBased/*`); `Pairing/Assumptions.lean` is J0 |
| N3 | Bilinear group description | `BilinearGroup` `Pairing/Group.lean:96` | N | typed group | covered by N2 |
| N4 | LWE family | `LWE.Family` `LWE/Assumption.lean:65` | N | deviation `:47–51`, `:62–64` | on the branch: `LWE/SampleSchedules`, `Pseudorandom/Generators/LWE/Basic`, `TrapdoorFunctions/Lossy/Experiments`; on #377: `GSW/Asymptotic`, `LWE.lean` (Q3) |
| N5 | LWE noise | `LWE.Noise` `LWE/Noise.lean:41` | N | "No efficient sampler is asserted" `:31`, `:40` | 15 files: `LWE/*`, Regev ×4, GSW ×4, the LWE PRG, lossy |
| N6 | SIS family | `SIS.Family` `SIS/Assumption.lean:66` | N | `:47–50`, `:64–65` | `Hashing/SIS.lean`, `Hashing/SIS/Profiles`, `Hashing/SIS/Asymptotic` |
| N7 | GSW (public-key, symmetric, leveled, bootstrapped) | `Parameters` `AdvancedEncryption/Homomorphic/GSW/Gadget.lean:59`; `encrypt` `GSW/Scheme.lean:102`, `decrypt` `:141`; `GSW/Eval.lean:122`; `GSW/Symmetric.lean:61`; 6b `Leveled`, `Bootstrap` (#377) | N | typed functions; "bridge is a separate unit" `GSW/Security.lean:47–50` | new `BitPublicKeyScheme` instance (EF-H8) |
| N8 | Regev symmetric | `Encryption/Symmetric/Regev/Basic.lean:58`, `:69` | N | `:23–24` | new `PrivateKeyScheme` instance |
| N9 | Regev PKE | `Encryption/PublicKey/Regev/Basic.lean:45`, `:66`, `:89` | N | `:34–35` | new `BitPublicKeyScheme` instance |
| N10 | Lossy TDF | `conceal` `TrapdoorFunctions/Lossy/Matrix.lean:46`, `evaluate` `:60`, `injectiveKey` `:92`, `recover` `:110` | N | **no LTDF interface exists**; `:38–39` | new interface (EF-D4) |
| N11 | All-but-one TDF | `allButOneKey` `TrapdoorFunctions/AllButOne/Basic.lean:59`, `evaluateBranch` `:80` | N | **no interface**; facade `TrapdoorFunctions/AllButOne.lean:20–22` | new interface (EF-D4) |
| N12 | LWE PRG | `generate` `Pseudorandom/Generators/LWE/Basic.lean:52`; `Bits.lean:44`; `Flat.lean:133` | N | not a `PRG` instance; `Basic.lean:84` | new `PRG` instance (dyadic `Flat`) |
| N13 | SIS hash | `hashPoly` `Hashing/SIS/Implementation.lean:45` (evaluator P, `:89`) | N (no `CRH` instance) | `Hashing/SIS.lean:32–33` | new `CRH` instance (EF-H4) |
| N14 | Joux key exchange | `jouxMsg` `KeyExchange/Joux.lean:74`, `jouxKey` `:82` | N | no key-exchange interface | interface (optional) + honest machines |
| N15 | Secret sharing | `SecretSharing.Scheme` `SecretSharing/Defs.lean:86` | N | deviation `:82–84` (information-theoretic) | `SecretSharing/Shamir.lean:101`; `MPC/BGW` (Q7) |
| N16 | BGW resharing | `Resharer` `MPC/BGW/Protocol.lean:67`; `bgwEval` `:101` | N | share-level functions | (Q7) |
| N17 | Garbling encryption | `MultiEnc` `SecureComputation/Garbling.lean:139` | N | its efficiency reaches Yao through `specialScheme` (D26) and `yaoHybrid_polyTime` | none needed (24 files; no standalone consumer) |
| N18 | Schnorr identification | `SchnorrProtocol.lean:42–61` | N | algebraic over `ZMod q` | port to `Protocol` (low priority) |

**Not counted.**
- **The Garg concrete layer** is N by design: `OneWayFunctions/`, `HardcoreBit/`, `Pseudorandom/Generators.lean`,
  `Pseudorandom/Functions/{Defs,GGM}.lean`, `Pseudorandom/GeneratorFromPermutation.lean`,
  `Pseudorandom/NextBit/Concrete.lean`. Its asymptotic counterparts are E.
- **The legacy `RSA.lean` (`TimeM`)** is an orphan, with no importer.
- **The DDH, BDH and DBDH assumption objects** are assumptions, not primitives. Their generators are D24 and N2.

---

## 3. Reductions (Part 2)

### 3.1 Assumption predicates and their quantifiers

Every assumption predicate on the branch quantifies over `NUPPT`:

| Predicate | Location |
|---|---|
| `FactoringAssumption` | `Candidates/Factoring.lean:309` |
| `RSAAssumption` | `Candidates/RSA.lean:125` |
| `BlumFactoringAssumption` | `Candidates/Rabin.lean:118` |
| `DLHard` / `DLAssumption` | `Candidates/DiscreteLog.lean:407`, `:1113` |
| `FullDLAssumption` | `Candidates/DiscreteLogHardcore.lean:820` |
| `DDHAssumption` (`Ensemble.Indist`, `Asymptotic/Ensembles.lean:182`) | `Candidates/DDH.lean:357` |
| `DBDHAssumption` / `BDHAssumption` | `Pairing/Assumptions.lean:266`, `:307` |
| `DLWEAssumption` | `LWE/Assumption.lean:136` |
| `SISAssumption` | `SIS/Assumption.lean:155` |
| generic: `StrongOneWay.hard`, `Collection.OneWay.hard`, `PRG.Secure`, `PRF.pseudorandom`, `Commitment.hides`, `EnhancedHardCore` | `SecureComputation/ObliviousTransfer.lean:271` (for `EnhancedHardCore`) |
| `WeakCircularSecureFamily` (#377) | `GSW/Asymptotic.lean:175` |

Every conclusion predicate also quantifies over `NUPPT` adversaries:
- **Ensemble and indistinguishability:** `Ensemble.Indist`.
- **Schemes:** `SingleBitSecure`, `INDSecure`, `NMSecure`, `SIDSecure` (`AdvancedEncryption/IdentityBased/Defs.lean:550`),
  `OneTimeSecure`, `CRH.CollisionResistant`, `MAC.Secure`.
- **Interactive protocols:** `HBCSecure`, and `ZK`/`HVZK` (simulator uniform).
- **Raw lattice forms:** `JouxKeyIndist` and the raw `collisionAt`.

The lattice F rows are the exception: they quantify over Lean functions, not machines.

### 3.2 Table

In the "How" column, "standard" means the theorem's proof builds the reduction machine. It is proved: `sorryAx`-free in
§4.

| # | Theorem (file:line) | Assumption (`NUPPT`?) | Conclusion (`NUPPT`?) | How | Notes |
|---|---|---|---|---|---|
| **[PS10] ch. 2** | | | | | |
| R1 | `weak_to_strong` `Asymptotic/OneWay.lean:671` | `WeakOneWay` (yes) | `StrongOneWay` (yes) | **M** | |
| R2 | `strong_prod_two` `Asymptotic/OneWay.lean:752` | `StrongOneWay` (yes) | yes | **M** | |
| R3 | `Collection.OneWay.exists_strongOneWay` `Asymptotic/Collections.lean:1116`; `StrongOneWay.exists_collection_oneWay` `:617` | yes | yes | **M** | |
| R4 | `theorem_63_1` `Asymptotic/Universal.lean:949`; `lemma_64_3` `:503`; `PadQuad.exists_family` `Asymptotic/UniversalPadding.lean:493` | `∃ OWF` (yes) | yes | **M** | |
| R5 | `goldreich_levin` `Asymptotic/HardCore/Functions.lean:477`; `goldreich_levin_coll` `Asymptotic/HardCoreCollection.lean:374`; `exists_owp_hardCore` `Asymptotic/HardCorePermutation/GoldreichLevin.lean:848` | yes | yes | **M** | |
| **Number-theoretic candidates** | | | | | |
| R6 | `fmult_weakOneWay` `Candidates/Factoring.lean:603`; `factoringCollection_oneWay` `:1806` | `FactoringAssumption` (yes) | yes | **MH** | AFP, including `prime` |
| R7 | `rsaTrapdoor_oneWay` `Candidates/RSA.lean:2044` (`rsaCollection_oneWay` `:2029`) | `RSAAssumption` (yes) | yes | **MH** | AFP, including `prime` and `xgcd` |
| R8 | `rabinCollection_oneWay` `Candidates/Rabin.lean:2243`; `rabinBlumTrapdoor_oneWay` `:3271` | `FactoringAssumption` (yes) | yes | **MH** | AFP; `BlumDensity` is not an efficiency hypothesis (rule 14) |
| R9 | `dlCollection_oneWay` `Candidates/DiscreteLog.lean:1208` (`expCollection_oneWay` `:1076`) | `DLAssumption` (yes) | yes | **MH** | AFP (no `prime`); the generator is a hypothesis object |
| R10 | `fullDLCollection_hardCore` `Candidates/DiscreteLogHardcore.lean:2994` (`fullDLCollection_oneWay` `:918`) | `FullDLAssumption` (yes) | yes | **MH** | AFP, including `xgcd` at a prime modulus |
| **[PS10] ch. 3** | | | | | |
| R11 | `exists_securePRG_of_owp` `Pseudorandom/Generators/Asymptotic/FromPermutation.lean:283` (`owp_hardcore_prg` `:188`, `cor_81_7` `:267`) | yes | `PRG.Secure` (yes) | **M** | |
| R12 | `prg_expand` `Pseudorandom/Generators/Asymptotic/Stretch.lean:209`; `PRG.Secure.truncate` `:397`, `.doubling` `:419` | yes | yes | **M** | |
| R13 | `Ensemble.Pseudorandom.nextBitUnpredictable` `Pseudorandom/NextBit.lean:401` | yes | yes | **M** | |
| R14 | `ggmPRF_prf` `Pseudorandom/Functions/Asymptotic/GGM.lean:321`; `exists_prf_of_exists_prg` `:383` | `DoublingPRG` / `PRG.Secure` (yes) | `PRF` (yes) | **M** | |
| **[PS10] ch. 4** | | | | | |
| R15 | `owp_commitment` `ZeroKnowledge/Commitment.lean:898`; `exists_commitment_of_owp` `:918` | OWP + hard-core (yes) | `Commitment` (yes) | **M** | |
| R16 | `col_zeroKnowledgeProof` `ZeroKnowledge/ThreeColoring/Simulator.lean:1656` (`col_zk` `:1638`) | `Commitment` (yes) | `ZK` (yes; uniform simulator) | **M** | |
| R17 | `zk_proof_of_levinReduction` `ZeroKnowledge/NP.lean:573` | `Commitment` (yes) | yes | **M** | given one Levin reduction |
| R18 | `zk_proof_of_mem_NP_of_owp` `ZeroKnowledge/NP.lean:742` (`zk_proof_of_mem_NP` `:720`) | `∃ OWP` (yes) | yes | **MH** | `LevinNPHard L3COL R3COL` (`:654`): the honest maps' efficiency (Q8) |
| **[PS10] ch. 5** | | | | | |
| R19 | `prgScheme_singleMessageSecure` `Encryption/PrivateKey/FromPRG.lean:295` | `PRG.Secure` (yes) | yes | **M** | |
| R20 | `prfScheme_multiMessageSecure` `Encryption/PrivateKey/FromPRF.lean:338`; `exists_multiMessageSecure_of_exists_prg` `:367` | `PRF` (yes) | yes | **M** | |
| R21 | `prfFixedScheme_cpa` `Encryption/PrivateKey/OracleFromPRF.lean:414`; `prfFixedScheme_cca1` `:431` | `PRF` (yes) | `INDSecure` (yes) | **M** | `Encryption/PrivateKey.lean:66`, `:71` still say "pending": stale |
| R22 | `tdpBitScheme_singleBitSecure` `Encryption/PublicKey/Trapdoor.lean:422`; `OneWay.exists_glPad_singleBitSecure` `:570`; `tdpBitScheme_padded_cpa` `Encryption/PublicKey/TrapdoorCPA.lean:42` | TDP one-way (yes) | yes | **M** | |
| R23 | `SingleBitSecure.bitwise_padded_cpa` `Encryption/PublicKey/BitwiseCPA.lean:481`; `.exists_adaptive_cpa` `:541`; `.padded_cpa` `Encryption/PublicKey/OracleSecurity/PaddedCPA.lean:314` | yes | yes | **M** | |
| R24 | `INDSecure.adaptive_cpa` `Encryption/PublicKey/AdaptiveCPA.lean:85` | yes | yes | **M** | |
| R25 | `exists_adaptiveCPA_of_rsa` `Implications/PublicKey.lean:79`; `exists_adaptiveCPA_of_factoring` `:97` | RSA / factoring (yes) | yes | **MH** | AFP (+ `BlumDensity`) |
| R26 | `elGamal_secure` `Encryption/PublicKey/ElGamal.lean:1772` | `DDHAssumption` (yes) | `GroupPKScheme.Secure` (yes) | **MH** | AFP; `hbig` is a size condition |
| R27 | `prfMAC_secure` `Authentication/MAC/FromPRF.lean:158` | `PRF` (yes) | yes | **M** | |
| R28 | `lamport_oneTimeSecure` `Authentication/Signatures/Lamport.lean:943` | OWF (yes) | yes | **M** | the helper's `hred` (`Authentication/Signatures/Lamport/Closing.lean:72`, `:84`) is discharged at `Lamport.lean:946` |
| R29 | `hashAndSign_oneTimeSecure` `Authentication/Signatures/HashAndSign.lean:609`; `exists_oneTimeSecure_of_crh_owf` `:644` | CRH + OWF (yes) | yes | **M** | |
| R30 | `dlHash_crh` `Hashing/FromDiscreteLog.lean:767` (reduction `Hashing/FromDiscreteLog/Reduction.lean:325–365`) | `DLHard` (yes) | `CollisionResistant` (yes) | **MH** | AFP `add`, `divMod`, `sub` |
| **[PS10] ch. 6** | | | | | |
| R31 | `otProtocol_hbcSecure` `SecureComputation/ObliviousTransfer.lean:740` | TDP + `EnhancedHardCore` (yes) | `HBCSecure` (yes) | **M** | |
| R32 | `HybridProtocol.hbcSecure_compose` `SecureComputation/ComposeSecurity.lean:429` | `HBCSecure` (yes) | yes | **M** | |
| R33 | `yaoProtocol_hbcSecure` `SecureComputation/YaoReal.lean:95` | TDP + `EnhancedHardCore` (yes) | yes | **M** | `YaoReal.lean:42–43` ("their `sorry`s") is stale |
| R34 | `specialScheme_multiMessageSecure_of_joint` `SecureComputation/SpecialEncryptionMulti.lean:341` | yes | yes | **M** | |
| **[PS10] ch. 7** | | | | | |
| R35 | `ccaScheme_cca2` `Encryption/PrivateKey/EncryptThenTag.lean:668` | `PRF` (yes) | yes | **M** | stale "pending" note at `Encryption/PrivateKey.lean:71` |
| R36 | `nmSecure_cca2_of_indSecure_cca2` `Encryption/PublicKey/NonMalleability/Indistinguishability.lean:397`; `simNMSecure_of_nmSecure_cpa` `Encryption/PublicKey/NonMalleability/Simulation.lean:771` | yes | yes | **M** | |
| R37 | `colSeq_efficientProverProof_zk` `Composability/ThreeColoring.lean:125` | `Commitment` (yes) | `ZK` (yes) | **M** | docstring `:123` ("admitted fill targets") is stale |
| **[PS10] ch. 8** | | | | | |
| R38 | `bpp_subset_dtime_subexp` `Randomness/Derandomization.lean:113` | `∃ PRG.Secure` (yes) | a class inclusion | **M** | the distinguisher is a machine |
| R39 | `not_weakLearnsUnder_prfConcept` `Randomness/Learning.lean:198` | `PRF` (yes) | learners are `NUPPT` | **M** | |
| **Pairings** | | | | | |
| R40 | `bb1_sidSecure` `AdvancedEncryption/IdentityBased/BonehBoyenSecurity.lean:177`; machine `exists_bb1_distinguisher` `AdvancedEncryption/IdentityBased/BonehBoyenMachine.lean:104` | `DBDHAssumption` (yes) | `SIDSecure` (yes) | **MH** | `H : ArithmeticFP`, `O : G.Ops`; built by `exists_handlerMachine`. Honest algorithms N (N1). |
| R41 | `jouxKeyIndist_of_dbdhAssumption` `KeyExchange/Joux.lean:185` | `DBDHAssumption` (yes) | `JouxKeyIndist` (yes) | **M** | identity reduction. Honest parties N (N14). |
| R42 | `bdhAssumption_of_dbdhAssumption` `Pairing/Assumptions.lean:426` | yes | yes | **M** | |
| **Lattice (branch)** | | | | | |
| R43 | Regev symmetric `distAdv_encrypt_le` `Encryption/Symmetric/Regev/Experiments.lean:116` | `LWE.decisionAdvantage` of `fun c r => D (shift P μ c) r`, a **function** | `distAdv` at **one** `Parameters` | **F** → G | 0 `NUPPT` in file. "efficiency and all-polynomial sample quantification remain separate obligations" (`:115`). No asymptotic statement. |
| R44 | Regev PKE `distAdv_encrypt_le` `Encryption/PublicKey/Regev/Experiments.lean:301` (+ `two_extractionError_le` `:334`) | function-level `reduction P μ D` (`:105`) | per `Parameters` | **F** → G | 0 `NUPPT`. The reduction uses only binary coins: TM-feasible now (§3.3). |
| R45 | GSW phase 5 `distAdv_encrypt_le_of_width` `AdvancedEncryption/Homomorphic/GSW/Security.lean:287` (`distAdv_encrypt_le` `:248`) | function-level | per `Parameters` | **F** → G | the 1 `NUPPT` mention is prose (`:47`) |
| R46 | Lossy TDF `concealed_advantage_le` `TrapdoorFunctions/Lossy/Experiments.lean:234`; `shifted_advantage_le` `:315` | sums of `decisionAdvantage (columnTest …)` (`:119`), a function | per `Parameters` | **F** → G | `columnTest` draws fresh `Z_q` secrets, uniform columns and `χ` noise. A machine needs the sampler bridge, or the dyadic/bit-noise profile. |
| R47 | All-but-one TDF | — | — | **G** (absent) | only algebra (`TrapdoorFunctions/AllButOne/Basic.lean:103–244`, `AntiCyclic.lean`); no security statement; no ABO interface |
| R48 | LWE PRG `pseudorandom_under_DLWE` `Pseudorandom/Generators/LWE/Basic.lean:85` | `DLWEAssumption` (yes) | `Negligible (prgAdv (generate …) (D …))` for `D : NUPPT` (yes) | **M** (identity) | the conclusion is not `PRG.Secure`. The bit and flat variants `generateBits_advantage` `Bits.lean:92` and `generateFlat_advantage` `Flat.lean:152` are **F** (equalities for a function `D`). |
| R49 | SIS `negligible_collisions_of_SIS` `Hashing/SIS/Asymptotic.lean:71`; `dyadic_collision_negligible` `:116` | `SISAssumption` (yes) | raw `collisionAt` (yes) | **M** | machine by `NUPPT.exists_compParam` (`TCSlib/Complexity/Randomized/Closure.lean:241`); not `CRH.CollisionResistant` |
| **Lattice (PR #377, GSW 6b statements, head `680be9fa45a9cf5deeb7a59820e8e86aaaa4f068`)** | | | | | |
| R50 | A1 `indCPA_of_dlweAssumption` `GSW/Asymptotic.lean:281` | `DLWEAssumption` (yes) **and `heff : ReductionEfficient F`** (`:202`) | `Negligible (distAdv … (D.distinguisherL κ …))` for `D : NUPPT` (yes) | **G** (smuggled) | `ReductionEfficient F := ∀ D μ, ∃ D' : NUPPT, ∀ κ, decisionAdvantage … (reduction … D_κ) ≤ F.advantageAt D' κ`. Its docstring says: "A domination statement, not a machine construction". Body `sorry`. Ruling P6-Q10. |
| R51 | A3 `leveledINDCPA_of_dlweAssumption` `GSW/Asymptotic.lean:312` | as R50, with `LeveledReductionEfficient F L` (`:230`) | yes | **G** (smuggled) | body `sorry`; concrete L5 `distAdv_leveledView_le` `GSW/LeveledSecurity.lean:343` is F and `sorry` |
| R52 | Pure FHE: `WeakCircularSecureFamily F` `GSW/Asymptotic.lean:175` (A2 reader) | — | assumption (yes) | **G** (by design) | the security *is* the circular-security assumption; no reduction exists. Concrete `distAdv_fheView_noEvk_le` `GSW/Circular.lean:137` is F (`sorry`). |

**Notes.**
- **Counts:** M 34 · MH 10 · F 4 (R43–R46) · G 4 (R47, R50, R51, R52). Each F row is also a gap at the chain level, so
  8 rows in all have no `NUPPT` reduction. R48 is M.
- **On the lattice side, inventory r1 is confirmed and sharpened.**
  - Regev (symmetric and PKE), GSW phase 5 and the lossy TDF use function-level distinguishers only, against no
    adversary class.
  - The LWE PRG and the SIS hash are refinements: both are genuinely `NUPPT` → `NUPPT`, but in raw form, so no
    primitive predicate follows.

### 3.3 What each lattice reduction needs

| Row | What the reduction does | Coins it draws | Machine route |
|---|---|---|---|
| R44 Regev PKE; R50/R51 GSW | Re-encrypts a fixed bit under the challenge key: `[A\|b]ᵀR + μG`, or the Regev subset sum. Re-encodes the view. Calls `D`. | binary only (`R` / subset coins) | **TM now.** Mod-`q` arithmetic on `ClassP/BinaryArith` with the `Encoding/BinaryArith` adapters, and the matrix products of `Encoding/DyadicLinearAlgebra`. Since `F.parameters` is an arbitrary function, `(n, m, q)` go in the reduction's **advice**, which a reduction may take. `exists_handlerMachine` / `exists_compParam`, and `RealizesOn` (#380) for the verdict lemma. |
| R43 Regev symmetric | adds `μ·⌊q/2⌋` to column `b` | none | TM now (trivial) |
| R46 lossy | inserts the challenge as column `k`; simulates earlier real columns (`Z_q` secrets, `χ` noise) and later uniform columns | uniform `Z_q`, `χ` | dyadic `q` with `bitNoise`: TM now. General `q` or `χ`: sampler bridge (#378), statistically close transfer. |
| R47 ABO | (statement first) | as R46 | after EF-D4 |

---

## 4. Axiom sweep (Part 3)

### 4.1 Method

**Tree.**
- The tree was `$SP/ol-effaudit`, a `cp -al` copy of `$SP/olean-snapshot` (snapshot #10, T `cf6a2266`).
- It carried the procedure's Mathlib overlay, needed for `Randomness/Derandomization/RootSchedule`:
  - `mloverlay.sh`: 3,346 links;
  - `NthRootLemmas.olean`, copied with SHA-256 `c0a9cff0…`.

**Snapshot #10 is Lean-equal to the tip.**
- `git diff --name-only cf6a2266 32a40963` lists nothing under `TCSlib/`, `TCSlib.lean`, `audits/`, `lakefile*`,
  `lean-toolchain` or `lake-manifest.json`.
- The only `.lean` file changed is `briefs/io-components/sampler-bridge/Skeleton.lean`, which is not in the build.
- Everything else is `briefs/` and four plan `.md` files.

**Runs.**
- **One process at a time.** One scratch file, `$SP/eff-audit/AxSweep.lean`, was run in sequence.
  - The direct `lean` 4.25.0 binary was used, with the `scripts/lean_check_tree.sh` `LEAN_PATH` and no `-o`.
  - No `lake`.
- **Runs:**
  - two early attempts stopped at start-up (missing `time` binary; `elan` proxy) or at elaboration (a type error
    in the meta command), with no output;
  - census run: 359 s, rc 0;
  - run 2, adding the probes and `#print axioms`: 501 s, rc 0;
  - run 3, adding `BinaryArith`: 474 s, rc 0, 0 `error`;
  - the census file is byte-identical across the three good runs.

**The scratch file imports the 29 Cryptography facades of `TCSlib.lean` (lines 50–78) and
`TCSlib.Complexity.ClassP.BinaryArith`.** Its meta command works as follows:
1. **Scan.** It reads every constant of the TCSlib, PFR and LeanAPAP modules in the environment: 44,014 constants. It
   records the *direct* `sorryAx` users, those whose type or value mentions `sorryAx`, and any local `axiom`.
2. **Reach.** It builds the reverse dependency graph and runs a reverse BFS from each direct user, which gives every
   constant that reaches `sorryAx`, with its sources.
3. **Census.** It writes one census line per constant of a `TCSlib.Cryptography.*` module.
4. **`#print axioms`.** It runs `#print axioms`, the kernel's own `collectAxioms`, on 96 named targets. This is an
   independent check.

**Coverage.**
- The census has 16,913 crypto constants in 486 modules.
- The 45 crypto `.lean` files with no constants are the 44 facades and the orphan `RSA.lean`.

**Controls.**
- `#print axioms Turing.FinTM.lengthBitsTM_computes` and `Turing.FinTM.polyBitsTM_computes` report `sorryAx`.
- The graph probe reports `polyBitsTM_computes` reaching `sorryAx` through `lengthBitsTM_computes`.
- `NUPPT.ofPolyTimeUniform`, `NUPPT.exists_compParam` and `PolyTimeComputable` report no `sorryAx`.

**Cleanup.**
- The copy was deleted after run 2, recreated for run 3, and deleted again.
- `snapmap.py verify` of snapshot #10 against `olean-snapshot.map-cf6a2266.tsv` gives 1,478 files, extra 0 / changed 0 /
  missing 0, RESULT OK.
- No other job's process was touched.

**Evidence (scratch, 2.2 MB).**

| File | SHA-256 |
|---|---|
| `AxSweep.lean` | `a510ded2…` |
| `census.tsv` | `a88b58a8…` |
| `census.tsv.reach` | `dbe97b37…` |
| `sweep2.log` | `43a1461c…` |
| `sweep3.log` | `9c0bc497…` |

### 4.2 Results

| Scope | Constants | Reaching `sorryAx` |
|---|---|---|
| All `TCSlib.Cryptography.*` (486 modules) | 16,913 | **0** |
| `TCSlib.Complexity.ClassP.BinaryArith.*` | 731 | **0** |
| Local constants in the import closure | 44,014 | 28 (all TM / Randomized layer, below) |
| Local `axiom` declarations | — | 0 |

- **`#print axioms`: 94 of the 96 targets depend only on `propext`, `Classical.choice` and `Quot.sound`.**
  `owpGenPRG` depends on `propext` and `Quot.sound` only. The 2 controls show `sorryAx`.
- **The targets cover four groups:**
  - every Part 2 headline: R1–R46, R48–R49, including `bb1_sidSecure`, `elGamal_secure`, `dlHash_crh`, all candidate
    `*_oneWay`, `yaoProtocol_hbcSecure`, `otProtocol_hbcSecure`, `zk_proof_of_mem_NP_of_owp`, `col_zeroKnowledgeProof`,
    `ccaScheme_cca2`, `nmSecure_cca2_of_indSecure_cca2`, `bpp_subset_dtime_subexp`;
  - the reduction-machine lemmas `exists_handlerMachine`, `exists_bb1_distinguisher` and `NUPPT.exists_compParam`;
  - the P-row efficiency lemmas and constructions: `exists_ggmPRF_evaluator`, `prgIterFun_poly`,
    `owpComStr_polyTimeComputable`, `colProver_efficient`, `colVerifier_efficient`, `seqProver_efficient`,
    `seqVerifier_efficient`, `otProtocol_polyTime`, `yaoHybrid_polyTime`, `polyTime_compose`, `fUniversal_easy`,
    `FunFamily.Easy.prod`, `polyTimeComputable_hashPoly`, `polyTimeComputable_halfStr`, `tdpBitScheme`, `prgScheme`,
    `prfScheme`, `ccaScheme`, `prfMAC`, `lamport`, `hashAndSign`, `dlHash`, `owpGenPRG`, `specialScheme`, `otProtocol`,
    `yaoProtocol`, `FunFamily.toCollection`, `factoringCollection`, `rsaTrapdoor`, `elGamal`;
  - `BinArith.polyTimeComputable_{add,sub,le,mul,div,mod,powMod,gcd}`, and
    `Encoding.BinaryArith.polyTimeComputable_{toLE,normalizeWidthPoly,fromLEPoly}`.
- **The census covers the rest.** Every inventory r1 **P** row and every Part 2 machine lemma is a crypto constant, and
  all are clean.

**`sorryAx` sources in the closure.** There are 22 direct users. None is reached by any crypto constant.

| Module (`TCSlib/Complexity/…`) | Direct `sorryAx` users |
|---|---|
| `TuringMachine/Composition` | `idTM_computes`, `condTM_computes_iff`, `ifEqTM_computes` |
| `TuringMachine/Build/Loop` | `loopHostTM_contracts`, `loopHostTM_finds`, `loopHostTM_decides`, `loopHostTM_spaceUsed_le_budget`, `emitLoopTM_computes` |
| `TuringMachine/Build/Primitives` | `appendBitTM_computes`, `unaryTokenTM_computes`, `polyUnaryTM_spaceUsed` |
| `TuringMachine/Build/RecordTable` | `exists_recordValidTM`, `exists_recordNextTM`, `exists_tableFindTM`, `exists_tableAppendTM` |
| `TuringMachine/Build/Wrappers` | `timedCondTM_computes`, `timedCondTM_spaceUsed` |
| `TuringMachine/Encoding` | `pairDiagTM_computes` |
| `TuringMachine/Simulation` | `branchTM_spaceUsed` |
| `ClassP/TimeConstructible` | `lengthBitsTM_computes`, `lengthBitsTM_spaceUsed` |
| `Randomized/NonUniform` | `NUPPT.decides_of_decidesWithAdviceInTime` |

The 6 indirect users are all in `Build/Primitives`: `polyBitsTM_computes`, `splitSolveTM_computes`,
`splitSolveWithTM_computes`, `splitSolveTM_spaceUsed`, `stripLastTM_computes` and the private `split_fuel`.

**MIG-1 count.** The brief's "17 sorried specs" counts MIG-1's TM specs. The closure here holds 21 TM-layer direct users,
plus the one `Randomized/NonUniform` lemma, which is not part of MIG-1. Reconciling the two lists is MIG-1's business. It
does not affect crypto.

**Consequences.**
- **Inventory r1 caveat 2 and unclear item 1 are settled.** Every **P** row and `BinaryArith` are free of `sorryAx`.
- **TM tooling is clean to build on.** That covers `BinaryArith`, the `Encoding` adapters, `exists_handlerMachine` and
  `exists_compParam`.
- **The stale "pending/admitted/sorry" docstrings are confirmed stale.** They are `Encryption/PrivateKey.lean:66`, `:71`,
  `SecureComputation/YaoReal.lean:43`, `Composability/ThreeColoring.lean:123`, `Pseudorandom/Generators/LWE.lean:22`,
  `TrapdoorFunctions/Lossy.lean:22` and `TrapdoorFunctions/AllButOne.lean:20`. They are a docstring-only fix, a candidate
  Stage 3 item.
- **Not swept:** PR #377, which is not in snapshot #10. It has 24 `sorry`s by count of its 11 files (A1, A3 and the
  concrete L5 and circular bounds among them), as the proved-modulo phase intends.
- **The word-RAM bridge would add `sorryAx`.** Its admission `WordRAM.exists_simulation`
  (`briefs/io-components/ram-bridge-assessment.md` §1) would enter every item proved through it, until RAM Stage 2 is
  proved. TM-route items carry none.

---

## 5. Remediation plan

**Routes and sizes.**
- The standing route is Claude for fills and Codex for gates. "In-house" means the maintainer.
- Sizes are new Lean lines, with ±40% on fills.
- **TM** means it can start now on `ClassP/BinaryArith`, `Encoding/{BinaryArith,DyadicArithmetic,DyadicLinearAlgebra,
  DyadicUniform}`, `exists_handlerMachine`, `NUPPT.exists_comp{,Param}` and `exists_reparam_pre_post`
  (`Asymptotic/UniversalLemmas.lean:79`).
- **SB** means it needs the sampler bridge (#378, `foundations/coin-sampling` `51dc7672`, with the contract
  `foundations/coin-contract`).
- **RL** means it uses `RealizesOn` (#380, `foundations/realization` `cdc0934f`), which is optional but saves glue.
- **RAM** means the word-RAM bridge: deliverables (a1)–(a5) and (b1) of `ram-bridge-assessment.md`.

### 5.1 Jobs

**A. Definition retrofits** (statement-level; rulings first)

| Job | Content | Route | Size | Depends on | Stage 2 interaction |
|---|---|---|---|---|---|
| **EF-D1** | `LWE.EfficientFamily` and `SIS.EfficientFamily` (Q3 A). They carry a uniform parameter map `1^κ ↦ ⟨n, m, q⟩` (`PolyTimeComputable`) and, for LWE, a noise sampler with an efficiency field in the #378 contract form (`DrawSamplable`/`CoinSampler`). The assumptions stay on the raw `Family`. | in-house statement + Codex gate | 200–350 | Q3; #378 for the noise field (or a bit-noise-only first cut, TM) | none: `LWE/`, `SIS/` are outside `scope.tsv` |
| **EF-D2** | Pairings (Q4 A): `BilinearGen` carries its `Ops` (or `EfficientBilinearGen extends BilinearGen`). Re-thread `O : G.Ops` out of 17 files. | in-house | 150 + 200–400 churn | Q4 | `Pairing/Assumptions` is J0 (S2-A); BB1 `Words`/`Oracles`/`Lazy` are J4 → **after S2-A and J4 merge** |
| **EF-D3** | `IBEScheme` efficiency (Q4 A): uniform string-machine fields beside the typed algorithms, with encodings `PolyTimeComputable`. Or the raw-bundle form `IBEScheme` + `IBEScheme.Efficient`, inhabited as a pair. | in-house statement | 150–300 | Q4, EF-D2 | `IdentityBased/Defs` is J0 → after S2-A |
| **EF-D4** | New interfaces `LossyTDF` and `ABOTDF` ([PW08]/[PW10] definitions): efficiency fields (E·s), plus lossiness and indistinguishability predicates over `NUPPT`. | Claude statement job + Codex gate | 300–500 | Q9 | none |
| **EF-D5** | Secret sharing / BGW (Q7 A): record as exempt (information-theoretic) until a computational consumer appears. | in-house record | 0 | Q7 | none |

**B. Honest-algorithm efficiency** (fills)

| Job | Content | Route | Size | Depends on | Stage 2 |
|---|---|---|---|---|---|
| **EF-H1** | Prove the 7 cheap `ArithmeticFP` fields: `mul`, `add`, `sub`, `divMod`, `modExp`, `le`, `size` (inventory §4.1). Then `xgcd`: at a prime modulus via Fermat/`powMod`; in general by extended Euclid on `polyTimeComputable_iterate`. All go in a **new file** (`Candidates/ArithmeticDischarge.lean`), so `Arithmetic.lean` is untouched. | Claude fill | 500–900 + `xgcd` 300–600 | TM | none (new file) |
| **EF-H2** | Split the AFP bundle (Q5 A) and re-thread the consumers. B5, B8, the DL-hash reduction, B6, B7 and the BB1 reduction become free of AFP. R6–R8 keep only `prime`. | in-house | 200–400 churn | EF-H1, Q5 | `Candidates/{Factoring,RSA,Rabin,DDH,Concrete}` are J2 → **after S2-A merges** |
| **EF-H3** | `prime` (Q5): no job until ruled. | — | — | Q5 | — |
| **EF-H4** | The dyadic SIS hash as a `CRH`: Gen passes through `N·M·W` fair coins (exact law); `inDom`/`inRange`; `collisionGame` ↔ `collisionAt`. CR comes from R49. | Claude fill | 400–700 | TM; EF-D1 (`SIS.EfficientFamily`) | new file beside `Hashing/SIS/`; J2 owns only `CollisionOutput` |
| **EF-H5** | Regev PKE at dyadic `q` with `bitNoise` as a `BitPublicKeyScheme` over `EfficientFamily`. `SingleBitSecure` comes from EF-R2. | Claude fill | 900–1,500 | TM; EF-D1, EF-R2 | none |
| **EF-H6** | Regev symmetric as a `PrivateKeyScheme` / `FixedLengthScheme`. | Claude fill | 700–1,200 | TM; EF-D1, EF-R3 | none |
| **EF-H7** | The LWE PRG (`Flat`, dyadic) as a `PRG`, with `PRG.Secure` from `generateFlat_advantage` + R48 + `Easy`. | Claude fill | 500–900 | TM; EF-D1 | none |
| **EF-H8** | GSW honest algorithms: KeyGen, Enc, Dec, then leveled and bootstrapped Eval (matrix products, `G⁻¹`, NAND circuits) as a `BitPublicKeyScheme`, with an evaluator efficiency predicate. | Claude fill(s) | 2,000–4,000 | **RAM preferred** for Eval; KeyGen/Enc/Dec are TM-feasible at dyadic `q`; after #377 and the 6b fills | none |
| **EF-H9** | Lossy and ABO TDF honest algorithms as instances of EF-D4. | Claude fill | 1,000–2,000 | TM at modulus `2^(b+a)` with bit noise; SB for general `χ`; EF-D4 | none |
| **EF-H10** | BB1 and Joux honest machines under `Ops` + AFP. They reuse `BonehBoyenMachine/{Words,Draws}`. The exponent draws use `sampleBelowL` (statistical), with a non-identity fallback for `g ∈ G*`, or the exact SB contract. | Claude fill | 1,000–1,800 | TM (+SB for exact laws); EF-D2, EF-D3 | after S2-A and J4 |
| **EF-H11** | Shamir / BGW (only if Q7 = B). | Claude fill | 600 / 2,000+ | TM + SB | none |
| **EF-H12** | `LevinNPHard` for 3COL (Q8): a string-level Levin reduction. | Claude fill | 2,000–4,000 | TM; reuse of Arora–Barak `NPReductions` is read-only and needs the AB owner's agreement; this audit proposes no AB edit | J6 (`ZeroKnowledge/NP`) → after J6 |
| **EF-H13** | Schnorr port to `Protocol`. | low priority | 800–1,200 | TM + SB | none |

**C. Reduction machines** (fills)

| Job | Content | Route | Size | Depends on | Stage 2 |
|---|---|---|---|---|---|
| **EF-R1** | Prove `ReductionEfficient F` and `LeveledReductionEfficient F L` **as theorems for every `F`** (with the width condition): parameters in advice, binary `R` coins, mod-`q` arithmetic, `encodeView` emission, and a verdict through `RealizesOn`. A1 and A3 then hold with `heff` discharged. Option: drop `heff` from the statements (Q2). | Claude fill | 700–1,200 | TM, RL; after #377 merges (best after its fill U19) | none |
| **EF-R2** | Regev PKE: an asymptotic statement over `LWE.Family` (`NUPPT` → `NUPPT`; IND-CPA of the encoded views) plus the reduction machine, which is binary coins + matrix-vector mod `q`. | Claude statement + fill | 600–1,000 | TM, RL | none |
| **EF-R3** | Regev symmetric: asymptotic statement + machine (shift only). | Claude | 400–700 | TM, RL | none |
| **EF-R4** | Lossy TDF: asymptotic mode-indistinguishability over `EfficientFamily` with the column-hybrid machine. | Claude | 800–1,300 | dyadic + bit noise: TM; general: SB (statistically close transfer); EF-D1, EF-D4 | none |
| **EF-R5** | ABO TDF: security statement + reduction. | Claude | 600–1,000 | EF-D4, EF-R4 | none |
| **EF-R6** | BB1: MH → M once EF-D2 puts `Ops` in the definition and EF-H2 removes AFP from the reduction. This is a restatement of `bb1_sidSecure` / `exists_bb1_distinguisher`. | in-house | 100–200 | EF-D2, EF-H1/H2 | after S2-A and J4 |

**Totals.**
- Definitions: about 0.8–1.6k lines.
- Honest algorithms: about 11–20k, of which GSW Eval and `LevinNPHard` are 4–8k.
- Reductions: about 3.2–5.4k.

### 5.2 Sequencing against cleanup Stage 2

S2-A (J0 + J1 + J2) is running on `cleanup/stage2-s2a`. Wave 1 is J3, J4, J5 and J6. Their owner files are in
`briefs/pass-shelat-ch5-8/cleanup-stage2/scope.tsv`.

1. **Now, on TM tooling, file-disjoint from Stage 2.**
   - **EF-H1** (new file).
   - **EF-R2** and **EF-R3**: statements over the raw `LWE.Family`, needing no honest efficiency.
   - **EF-D4.**
   - **EF-D1**: in a bit-noise-first cut if #378 has not merged.
   - **EF-H4**, once EF-D1 lands.
   - No row of `scope.tsv` touches `LWE/`, `SIS/`, `Encryption/*/Regev`, `GSW/`, `TrapdoorFunctions/`,
     `KeyExchange/`, `SecretSharing/`, `MPC/` or `Candidates/Arithmetic.lean`. Only the facade lines need
     coordination.
2. **After #377 (GSW 6b statements) merges:** **EF-R1**, and the Q2 restatement if ruled.
3. **After #378 merges:** the general-noise halves of EF-D1, EF-H5–EF-H7, EF-H9 and EF-R4.
4. **After S2-A merges:** **EF-H2** (Candidates, J2) and **EF-D2/EF-D3** (`Pairing/Assumptions`, `IdentityBased/Defs`,
   J0).
5. **After J4 merges:** **EF-H10** and **EF-R6**. J4 owns `BonehBoyenMachine/{Words,Oracles}` and
   `BonehBoyenSecurity/Lazy`.
6. **After J6:** EF-H12, if ruled.
7. **After the RAM bridge** ((a1)–(a5), (b1)): **EF-H8** (GSW Eval). Optionally, lattice honest algorithms can be
   re-routed to RAM programs.
   - Such items carry `sorryAx` via `WordRAM.exists_simulation` until RAM Stage 2 is proved.
   - Q10 asks whether that counts as "proved".

### 5.3 RAM bridge versus TM now

| On TM tooling now | Needs the sampler bridge (#378) | RAM bridge preferred or needed |
|---|---|---|
| EF-H1, EF-H2, EF-H4, EF-H5–H7 (dyadic), EF-H10 (statistical draws), EF-R1, EF-R2, EF-R3, EF-R4 (dyadic), EF-R6, and all definition retrofits | non-dyadic `q`; general `χ`; exact `Z_p`/`G` laws (BB1, Joux, Schnorr exact); Shamir over non-power-of-two fields; EF-R4 general | EF-H8 GSW Eval (bootstrapping and leveled circuits); a PHFE-style use of `Ops` as subroutines needs (b1) |

---

## 6. Questions for Seyoon (recommended option first)

**Q1. Efficiency in the primitive *predicate* (E·p) rather than the raw structure.** This covers `FunFamily` + `StrongOneWay.easy`, `PRG` + `PRG.Secure`, `Strategy`/`Protocol` + `InteractiveProof`/`ZK`, and `Functionality` + `HBCSecure`.
- **A (recommended).** E·p satisfies rule 15. The raw structure is the "raw algorithm bundle" the rule allows, and the
  named primitive cannot hold without the efficiency proof. This follows the text: [PS10] Def 27.3 and Def 77.1 have
  efficiency as clause (1).
- **B.** Move `easy` into the raw structures. This touches 49 + 27 + 88 files, mostly signature churn.
- **C.** Do B only for `PRG`.

**Q2. GSW 6b A1/A3 hypothesis `ReductionEfficient` / `LeveledReductionEfficient`** (P6-Q10, before rule 15).
- **A (recommended).** Let #377 land as audited. Add EF-R1, which proves both predicates for every `F` (parameters as
  advice), so A1 and A3 become unconditional through one-line wrappers. Record P6-Q10 as superseded.
- **B.** Re-issue A1 and A3 without `heff` before Gate 46 closes, and make the machine part of the U19 fill.
- **C.** Keep `heff` as accepted debt. This contradicts rule 15 ("not accepted debt").

**Q3. LWE/SIS family efficiency.**
- **A (recommended).** A separate `EfficientFamily extends Family`: a uniform parameter map, plus a noise sampler in the
  #378 contract form. `DLWEAssumption` and `SISAssumption` stay on the raw `Family`, since a hardness assumption needs no
  honest efficiency. Every scheme instance requires `EfficientFamily`.
- **B.** Add the fields to `Family` itself. This touches the assumption, every consumer and #377.
- **C.** A `Family.Efficient` predicate. This is weaker: the primitive is then a pair, not a structure.

**Q4. Pairings: the Q5 deferral (`IBEScheme`) and `Ops`.**
- **A (recommended).** Supersede Q5 by rule 15.
  - `BilinearGen` carries `Ops` (EF-D2).
  - `IBEScheme` gains uniform machine fields (EF-D3).
  - `bb1Scheme` is re-inhabited by EF-H10, with statistical draws and a correctness-preserving fallback.
- **B.** Keep `IBEScheme` typed, plus `IBEScheme.Efficient`, and require the pair at every consumer.
- **C.** Keep the Q5 deferral.

**Q5. `ArithmeticFP`.**
- **A (recommended).** Discharge 8 fields (EF-H1, `xgcd` included). Split the bundle so that `prime` alone is a named
  hypothesis (`PrimesInP`, true by AKS). Factoring, RSA and Rabin generators stay conditional only on it, recorded as a
  standing exception.
- **B.** Formalize a deterministic primality test (AKS; very large).
- **C.** Switch the samplers to the library's randomized test (`PRIMES ∈ coRP`). This needs a statistical `sample_spec`,
  which is a D10-style change to the factoring, RSA and Rabin collections.

**Q6. Hypothesis-object generators** (`SafePrimeGen`, `FullGroupGen`, `BilinearGen`). They are E·s by type, but nothing
inhabits them.
- **A (recommended).** Accept them as assumption objects (their existence is the assumption, [PS10] pp. 52–53), and
  document them as such in the docstrings.
- **B.** Seek concrete instances (open problem for safe primes; concrete curves are out of scope).

**Q7. Secret sharing and BGW.**
- **A (recommended).** Exempt while every consumer is information-theoretic, and record it in the deferred-work list.
- **B.** Retrofit now (EF-H11).

**Q8. ZK for NP (`LevinNPHard`).**
- **A (recommended).** Keep it as a named hypothesis for now, and schedule EF-H12 after J6, subject to the Arora–Barak
  owner agreeing to read-only reuse.
- **B.** Start EF-H12 now.
- **C.** Accept it permanently.

**Q9. Lossy and ABO TDF interfaces.**
- **A (recommended).** Define them now (EF-D4), so that the lossy and ABO results have a primitive to land in.
- **B.** Defer until a CCA2 consumer exists.

**Q10. Items routed through the word-RAM bridge carry `sorryAx`** (`WordRAM.exists_simulation`) until RAM Stage 2 is
proved.
- **A (recommended).** Route everything feasible on TM tooling now: all items except GSW Eval. Allow RAM-routed items
  only with the admission disclosed, and count them as "proved" only once `exists_simulation` is proved.
- **B.** Wait for the RAM bridge for all lattice honest algorithms.
- **C.** Count RAM-routed items as proved now.

**Q11. Sequencing with Stage 2.**
- **A (recommended).** Start the file-disjoint jobs now (§5.2 step 1). Hold the Candidates, Pairing and IBE retrofits
  until S2-A and J4 merge.
- **B.** Fold EF-H2 and EF-D2/D3 into S2-A/J4.
- **C.** Hold all efficiency work until the Stage 2 gate.
