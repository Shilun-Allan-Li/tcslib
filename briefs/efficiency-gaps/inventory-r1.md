# Efficiency of honest algorithms: inventory r1

Records branch `cryptography/pass-shelat-ch2-4`, head `aac476f1cf74aea6e7488233525a41eb28e1b914`
(2026-11-18). Static survey only: `grep`/`rg`, file reads, `git` read-only, `python3 -I`. No Lean,
no `lake`, so no axiom closure was checked. Requested by Seyoon: every primitive and construction
under `TCSlib/Cryptography/` whose honest parties should be proved efficient but are not yet.

All paths below are relative to `TCSlib/Cryptography/` unless they start with `TCSlib/`, a plan
file name, or `briefs/`.

## 0. Conventions

**Status of an honest algorithm.**

| Code | Meaning |
|---|---|
| **P** | Proved efficient, unconditionally. For a generic construction, "unconditionally" means relative only to the efficiency fields of its input primitive. The input interface demands those fields, so they are not extra hypotheses: a PRF's `easy`, a commitment's `easy`, a collection's `gen`/`sample`/`eval_poly`. |
| **H** | Proved efficient under a stated efficiency hypothesis: `Candidates.ArithmeticFP`, `BilinearGen.Ops`, or `LevinNPHard`. Also used for a *hypothesis-object* generator (`ExpGroupGen`, `BilinearGen`): its type demands an `NUPPT`, but no instance is built. These rows are marked "(obj)". |
| **D** | Efficiency deferred or absent. The algorithm is typed only as a Lean function or a `ProbComp`. |
| **+S** | Flag on a randomised algorithm whose coin law is non-dyadic: uniform `Z_p` or `G` with `p` prime, `Z_q` with `q` not a power of two, or a general finite noise law. Such an algorithm cannot be implemented exactly from fair coins and needs the planned sampler bridge (`IOComponentsPlan.md:34–46`). Every `+S` entry here is also a **D** entry. |

**Counting.** There is one entry per honest algorithm per construction row. Security reductions,
adversaries and simulators are listed separately (§3). Concrete-layer (Garg) modules are not
counted (§2.L). Statuses are written in bold in the "honest algorithms" column, and §5 counts
those bold tokens.

**Global caveats (static limits).**

1. `rg '\bsorry\b'` finds no `sorry` in Lean code under `TCSlib/Cryptography/`. The only hit
   is prose, at `SecureComputation/YaoReal.lean:43`.
2. The Turing-machine witness layer is mid-migration (MIG-1 stage S). It carries sorried specs,
   for example `idTM_computes` (`TCSlib/Complexity/TuringMachine/Composition.lean:155`, noted at
   `:73–74`), `lengthBitsTM_computes` (`TCSlib/Complexity/ClassP/TimeConstructible.lean:432`)
   and `loopHostTM_contracts` (`TCSlib/Complexity/TuringMachine/Build/Loop.lean:2303`).
   `polyBitsTM_computes` depends on one of them (`TCSlib/Complexity/TuringMachine/Build/Primitives.lean:75–78`).
   - The sources of `TCSlib/Complexity/ClassP/BinaryArith/` contain no `sorry`. Their transitive
     import closure (82 TCSlib modules) does include these TM files.
   - **Unclear:** whether any **P** row below, or `BinaryArith`, has `sorryAx` in its axiom
     closure. Only `#print axioms` can settle this.

## 1. Which interfaces demand efficiency

| Interface | Demands efficiency? | Evidence (file:line) |
|---|---|---|
| `Collection` (OWF collections) | yes | `gen : NUPPT` `Asymptotic/Collections.lean:151`, `sample : NUPPT` `:155`, `eval_poly : PolyTimeComputable eval` `:161`; uniformity of the sampler only up to `SampleClose` (`:200`, D10) |
| `TrapdoorCollection` | yes | `inv : NUPPT` `Asymptotic/Collections.lean:376` |
| `Collection.HardCore` | yes | polynomial-time evaluator `Asymptotic/Collections.lean:248` |
| `FunFamily` one-wayness (strong/weak/worst-case) | yes | `FunFamily.Easy` `Asymptotic/OneWay.lean:109`; field `easy` at `:132`, `:144`, `:167`, `:193` |
| `PRG` | yes (in `Secure`) | `PRG.Easy` `Pseudorandom/Generators/Asymptotic/Defs.lean:150`; the structure `:132` itself carries no efficiency field |
| `PRF` | yes | `easy` `Pseudorandom/Functions/Asymptotic/Defs.lean:446` |
| `PrivateKeyScheme`, `FixedLengthScheme` | yes | `gen/enc/dec : NUPPT` with `*_uniform` `Encryption/PrivateKey/Scheme.lean:58–62`; `FixedLengthScheme extends` it `Encryption/PrivateKey/OracleSecurity.lean:87` |
| `PublicKeyScheme`, `BitPublicKeyScheme` | yes | `dec_poly` `Encryption/PublicKey/Scheme.lean:55`, `:77` (gen/enc uniform `:51–53`, `:73–75`) |
| `FixedLengthPKScheme` | yes | `Encryption/PublicKey/OracleSecurity.lean:241–245` |
| `GroupPKScheme` (El Gamal shape) | yes | `Encryption/PublicKey/ElGamal.lean:116–120` |
| `MAC`, `SignatureScheme` | yes | `Authentication/MAC/Defs.lean:59–63`; `Authentication/Signatures/Defs.lean:72–76` |
| `CRH` | yes | `gen_uniform` `Hashing/CollisionResistant.lean:70`, `eval_poly` `:72` |
| `Commitment` | yes | `easy : PolyTimeComputable Com` `ZeroKnowledge/Commitment.lean:114` |
| `InteractiveProof`, `EfficientProverProof` | yes | `efficientV` `ZeroKnowledge/InteractiveProofs.lean:128`, `efficientP` `:350`; `Strategy.Efficient` `ZeroKnowledge/Interaction.lean:223` |
| `HBCSecure` (2PC) | yes | requires `Functionality.PolyTime` `SecureComputation/Defs.lean:152`, `:176`; hybrid model `SecureComputation/Hybrid.lean:206`; `YaoCircuit.uniform` `SecureComputation/Yao.lean:201` |
| `LevinReduction` | yes | `f_poly` `ZeroKnowledge/NP.lean:137`, `w_poly` `:139` |
| `Ensemble.Samplable` | yes (predicate, used where needed) | `Asymptotic/Ensembles.lean:169` |
| `ExpGroupGen` (safe-prime / DL generators) | yes, by type | `gen : NUPPT` `Candidates/DiscreteLog.lean:328`; hypothesis object, "no efficient sampler of safe primes with generators is known" `:320–325` |
| `BilinearGen` | yes, by type | `gen : NUPPT` `Pairing/Group.lean:285`; group operations are a separate contract `BilinearGen.Ops` `Pairing/Operations.lean:68` (`Pairing/Group.lean:281`) |
| `ArithmeticFP` | (hypothesis bundle) | `Candidates/Arithmetic.lean:314`; deviation "states each candidate result under this explicit hypothesis instead of building the machines" `:304–312` |
| **`IBEScheme`** | **no** | "typed probabilistic computations, without an efficiency requirement in the interface … efficiency of the encodings is deferred with that of the algorithms (ruling Q5)" `AdvancedEncryption/IdentityBased/Defs.lean:98–105`; `PairingCryptographyPlan.md:146–148` (D5), `:288–291` (Q5), `:391` (ruled), `:396` ("efficiency stays deferred (Q5)") |
| **`SecretSharing.Scheme`** | **no** | "[PS10] asks `Share` and `Recon` to be probabilistic polynomial-time; efficiency is not modelled here" `SecretSharing/Defs.lean:82–84` |
| **`LWE.Family`, `LWE.Noise`** | **no** | "`Family` and `DLWEAssumption` assert no efficient parameter generator, residue sampler or noise sampler" `LWE/Assumption.lean:47–51`, `:62–64`; "No efficient sampler is asserted" `LWE/Noise.lean:31`, `:40` |
| **`SIS.Family`** | **no** | "Efficient parameter generation, matrix sampling and implementation … remain separate construction obligations" `SIS/Assumption.lean:47–50`, `:64–65` |
| **`MultiEnc`** (garbling encryption) | no (typed) | `SecureComputation/Garbling.lean:139`; efficiency is covered inside Yao's `PolyTime` proof (§2.I) |
| **`BGW.Resharer` / `bgwEval`** | no (typed) | `MPC/BGW/Protocol.lean:67`, `:101` |
| Lattice schemes, Joux, Schnorr | no interface; typed functions | see §2 rows F, G, H7 |
| Garg concrete layer | no, by design | `GargCryptoPlan.md` foundation decision 1 (two layers); asymptotic counterparts carry efficiency |

## 2. Summary table

Abbreviations: AFP = `Candidates.ArithmeticFP`; "cheap AFP" = fields `mul`, `add`, `sub`,
`divMod`, `modExp`, `le`, `size` (see §4.1).

### A. One-way functions and collections ([PS10] ch. 2)

| # | Construction | File | Honest algorithms | Evidence / hypothesis / deviation | What it would take |
|---|---|---|---|---|---|
| A1 | OWF ⇒ collection (`FunFamily.toCollection`) | `Asymptotic/Collections.lean:468` | Gen **P** · Sample **P** · Eval **P** | `Collection` fields discharged by the construction | nothing |
| A2 | Weak ⇒ strong OWF (Yao amplification) | `Asymptotic/OneWay.lean:671` | Eval **P** | `Easy.prod` `Asymptotic/OneWay.lean:450` | nothing |
| A3 | Levin's universal OWF; quadratic-time family (Lemma 64.3) | `Asymptotic/Universal.lean:255`; `Asymptotic/UniversalPadding.lean:493` | Eval **P** | `fUniversal_easy` `Asymptotic/Universal.lean:439` takes `CanonizerExp c`, which is satisfiable: `exists_canonizerExp` `Asymptotic/Universal.lean:306` | nothing |
| A4 | Goldreich–Levin padded OWF and hard-core bit (families, collections) | `Asymptotic/HardCore/Functions.lean:358`, `:399`, `:477`; `Asymptotic/HardCoreCollection.lean:92` | Eval **P** · HC predicate **P** | `StrongOneWay.glPad` carries `easy`; `HardCore` demands the evaluator | nothing |

### B. Number-theoretic candidates (conditional by design: `PassShelatChapter2-4Plan.md:362`, D11)

| # | Construction | File | Honest algorithms | Evidence / hypothesis / deviation | What it would take |
|---|---|---|---|---|---|
| B1 | `f_mult` | `Candidates/Factoring.lean:233` | Eval **H** | AFP `mul` | cheap AFP |
| B2 | Factoring collection | `Candidates/Factoring.lean:1482` | Gen **P** (`factoringGen`, no coins, `:1422`) · Sample **H** · Eval **H** | sampler `:1416` uses `H.prime`; eval uses `H.mul` (`:1495`) | `prime` (blocked, §4.1) + cheap AFP |
| B3 | RSA trapdoor permutation / collection | `Candidates/RSA.lean:1307` | Gen **H** (`:1127`) · Sample **H** (`:1170`) · Eval **H** (`:277`) · Inv **H** (`:1189`) | AFP incl. `prime` (`:866`, `:876`) and `xgcd` (inverse mod Φ(N), a composite modulus) | `prime` + general modular inverse + cheap AFP |
| B4 | Rabin collection and Rabin–Blum TDP | `Candidates/Rabin.lean:1158`, `:2831` | Gen(odd) **H** (`:975`) · Gen(Blum) **H** (`:984`) · Sample(Rabin) **H** (`:1070`) · Sample(Blum) **H** (`:2411`) · Eval **H** (`:1059`) · Inv **H** (`:2617`) | AFP incl. `prime` (`:670`, `:676`) and `xgcd`. `BlumDensity` (`Implications/PublicKey.lean:97`) is a density hypothesis, not an efficiency one. | as B3 |
| B5 | Discrete-log collection (`expCollection`, `dlCollection`) | `Candidates/DiscreteLog.lean:798`, `:1126` | Gen **H** (obj: `expGen G` from `SafePrimeGen`) · Sample **H** (`expSampler` `:736`) · Eval **H** (`:287`) | AFP fields used: `le`, `modExp`, `size`, `sub` (no `prime`, no `xgcd`); the generator is a hypothesis object (`:320–325`) | cheap AFP + a bundle split (§4.2); generator: open problem [PS10, pp. 52–53] |
| B6 | Full-DL collection + hard-core bit of DL | `Candidates/DiscreteLogHardcore.lean:830`, `:2994` | Gen **H** (obj: `FullGroupGen` `:810`) · Sample **H** · Eval **H** · HC predicate **H** (`polyTimeComputable_halfStr` `:971`) | AFP `add`, `divMod`, `le`, `modExp`, `mul`, `sub`, `xgcd` (`:1032`; prime modulus) | cheap AFP + inverse mod a prime (Fermat via `powMod`) + split; generator open |
| B7 | El Gamal | `Encryption/PublicKey/ElGamal.lean:776` | Gen **H** (`egGen` `:578`, `SafePrimeGen` obj) · Enc **H** (`egEnc` `:697`) · Dec **H** (`:727`) | AFP `add`, `divMod`, `le`, `modExp`, `mul`, `size`, `sub`, `xgcd` (`:733`, inverse mod prime `p`); exponents by truncated rejection (statistical, D10) | as B6 |
| B8 | DL-based CRH (Protocol 142.2, `dlHash`) | `Hashing/FromDiscreteLog.lean:451` | Gen **H** (AFP + `ExpGroupGen` obj) · Eval **H** (`:430`) | AFP `divMod`, `mul` (the reduction also uses `add`, `sub`) | cheap AFP + split |
| B9 | PKE from RSA / factoring (`exists_adaptiveCPA_of_rsa`, `_of_factoring`) | `Implications/PublicKey.lean:79`, `:97` | inherits B3/B4 and E1 (not counted again) | AFP (+ `BlumDensity`) | as B3/B4 |

### C. Pseudorandomness ([PS10] ch. 3; Garg asymptotic layer; lattice)

| # | Construction | File | Honest algorithms | Evidence / hypothesis / deviation | What it would take |
|---|---|---|---|---|---|
| C1 | PRG from OWP + hard-core bit (`owpGenPRG`) | `Pseudorandom/Generators/Asymptotic/FromPermutation.lean:70` | G **P** | `exists_securePRG_of_owp` `:283`; `Secure` includes `Easy` | nothing |
| C2 | PRG stretch / truncation / doubling | `Pseudorandom/Generators/Asymptotic/Stretch.lean:397`, `:419` | G **P** | `prgIterFun_poly` `Pseudorandom/Generators/Asymptotic/StretchMachine.lean:86` | nothing |
| C3 | GGM PRF (asymptotic) | `Pseudorandom/Functions/Asymptotic/GGM.lean:68` | F **P** | `exists_ggmPRF_evaluator` `:91`; `ggmPRF_prf` `:321` | nothing |
| C4 | LWE-based PRG (`generate`, `generateBits`, `generateFlat`) | `Pseudorandom/Generators/LWE/Basic.lean:52`; `Pseudorandom/Generators/LWE/Bits.lean:44`; `Pseudorandom/Generators/LWE/Flat.lean:133` | G **D+S** | "no efficient generator or stretch claim is inferred" `Pseudorandom/Generators/LWE/Basic.lean:84`; implementation obligations `Pseudorandom/Generators/LWE/Basic.lean:40`, `Flat.lean` module doc; not a `PRG` instance. `+S` only for non-dyadic `q` or noise. | dyadic: string machine from `Encoding/DyadicLinearAlgebra` + bit-seed noise, or a word-RAM program via the bridge; non-dyadic: sampler bridge; then reindexing to `PRG` |

### D. Private-key encryption, MACs, signatures, hashing

| # | Construction | File | Honest algorithms | Evidence | What it would take |
|---|---|---|---|---|---|
| D1 | PRG pad scheme (Alg. 92.1) | `Encryption/PrivateKey/FromPRG.lean:167` | Gen **P** · Enc **P** · Dec **P** | `ofPolyTimeUniform` from the PRG evaluator | nothing |
| D2 | PRF scheme (Alg. 99.1) | `Encryption/PrivateKey/FromPRF.lean:191` | Gen **P** · Enc **P** · Dec **P** | as D1 | nothing |
| D3 | Fixed-length PRF scheme | `Encryption/PrivateKey/OracleFromPRF.lean:75` | Gen **P** · Enc **P** · Dec **P** | `FixedLengthScheme` fields | nothing |
| D4 | Encrypt-then-tag (Alg. 169.3) | `Encryption/PrivateKey/EncryptThenTag.lean:349` | Gen **P** · Enc **P** · Dec **P** | | nothing |
| D5 | Special encryption (Alg. 157.2, Yao) | `SecureComputation/SpecialEncryptionSecurity.lean:89` | Gen **P** · Enc **P** · Dec **P** | `SecureComputation/SpecialEncryption.lean:154`, `:214` | nothing |
| D6 | PRF MAC (Prot. 134.3) | `Authentication/MAC/FromPRF.lean:103` | Gen **P** · Tag **P** · Ver **P** | | nothing |
| D7 | Lamport one-time signature (Prot. 137.1) | `Authentication/Signatures/Lamport.lean:597` | Gen **P** · Sign **P** · Ver **P** | relative to the OWF evaluator `hE` (`:283`) | nothing |
| D8 | Hash-and-sign (Prot. 144.2) | `Authentication/Signatures/HashAndSign.lean:323` | Gen **P** · Sign **P** · Ver **P** | generic over `CRH` and `SignatureScheme` | nothing |
| D9 | SIS binary-matrix hash | `Hashing/SIS/Implementation.lean:89` | KeyGen **D+S** · Eval **P** | Eval: `polyTimeComputable_hashPoly` (dyadic `q`). KeyGen: "no automatic uniform-parameter or fair-bit sampler claim" `Hashing/SIS/Asymptotic.lean:34`. Not a `CRH` instance: "efficient machine adapters and the future generic CRH-owner bridge remain explicit consumer obligations" `Hashing/SIS.lean:32–33`. `+S` only for non-dyadic `q`; the explicit profile `dyadicFamily` (`Hashing/SIS/Profiles.lean:79`) is dyadic. | cheap for `dyadicFamily` (§4.3); non-dyadic `q`: sampler bridge |

### E. Public-key encryption, generic

| # | Construction | File | Honest algorithms | Evidence | What it would take |
|---|---|---|---|---|---|
| E1 | TDP bit encryption (Alg. 104.3, `tdpBitScheme`) | `Encryption/PublicKey/Trapdoor.lean:250` | Gen **P** · Enc **P** · Dec **P** | relative to `TrapdoorCollection` fields and the hard-core evaluator | nothing |
| E2 | Bitwise / padded fixed-length wrappers | `Encryption/PublicKey/EnsembleSecurity.lean:279`; `Encryption/PublicKey/OracleSecurity.lean:260` | Gen **P** · Enc **P** · Dec **P** | | nothing |

### F. Lattice assumptions and schemes (LWE/SIS campaign; GSW)

| # | Construction | File | Honest algorithms | Evidence / deviation | What it would take |
|---|---|---|---|---|---|
| F1 | LWE sampler (matrix, common secret, noise) | `LWE/Basic.lean:101`; bit form `LWE/Sampling.lean:48`; `LWE/BitNoise.lean:40`, `:78` | Sampler **D+S** | `LWE/Assumption.lean:47–51`; `LWE/Noise.lean:31`. Exact fair-bit laws exist only for `q = 2^w` (`Encoding/DyadicUniform.lean:46`, "no rejection sampler or approximation for odd moduli"). | dyadic: machine over the existing bit maps; otherwise sampler bridge |
| F2 | SIS sampler (uniform matrix) | `SIS/Assumption.lean:47–50` | = D9 KeyGen (not counted again) | | as D9 |
| F3 | Regev symmetric encryption | `Encryption/Symmetric/Regev/Basic.lean:58`, `:69` | KeyGen **D+S** · Enc **D+S** · Dec **D** | "Machine construction and the existing primitive-security bridge remain separate obligations" `Encryption/Symmetric/Regev/Basic.lean:23–24` | string or word-RAM programs (dyadic: `Encoding/DyadicLinearAlgebra.lean:445`, `Encoding/DyadicArithmetic.lean:122/205/322`) + sampler bridge + `PrivateKeyScheme` bridge |
| F4 | Regev PKE | `Encryption/PublicKey/Regev/Basic.lean:45`, `:66`, `:89` | KeyGen **D+S** · Enc **D** · Dec **D** | "no … efficient machine or existing primitive bridge" `Encryption/PublicKey/Regev/Basic.lean:34–35`; Enc uses binary coins (dyadic) | as F3, target `BitPublicKeyScheme` (§4.4) |
| F5 | GSW leveled FHE (incl. symmetric GSW) | `AdvancedEncryption/Homomorphic/GSW/Scheme.lean:102`, `:141`; `AdvancedEncryption/Homomorphic/GSW/Eval.lean:122`; `AdvancedEncryption/Homomorphic/GSW/Symmetric.lean:61` | KeyGen **D+S** (Regev keygen) · Enc **D** · Dec **D** · Eval **D** | "The asymptotic primitive bridge (`NUPPT` reductions, `BitPublicKeyScheme.SingleBitSecure`) is a separate unit" `AdvancedEncryption/Homomorphic/GSW/Security.lean:47–50` | word-RAM programs via the bridge (matrix products, `G⁻¹`) + sampler bridge + scheme bridge |
| F6 | GSW bootstrapping (phase 6) | not on this branch | (not counted) | 6b statements external; `LatticeCryptographyPlan.md:570`, `:588`. Reductions planned under `LeveledReductionEfficient`. | follow phase-6 rulings |
| F7 | Lossy TDF (concealed gadget) | `TrapdoorFunctions/Lossy/Matrix.lean:92`, `:60`, `:110`; sampler `TrapdoorFunctions/Lossy/Experiments.lean:50` | Gen **D+S** · Eval **D** · Inv **D** | "Polynomial-time implementations and CCA2 consumers remain separate obligations" `TrapdoorFunctions/Lossy/Matrix.lean:38–39`; modulus `2^(b+a)` is dyadic, `+S` from the general `Noise` | as F3 |
| F8 | All-but-one TDF | `TrapdoorFunctions/AllButOne/Basic.lean:59`, `:80` | Gen **D+S** · Eval **D** | facade `TrapdoorFunctions/AllButOne.lean:20–22` ("efficiency/security endpoints" separate) | as F3 |

### G. Pairing-based (pairing campaign)

| # | Construction | File | Honest algorithms | Evidence / deviation | What it would take |
|---|---|---|---|---|---|
| G1 | Bilinear group generator | `Pairing/Group.lean:283` | Gen **H** (obj) | `gen : NUPPT` by type; no instance (concrete curves out of scope, `PairingCryptographyPlan.md` scope); operations are the contract `Ops` `Pairing/Operations.lean:68` | not dischargeable abstractly |
| G2 | Joux one-round tripartite DH | `KeyExchange/Joux.lean:74`, `:82`, `:116` | Setup (`g ∈ G*`) **D+S** · Msg (`x ← Z_p`, `g^x`) **D+S** · Key (`e(X,Y)^x`) **D** | typed functions over abstract `BilinearGroup`; no efficiency field | `Ops` (`powG`, `pairStr`) + exponent sampling; word-RAM via bridge (b), which calls `Ops`; sampler bridge or `sampleBelowL` draws (statistical) |
| G3 | Boneh–Boyen BB1 IBE | `AdvancedEncryption/IdentityBased/BonehBoyen.lean:339` (`BB1.setup` `:126`, `keyGen` `:147`) | Setup **D+S** · KeyGen **D+S** · Enc **D+S** · Dec **D** | `IBEScheme` deviation `AdvancedEncryption/IdentityBased/Defs.lean:98–105`; Q5 deferral (`PairingCryptographyPlan.md:288–291`, `:391`); exponents and elements drawn by `ProbComp.sample` (`Games/Probability.lean:93`) over `Z_p`, `G`, `G*` | Q5 option (B): `IBEScheme.Efficient` + machines under `Ops` + AFP (reuse `AdvancedEncryption/IdentityBased/BonehBoyenMachine/Words.lean`, `Draws.lean`) or a word-RAM program; sampler bridge for exact laws |

### H. Commitments and zero knowledge ([PS10] ch. 4, 7)

| # | Construction | File | Honest algorithms | Evidence / hypothesis | What it would take |
|---|---|---|---|---|---|
| H1 | Commitment from OWP + hard-core (Thm 126.4) | `ZeroKnowledge/Commitment.lean:508` | Com **P** | `owpComStr_polyTimeComputable` `:873`; `owp_commitment` `:898` | nothing |
| H2 | Graph isomorphism protocol (single, repeated) | `ZeroKnowledge/GraphIsomorphism/Proofs.lean:320`, `:379` | Prover **P** · Verifier **P** | `ZeroKnowledge/GraphIsomorphism/Efficiency.lean:473`, `:509`; `ZeroKnowledge/GraphIsomorphism/EfficiencyRepGI.lean:110`, `:315` | nothing |
| H3 | Graph non-isomorphism protocol | `ZeroKnowledge/GraphIsomorphism/Proofs.lean:231`, `:284` | Verifier **P** (prover unbounded by definition) | `ZeroKnowledge/GraphIsomorphism/Efficiency.lean:561`; `ZeroKnowledge/GraphIsomorphism/EfficiencyRep.lean:609` | nothing |
| H4 | 3-colouring protocol | `ZeroKnowledge/ThreeColoring/Protocol.lean:469`, `:546` | Prover **P** · Verifier **P** | `colProver_efficient` `:569`, `colVerifier_efficient` `:584`, rep `:591`, `:599` (given `PolyTimeComputable Com`, a `Commitment` field) | nothing |
| H5 | ZK for NP via Levin reductions (Thm 124.1) | `ZeroKnowledge/NP.lean:573`, `:720` | Prover **H** · Verifier **H** | Given a `LevinReduction` the parties are efficient (`Strategy.pullback_efficient` `:249`). The NP-wide form assumes `LevinNPHard L3COL R3COL` (`:654`), whose maps must be polynomial-time (`:137`, `:139`). | a string-level Levin reduction with witness map to `3COL`. `TCSlib/Complexity/NPReductions/ThreeSATToColoring.lean` is graph-level; reuse is unclear. |
| H6 | Sequential repetition | `Composability/SequentialZK.lean:354` | Prover **P** · Verifier **P** | `seqProver_efficient` `:718`, `seqVerifier_efficient` `:727` | nothing |
| H7 | Schnorr identification | `SchnorrProtocol.lean:42–61` | Prover **D+S** · Verifier **D+S** | purely algebraic over `ZMod q` (`q` prime); no machine, not in the `Protocol` framework | port to `Protocol` + a group-operations contract (as `Ops`) + sampler bridge |

### I. Secure computation and secret sharing

| # | Construction | File | Honest algorithms | Evidence | What it would take |
|---|---|---|---|---|---|
| I1 | Oblivious transfer (Prot. 160.4) | `SecureComputation/ObliviousTransfer.lean:222` | Sender **P** · Receiver **P** | `otProtocol_polyTime` `:732` (`HBCSecure` demands `PolyTime`) | nothing |
| I2 | Yao's protocol (OT-hybrid and real), with garbling | `SecureComputation/Yao.lean:539`; `SecureComputation/YaoReal.lean:64` | Alice (garbler) **P** · Bob (evaluator) **P** | `yaoHybrid_polyTime` `SecureComputation/Yao.lean:863`; `polyTime_compose` `SecureComputation/ComposeSecurity.lean:371`; `yaoProtocol_hbcSecure` `SecureComputation/YaoReal.lean:95`; standalone `MultiEnc` is typed (`SecureComputation/Garbling.lean:139`) | nothing |
| I3 | Shamir secret sharing | `SecretSharing/Shamir.lean:101` | Share **D+S** · Reconstruct **D** | deviation `SecretSharing/Defs.lean:82–84`; uniform `F`-coefficients (`+S` unless `|F|` is a power of two) | field-arithmetic machines (prime fields: `BinaryArith`) + sampler bridge; only if a computational consumer needs it |
| I4 | BGW (semi-honest MPC) | `MPC/BGW/Protocol.lean:101` | Parties **D+S** | share-level function; resharing coins abstracted (`:67`) | protocol-model port + machines + sampler bridge |

### J. Randomness ([PS10] ch. 8)

| # | Construction | File | Honest algorithms | Evidence | What it would take |
|---|---|---|---|---|---|
| J1 | PRF concept class (Thm 179.1) | `Randomness/Learning.lean:109` | Concept evaluation **P** | `prfConcept_decidable` | nothing |
| J2 | Efficient source in the extractor impossibility (Thm 183.6) | `Randomness/Extraction.lean:312` | Source sampler **P** | `Randomness/Extraction/Sampler.lean` | nothing |
| J3 | Derandomization (Thm 180.1) | `Randomness/Derandomization.lean:113` | no honest party (not counted) | | — |

### K. Legacy

| # | Construction | File | Honest algorithms | Evidence | What it would take |
|---|---|---|---|---|---|
| K1 | Textbook RSA with `TimeM` cost annotations | `RSA.lean:497`, `:501` | Enc **D** · Dec **D** | **Orphan:** no file imports `TCSlib.Cryptography.RSA` (not in `TCSlib.lean`). `TimeM` annotations are trusted (`RSA.lean:19`). | retire, or leave; superseded by B3 |

### L. Not counted

- **Garg concrete layer.** `OneWayFunctions/`, `HardcoreBit/`, `Pseudorandom/Generators.lean`,
  `Pseudorandom/Functions/{Defs,GGM}.lean`, `Pseudorandom/GeneratorFromPermutation.lean`,
  `Pseudorandom/NextBit/Concrete.lean`. These are concrete by design and their asymptotic
  counterparts are P (rows A, C).
- **Assumption-only objects.** The DDH ensembles (`Candidates/DDH.lean:330`, `:341`) and the
  BDH/DBDH experiments (`Pairing/Assumptions.lean`) have no honest party of their own.
- **`Games/` framework.** Infrastructure only. `ProbComp.sample` (`Games/Probability.lean:93`)
  is the uniform sampler over an arbitrary finite type. It is where non-dyadic honest laws
  (rows F, G, I) enter, so the sampler bridge plugs in there.

## 3. Security reductions (not honest parties)

| Reduction | Status | Evidence | Note |
|---|---|---|---|
| BB1 ⇒ DBDH distinguisher | H (AFP + `G.Ops`) | `exists_bb1_distinguisher` `AdvancedEncryption/IdentityBased/BonehBoyenMachine.lean:104`; `bb1_sidSecure` `AdvancedEncryption/IdentityBased/BonehBoyenSecurity.lean:177`; exponents via `sampleBelowL` (`AdvancedEncryption/IdentityBased/BonehBoyenMachine/Draws.lean:23–29`) | AFP fields used: `add`, `divMod`, `le`, `mul`, `size`, `sub`, `xgcd` (`AdvancedEncryption/IdentityBased/BonehBoyenMachine/Words.lean`); no `prime`. `Ops` cannot be discharged abstractly. Recorded in `IOComponentsPlan.md:78`. |
| DL-hash collisions ⇒ DL | H (AFP) | `Hashing/FromDiscreteLog/Reduction.lean:77`, `:129`, `:305` | `add`, `divMod`, `sub` |
| Candidate reductions (factoring planting, RSA from factoring, DL hard-core inverter, El Gamal ⇒ DDH) | H (AFP) | `Candidates/Factoring.lean:752`; `Candidates/RSA.lean:2340`; `Candidates/DiscreteLogHardcore.lean:1963` ff.; `Encryption/PublicKey/ElGamal.lean:1130` | as rows B |
| ZK for NP | H (`LevinNPHard`) | `ZeroKnowledge/NP.lean:654`, `:720` | as H5 |
| Lattice reductions (Regev PKE, symmetric Regev, GSW, lossy TDF hybrids) | **D**: function-level distinguishers, no `NUPPT` bridge | `Encryption/PublicKey/Regev/Experiments.lean:105`; `AdvancedEncryption/Homomorphic/GSW/Security.lean:47–50`; `TrapdoorFunctions/Lossy/Experiments.lean:106` | The LWE PRG needs no reduction (`pseudorandom_under_DLWE`, `Pseudorandom/Generators/LWE/Basic.lean:84`). The SIS-hash postprocessor is P (`Hashing/SIS/CollisionOutput.lean:287`, used by `Hashing/SIS/Asymptotic.lean:71`). |
| All other [PS10] ch. 2–8 reductions and simulators | P (`NUPPT` machines) | handler machines `exists_handlerMachine` `Games/Efficiency.lean:332` (proved) | subject to global caveat 2 |

## 4. Cheapest wins

### 4.1 Discharge 7 of the 9 `ArithmeticFP` fields

All the parts already exist.

- **Machines.** `TCSlib/Complexity/ClassP/BinaryArith` proves, with no `sorry` in its sources:
  - `add` (`TCSlib/Complexity/ClassP/BinaryArith/AddSub.lean:162`), `sub` (`:239`), `le` (`:219`);
  - `mul` (`TCSlib/Complexity/ClassP/BinaryArith/Mul.lean:217`);
  - `div` (`TCSlib/Complexity/ClassP/BinaryArith/Div.lean:230`), `mod` (`:245`);
  - `powMod` (`TCSlib/Complexity/ClassP/BinaryArith/ModPow.lean:214`), `gcd` (`:348`).
- **Representation adapters.** These are already proved in `Encoding/BinaryArith.lean` and bridge
  `listToNat`/`natToList` (MSB-first, fixed width) to `Nat.bits` (little-endian):
  - `toLE`: `toLE_eq_natBits` `:72`, `polyTimeComputable_toLE` `:114`;
  - `normalizeWidthPoly`: `normalizeWidthPoly_pairEncode` gives `natToList (p |u|) (listToNat w)`
    (`:144`, polynomial-time at `:185`);
  - `fromLEPoly` (`:200`, `:282`).
- **Precedent.** `Encoding/DyadicArithmetic.lean` already composes these adapters into modular
  `add`/`mul`/`sub`.

**Cheap fields.** `mul`, `add`, `sub`, `divMod`, `modExp`, `le`, `size` need only glue: output
widths taken from input lengths, and edge cases at modulus 0. For example, `powMod` returns 0 when
`p = 0` (`TCSlib/Complexity/ClassP/BinaryArith/ModPow.lean`, "Divergences"), while `modExpStr`
truncates `a^x` to `|N|` bits. `size` is `Nat.bits` followed by a constant map.

**`xgcd`: moderate.** It needs `a⁻¹ mod b` for any `b`, and `BinaryArith` has only the gcd. The
options are an extended-Euclid loop on `polyTimeComputable_iterate`, or, at prime moduli only,
Fermat's inverse through `powMod`. The latter suffices for B6, B7 and the BB1 reduction, but not
for RSA's inverse mod Φ(N).

**`prime`: blocked.** The library has no deterministic polynomial-time primality test, only
`PRIMES ∈ coRP` (Solovay–Strassen, `TCSlib/Complexity/Randomized.lean:117`). Swapping in a
randomised test would break the every-coin `sample_spec` of the factoring, RSA and Rabin samplers.

### 4.2 Split the bundle (needs a ruling)

`ArithmeticFP` is all-or-nothing, so 4.1 alone makes nothing unconditional. D11 is frozen
(`PassShelatChapter2-4Plan.md:361–362`). A core sub-bundle (cheap fields), with `xgcd` and
`prime` separate, would make several results conditional only on cryptographic and
hypothesis-object assumptions:

- B5 and B8, and the DL-hash reduction, use no `prime` and no `xgcd`. They would then be
  conditional only on their hypothesis-object generators.
- B6, B7 and the BB1 reduction would follow after adding the prime-modulus inverse.

Owner: [PS10] ch. 2–4 campaign, now with the ch. 5–8 maintainer (`PassShelatChapter2-4Plan.md:375`).

### 4.3 SIS hash as a `CRH` for `dyadicFamily`

Eval is already **P** (`Hashing/SIS/Implementation.lean:89`). Gen at modulus `2^(κ+1)` is a
pass-through of `N·M·W` fair coins (exact law, `Encoding/DyadicUniform.lean`). Collision
resistance is already bounded (`dyadic_collision_negligible`, `Hashing/SIS/Asymptotic.lean:116`).

What remains is CRH glue: `inDom`/`inRange` tests, the `⟨1^n, ⟨i, x⟩⟩` layout, and matching
`collisionGame` to `collisionAt`. `LatticeCryptographyPlan.md:506` records SIS CRH fills cleared at
Gate 14. That is on the lattice campaign's own branch; whether it landed anywhere is **unclear**
from this branch.

### 4.4 Regev PKE at a dyadic modulus with bit-seed noise (moderate)

`matVecPoly` (`Encoding/DyadicLinearAlgebra.lean:445`), modular arithmetic
(`Encoding/DyadicArithmetic.lean`) and `expandPoly` (`Encoding/BooleanVector.lean:189`) already
cover key generation (`As + e`), subset-sum encryption and decryption as string machines, with
no word-RAM needed. The remaining pieces are:

- a polynomial-time `bitNoise` profile, such as `centeredNoise` (`LWE/BitNoise.lean:78`);
- the `BitPublicKeyScheme` bridge, already planned (`AdvancedEncryption/Homomorphic/GSW/Security.lean:47–50`).

GSW, the LWE PRG and the lossy TDF follow the same route, with more matrix work.

### 4.5 BB1 and Joux under `Ops` + AFP: Q5 option (B) (moderate; needs a ruling)

The reduction already builds the needed string functions (`AdvancedEncryption/IdentityBased/BonehBoyenMachine/Words.lean`) and
coin-block draws (`AdvancedEncryption/IdentityBased/BonehBoyenMachine/Draws.lean`). Honest-party machines could reuse them under an
`IBEScheme.Efficient` predicate (`PairingCryptographyPlan.md:290–291`).

`sampleBelowL` gives statistically close draws, not exact ones. The fallback must keep correctness:
`g ∈ G*` needs a non-identity fallback.

Alternatively, these become word-RAM programs over deliverable (b) of the planned bridge
(`IOComponentsPlan.md:80`). That bridge is held pending another branch's API
(`IOComponentsPlan.md:79`).

### Incidental (not efficiency; static observations only)

- `Encryption/PrivateKey.lean:66`, `:71` say `prfFixedScheme_cpa`/`_cca1` and `ccaScheme_cca2`
  are "pending". The theorems exist with tactic proofs and no `sorry`
  (`Encryption/PrivateKey/OracleFromPRF.lean:414`, `Encryption/PrivateKey/EncryptThenTag.lean:668`).
- `SecureComputation/YaoReal.lean:42–43` says the result rests on "their `sorry`s".
- `Pseudorandom/Generators/LWE.lean:22`, `TrapdoorFunctions/Lossy.lean:22` and
  `TrapdoorFunctions/AllButOne.lean:20` say statements are "admitted".
- These four docstrings look stale, but they were not checked against a build.

## 5. Counts

Count of bold status tokens in §2 (116 honest algorithms):

| Status | Count | Rows |
|---|---|---|
| P | 56 | A1–A4, B2 (Gen), C1–C3, D1–D8, D9 (Eval), E1–E2, H1–H4, H6, I1–I2, J1–J2 |
| H | 28 | B1–B8 (25: AFP; B5–B8 also need an unconstructed group generator), G1 (1, obj), H5 (2, `LevinNPHard`) |
| D | 32 | C4, D9 (KeyGen), F1, F3–F5, F7–F8, G2–G3, H7, I3–I4, K1 |
| of which +S | 18 | always non-dyadic (prime order): G2 (2), G3 (3), H7 (2), 7 in total. Non-dyadic only for odd `q` or general noise: C4, D9, F1, F3 (2), F4, F5, F7, F8, 9 in total. Depends on `\|F\|`: I3, I4, 2 in total. |

Of the 25 AFP entries:

- 12 sit in rows that use `prime`: B2 (2), B3 (4), B4 (6).
- 1 is B1, which uses only `mul` but takes the whole bundle.
- 12 are in B5–B8 (3 + 4 + 3 + 2). They use no `prime`, but they also rest on unconstructed
  generators.

## 6. Campaigns and owners (as recorded)

| Rows | Campaign | Record |
|---|---|---|
| A, B1–B7, C1–C3, D1–D3, E, H1–H6, `ArithmeticFP` | [PS10] ch. 2–4. Original owner left the branch; handed to the ch. 5–8 maintainer on 2026-11-05. | `PassShelatChapter2-4Plan.md:375`; D11 `:362` |
| B8–B9, D4–D8, I1–I2, J, ch. 7 composability | [PS10] ch. 5–8 (maintainer, records branch) | `PassShelatChapter5-8Plan.md`; HBC efficiency ruling `:259` |
| C1–C3 asymptotic layer; concrete layer (§2.L) | Garg ch. 1–3 | `GargCryptoPlan.md` |
| G1–G3, BB1 reduction | Pairings (Seyoon approves; maintainer runs) | `PairingCryptographyPlan.md` (Q5 `:288–291`, `:391`) |
| C4, D9, F1–F4, F7–F8 | LWE/SIS constructions (central branch `cryptography/lwe-sis-constructions`) | `LatticeCryptographyPlan.md` (D2 `:250–262`, D7 `:357–364`) |
| F5–F6 | GSW (phase 5 done here; phase 6 under way) | `LatticeCryptographyPlan.md:507`, `:538`, `:570`, `:588` |
| sampler bridge; word-RAM bridge | iO components (in-house sampler bridge; RAM bridge held on another branch) | `IOComponentsPlan.md:34–46`, `:78–80` |
| I3 | unclear: [PS10] Def 152.1 is cited and `SecretSharing/` was touched at ch. 5–8 Gate 01 (commit `16e2bd02f`) | — |
| I4, H7, K1 | none recorded (legacy files, 2026-07 to 2026-09) | — |
| Arora–Barak (`TCSlib/Complexity/`) | no crypto primitives found. It supplies machine infrastructure only (`BinaryArith`, `NPReductions`, `CookLevin`); no edits proposed. | — |

## 7. Unclear (not determined statically)

1. The axiom closure of every **P** row and of `BinaryArith`, given the MIG-1 stage S sorried
   witness specs (§0, caveat 2).
2. Whether the SIS-CRH fills of `LatticeCryptographyPlan.md:506` exist on another branch.
3. Whether `TCSlib/Complexity/NPReductions/ThreeSATToColoring.lean` can serve as the string-level
   Levin reduction that `LevinNPHard` needs (H5).
4. The campaign owner of `SecretSharing/` and `MPC/BGW/`.
5. The API names of the word-RAM bridge being built on another branch (`IOComponentsPlan.md:79`).
