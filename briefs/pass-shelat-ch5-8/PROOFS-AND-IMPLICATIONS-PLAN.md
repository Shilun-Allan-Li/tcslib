# Pass–shelat proof and Implications plan

Planning base `0cb228f06ae56e91bc903cae801e49db73e0ae23` on `cryptography/pass-shelat-ch2-4`, after the merge of
[#282](https://github.com/Shilun-Allan-Li/tcslib/pull/282). This is the proof
roadmap for chapters 2–4 and the additional encryption material. The proof,
interface, and catalog PRs target the campaign branch. Revisit a release to
`main` after the selected proofs and the release-scope seals are complete.
Secure computation reorganization remains a later layout phase.

## 1. Refresh the proof prerequisites

Pin each proof batch to the current source, its dependency closure, and the
frozen statement headers. Use the [#248 acceptance record](maintainer/cleanup-incremental-2026-11-09/final-r1/README.md)
and the relocation records to identify retained reads and their current
owners. The [earlier dependency screen](maintainer/proof-dependency-screen-2026-11-08/README.md)
predates #248 and the import moves. Repeat it on the intended base before
assigning work, then inspect the actual reader dependencies of each route.

Start with the [efficiency draft](fills/efficiency/brief-draft.md). Its
candidate prerequisites now have public names in
[`PPT`](../../TCSlib/Complexity/Randomized/PPT.lean) and
[`Functions.Asymptotic.Defs`](../../TCSlib/Cryptography/Pseudorandom/Functions/Asymptotic/Defs.lean).
Probe `NUPPT.coinLen_eq` and the complete `decodeOracleMove` case split,
including malformed words and wrong-length payloads. Check the shared
`decodeFin_eq_some_iff` reader and the existing GGM loop equations at their
current owners. Run the toy handler and zero-width codec probes specified
in the draft. Record which providers are ready and request a scoped ruling
if an efficiency fill would need a dependency with unresolved cleanup reads.
The [cleanup plan](CLEANUP-PLAN.md#3-close-the-inherited-seal-ledger-on-the-new-layout)
continues to govern the full seal pass.

In parallel, preflight the fixed-length PRF CCA2 separation and the two Levin
proofs below. The separation sketch uses a directly constructed uniform
adversary. It is the first candidate for a small independent proof PR if
its reader and ownership checks pass. Endpoint statement design can proceed
alongside these probes.

## 2. Fill the existing proofs

The Gate 06 encryption headers landed in
[#232](https://github.com/Shilun-Allan-Li/tcslib/pull/232). Fill the frozen
statements through their published interfaces. Route changes can refresh
the proof sketch. A substantive statement change gets a separate audit.

| Batch | Targets and dependencies |
| --- | --- |
| Shared machine reductions | Fill `exists_handlerMachine` (T1), `exists_interactiveHandlerMachine` (T2), `exists_toCompOn_of_toComp` and `exists_toOracleAdversary_of_bitCodec` (T4). Prioritize the plain handler for public-key CPA. The interactive handler, input-free companion and codec transport are the route in the private-key CPA and CCA sketches. Reuse the GGM loop and check the resulting machine's run law, coins, and query budget. Keep one owner for the batch. [Source](../../TCSlib/Cryptography/Games/Efficiency.lean) · [Design](design/S2b-efficiency.md) |
| Private-key oracle security | Fill `prfFixedScheme_not_cca2` as the independent candidate. Then prove `prfFixedScheme_cpa` and `prfFixedScheme_cca1` using the checked handler and codec path. Fill `ccaScheme_cca2` after CPA and the shared reductions pass. The tagged proof needs the first-discrepancy bound and exact challenge refusal in its game. Check that the derived `not_prfFixedScheme_cca2` also has only standard axioms. [Fixed-length PRF scheme](../../TCSlib/Cryptography/Encryption/PrivateKey/OracleFromPRF.lean) · [Encrypt-then-tag](../../TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag.lean) |
| Public-key CPA bridge | Fill `BitPublicKeyScheme.SingleBitSecure.padded_cpa` after T1 or a checked equivalent route. Preserve the padding bound, the public-key-dependent message choice, and the machine run agreement. Recheck `TrapdoorCollection.tdpBitScheme_padded_cpa`, which inherits the bridge. This is the CPA dependency for the first catalog route. [Oracle security](../../TCSlib/Cryptography/Encryption/PublicKey/OracleSecurity.lean) · [Trapdoor corollary](../../TCSlib/Cryptography/Encryption/PublicKey/TrapdoorCPA.lean) |
| Public-key non-malleability | Prove `indSecure_cca2_iff_nmSecure_cca2`, `nmSecure_of_simNMSecure`, and `simNMSecure_of_nmSecure_cpa` against the audited formulations. Check which shared handlers each proof needs and preserve the attack quantifiers and simulator interface. Recheck the derived simulation/IND non-malleability equivalence at CPA. [Indistinguishability](../../TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Indistinguishability.lean) · [Simulation](../../TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation.lean) |
| Levin universal one-way function | Scope two machine proofs separately. `PadQuad.exists_linearTime_gStr` needs a registered or reused construction with the exact linear time bound on all inputs. Its completion clears the admission in `lemma_64_3` and then `theorem_63_1`. `exists_canonizerExp` needs a concrete `EffectiveMachineCode` and a bound for its canonizer, including malformed inputs. The conditional Levin theorems keep their stated `CanonizerExp` premise. [Padding machine](../../TCSlib/Cryptography/Asymptotic/UniversalPadding.lean) · [Canonizer and theorem](../../TCSlib/Cryptography/Asymptotic/Universal.lean) |

The shared reductions and the public-key CPA bridge are the proof critical
path for the CPA route. The non-malleability and Levin batches can advance
on their own owners when the dependency screen clears. The chapter 2–4
statement audits `03d`, `03h`, `03i`, `03j`, and `03k` still need restaging
on current owners after their recorded prerequisites. [Audit status](MAINTAINER-HANDOFF.md#6-current-state-verified-at-codex-intake-2026-11-06-pst)

### Additional proof packages

- The optional `NUPPT.decides_of_decidesWithAdviceInTime` bridge needs a
  clocked simulation with agreement on the well-formed advised inputs.
  Decide its release scope separately from the two Levin targets.
  [Advice bridge](../../TCSlib/Complexity/Randomized/NonUniform.lean)
- Queue `prfMAC_secure`, `lamport_oneTimeSecure`, `hashAndSign_oneTimeSecure`,
  and `dlHash_crh` as authentication and hashing work. The current sketches
  put the PRF-MAC after the interactive handler and codec path, Lamport after
  the plain handler, and hash-and-sign after its plain and interactive
  reductions. Check the generic hash-and-sign result and its Lamport
  composition separately. Screen the discrete-log hash proof as its own
  route. [MAC](../../TCSlib/Cryptography/Authentication/MAC/FromPRF.lean) ·
  [Lamport](../../TCSlib/Cryptography/Authentication/Signatures/Lamport.lean) ·
  [Hash-and-sign](../../TCSlib/Cryptography/Authentication/Signatures/HashAndSign.lean) ·
  [Discrete-log hash](../../TCSlib/Cryptography/Hashing/FromDiscreteLog.lean)

## 3. Define and prove the Implications endpoints

The selected public-key endpoints are **multi-message IND-CPA** and
**multi-message IND-CCA2**. CCA1 remains an intermediate. The final
theorems in `Cryptography/Implications/PublicKey.lean` start from explicit
sets of assumptions and produce a correct, efficient scheme with the chosen
security guarantee and a meaningful message space. Publish the game and
supporting proofs with their scheme owners and keep the catalog proofs as
short compositions through those interfaces.
[Implications design](implications/README.md)

### Settle the shared statement

Use `FixedLengthPKScheme` as the initial interface candidate. It already
packages uniform efficient key generation and encryption, efficient
decryption, and perfect correctness. Require a substantive message
space such as `n`-bit messages at positive security parameters, or state
the exact alternative and its size guarantee.

Propose a multi-challenge left-or-right experiment with one public key and
one hidden bit. An efficient adversary chooses pairs within a polynomial
query budget, and each challenge encryption uses fresh coins. Gate the
exact adversary and query semantics, including the one-challenge
specialization and how CCA2 handles adaptive decryption and all challenge
ciphertexts in the transcript. Bring the message-space and game choices
to Seyoon for a ruling before freezing the interface. The statement review
should cover repeated ciphertexts, malformed queries, and budget boundaries.
Publish the exact reduction and its machine cost before using the game in a
catalog theorem.
The existing `PublicKeyScheme.MultiMessageSecure` fixed-vector theorem
remains available in its own model.
[Fixed-vector game](../../TCSlib/Cryptography/Encryption/PublicKey/EnsembleSecurity.lean) ·
[Single-challenge oracle game](../../TCSlib/Cryptography/Encryption/PublicKey/OracleSecurity.lean)

### Deliver the CPA pilot first

1. With the public-key CPA bridge, package a meaningful fixed-length
   message scheme. Reuse the bitwise machinery where its contract applies.
   Check padding and unpadding, uniformity and fresh coins, and prove the
   transport to the audited oracle game, including the polynomial
   multi-challenge lift.
2. Develop the RSA/Rabin width transport in parallel. Gate a shared
   constant-shift collection contract and prove the generator, sampler
   and inverter run laws, closeness and one-wayness transports, and the
   candidate width equations. The design uses `n+2` for RSA and `n+3` for
   Blum Rabin to obtain exact `PolyExpr` widths. Reuse the existing
   negligibility and machine reparameterization facts. Move the general
   `Negligible.comp_of_le` to Foundations with its existing name and
   verify its consumers before lower-layer collection code uses it.
   Then compose Goldreich–Levin and the audited CPA endpoint.
   [Normalization design](implications/normalization-design.md)
3. Land the RSA composition first, then reuse the transport for Rabin.
   Keep `ArithmeticFP` and `RSAAssumption` explicit for RSA, and
   `ArithmeticFP`, `FactoringAssumption` and `BlumDensity` explicit for
   Rabin. Check each exact witness and all dependencies with `#print axioms`
   before exporting it. The catalog entry is the assumption-to-primitive
   theorem. The trapdoor and bitwise lemmas support it.
4. Follow with ElGamal after proving the message and game transport from
   `GroupPKScheme`. Retain its safe-prime generator, DDH and exceptional
   probability premises. For LWE, coordinate the parameter, correctness,
   efficiency and oracle-game bridges with the lattice owners. The
   existing finite Regev correctness and advantage theorems can be
   documented at their actual proved scope while that work proceeds.
   [ElGamal](../../TCSlib/Cryptography/Encryption/PublicKey/ElGamal.lean) ·
   [Lattice plan](../../LatticeCryptographyPlan.md)

### Treat public-key CCA2 as a construction milestone

Design the CCA2 candidate after the shared endpoint statement is settled.
Bring a source-backed route and its dependency list to Seyoon for a ruling
before freezing the construction. The lattice plan's lossy/all-but-one
trapdoor route is one candidate. Its review must identify the exact lossiness
and inversion contracts, a
strongly unforgeable one-time signature with compatible parameter widths,
and a correctness guarantee that fits the scheme record. Keep every
auxiliary assumption explicit. An LWE-only implication needs a proved
discharge of the signature and any other supporting assumptions. Once a
route is chosen, gate its statements, prove correctness and security,
and check the CCA2 multi-challenge transport including challenge
ciphertext exclusion. The public-key non-malleability equivalences belong
to their relation proofs in section 2. The tagged construction belongs to
private-key encryption. [Lattice CCA2 design](../../LatticeCryptographyPlan.md#d6-cryptographic-trapdoors-and-cca2)

## 4. Review and land each slice

For each proof or endpoint PR, record the exact source, target headers,
owner and approved dependencies. Apply the [repository policy](../../policy.md)
for new shared hosts, attribution, public equations, and proof sketches.
Check affected modules serially with `scripts/lean_check_tree.sh`, including
the relevant facade, `TCSlib` and campaign Checks. Use instance-aware seals
and sensitivity controls for affected declarations, and inspect explicit
and generated foreign reads. Compare declaration types and actual axiom
sets through each new proof and its advertised corollaries. A completed
catalog entry has a checked nonvacuous witness, the audited game, and
standard Lean axioms only.

Before preparing an external audit or fill, record Seyoon's Codex or Claude
choice. Seyoon dispatches and merges. Keep each proof batch on a reviewable
campaign PR and update the decision log after verification. Close the
remaining release-scope seal ledger on the settled source before preparing
a `main` candidate.
