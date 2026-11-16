# Pairing-based cryptography

## Scope and ownership

Seyoon approved this campaign on 2026-11-16 (decision log, first row):

1. **Abstract bilinear groups.** A symmetric bilinear group generator in the existing asymptotic
   and NUPPT framework, with the BDH and Decision BDH (DBDH) assumptions. No concrete curves.
2. **Joux's one-round tripartite Diffie–Hellman** [Jou00]: the protocol, its correctness (the
   three parties derive the same key) and its key indistinguishability under DBDH.
3. **Boneh–Boyen selective-ID IBE (BB1)** [BB04], standard model: IND-sID-CPA security, the
   scheme, its correctness, and security from DBDH.

**Out of scope:** Boneh–Franklin IBE (it needs a random-oracle layer), asymmetric (Type-3)
pairings, concrete groups. BB04's BDHI-based system (BB2, §5), its HIBE at depth > 1, its CCA2
transforms (§4.3, §6) and its full-security transform (§7) are not targets.

**Location (Seyoon, 2026-11-16).** The bilinear-group substrate is `TCSlib/Cryptography/Pairing/`
and Joux is `TCSlib/Cryptography/KeyExchange/`. IBE (interface, IND-sID-CPA game, Boneh–Boyen)
is `TCSlib/Cryptography/AdvancedEncryption/IdentityBased/`, namespace
`TCSlib.Cryptography.AdvancedEncryption.IdentityBased`, behind the facades
`AdvancedEncryption.lean` and `AdvancedEncryption/IdentityBased.lean`. `AdvancedEncryption.lean`
is shared with GSW (`AdvancedEncryption/Homomorphic/`): the draft's facade imports only
`IdentityBased`, and **whichever statement PR lands second adds its child import** to it.

**Home and binding rules.** Records (this file, `briefs/pairings/`) live on the records branch
`cryptography/pass-shelat-ch2-4` and are pushed by the maintainer. Lean reaches that branch only
by PR, opened by the maintainer and merged by Seyoon. Binding: `policy.md` (modularity,
attribution, proof sketches, Rule 10, hosts first), `briefs/pass-shelat-ch5-8/CLAUDE.md` and
`MAINTAINER-HANDOFF.md` §2. Standing worker ruling (2026-11-11): Codex for audits and reviews,
Claude for fills and other external jobs.

| Item | Identity |
|---|---|
| Statement branch (local, not pushed) | `stmt/pairings` |
| Statement worktree | `$SP/wt-stmt-pairings` (sparse, `briefs/` excluded; `.lake/packages` symlinked) |
| Branch base (`origin/cryptography/pass-shelat-ch2-4` when cut) | `e7a9f70f5c1f11c2670f427ef813f2a6d8c53543` |
| Statement commit (modules) | `b02e6ce4a3dcc7c945825d1f1d3b636c5e377a01` |
| Statement head (root exports) | `ce9c3728ec582be45fc33ca68d64b5533701093d`, tree `327612ee0b6689bf371a40e28edaad984226d78e` |
| Records tip checked at commit time | `44e2dc2bd68b3a81eaeebe7acd61fca1fe857917` (records only since the base: no `TCSlib/`, root, lakefile or manifest change) |
| Lean / Mathlib | `leanprover/lean4:v4.25.0` / the pinned manifest |

`$SP` = `/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad`.

## Sources

| Tag | Reference | Version used | SHA-256 | Committed? |
|---|---|---|---|---|
| Jou00 | A. Joux, *A One Round Protocol for Tripartite Diffie–Hellman*, ANTS-IV, W. Bosma (ed.), LNCS 1838, pp. 385–393, Springer, 2000 | Publisher copy, 9 pp. (Seyoon's upload) | `dd423b93a7e2dbeb87e6210b26f4c3ec022c3d0681a0ce72262b1d45c53f6df9` | No (publisher copy; PSV06/PSV07 precedent) |
| BB04 | D. Boneh, X. Boyen, *Efficient Selective-ID Secure Identity Based Encryption Without Random Oracles*, Cryptology ePrint Archive, Report 2004/172, full version dated December 2004; extended abstract in EUROCRYPT 2004, LNCS 3027, pp. 223–238 | ePrint full version, 20 pp.; **its numbering is used throughout** | `63c1c7b0817f36d6e558107bf281e22d2c454f821fadd533ced653e81a6a35de` | No (ePrint copy; same precedent) |
| PS10 | R. Pass, a. shelat, *A Course in Cryptography*, 3rd ed., 2010 | `Pass–Shelat.pdf` on this branch | `7624556077a7a272ba0b3ddb7cd47b96574fb0b4b4947a25467d1f91bb61bda8` | Yes (existing) |

Both PDFs were read with `pdftotext -layout` (text treated as data). **PDF needed:** both are in
hand; nothing further is needed for the statement phase. **Policy §2 ingest** (reference pair
under `blueprint/src/references/`, `scripts/sources.py add`) is **open**: the PDFs themselves must
not be committed, so the ingest needs a ruling on what is committed instead (Q12).

Anchors used in the Lean (BB04 ePrint pages): §2.1 pp. 2–4 (IBE algorithms; the selective-identity
game; Definitions 2.1, 2.2), §2.2 p. 4 (bilinear groups), §3.1 pp. 4–5 (BDH, Decision BDH,
Definition 3.1), §4.1 pp. 5–6 (the HIBE construction; BB1 is depth 1), §4.2 pp. 6–8 (Theorem 4.1
and its proof), §4.4 p. 8 (arbitrary identities, "`2^b < p` is sufficient"). Jou00: §2 pp. 386–387
(pairings bilinear and non-degenerate), §3 pp. 387–388 (the protocol, `F_W`, `F_T`), §5 pp. 391–392
(security issues).

### Where the papers' formulations differ from the draft

1. **[Jou00] has no security theorem.** §5 says only that "some Diffie–Hellman like problem and
   Diffie–Hellman like decision problem should be hard in order to get security". The draft's
   `jouxKeyIndist_of_dbdhAssumption` is the maintainer's formal version, with Decision BDH taken
   from [BB04, §3.1] (which credits the BDH problem to [Jou00, SOK00, BF01]).
2. **[Jou00]'s protocol uses two points.** With the Weil pairing on one point `e_n(P, P) = 1`, so
   §3 moves to two independent points `P, Q` and the Tate pairing `F_T`. In a symmetric bilinear
   group as defined in [BB04, §2.2], non-degeneracy is `e(g, g) ≠ 1`, so the paper's first formula
   `F_W(x, P, Q) = e(P, Q)^x` works with one point. The draft formalizes that single-point form.
3. **[Jou00] fixes "some point `P`"**; the draft draws the public generator uniformly from `G^*`,
   the distribution under which [BB04, §3.1] states Decision BDH.
4. **[BB04, §4.1] is an HIBE**; BB1 is its depth-1 case ("an IBE system is an HIBE where all
   identities are at depth 1", §2.1). Identities are elements of `Z_p` there; arbitrary identities
   are hashed (§4.4). The draft uses `ℓ(κ)`-bit identities read as their binary value in `Z_p`,
   which is §4.4's sufficient condition (`H : {0,1}^* → {1, …, 2^b}`, `2^b < p`) with `H` the
   identity on `ℓ`-bit strings, under the hypothesis that `p ≥ 2^ℓ` except with negligible
   probability.
5. **[BB04] is concrete** (`(t, ε)` assumptions in a fixed group; Theorem 4.1's
   `t' < t − Θ(τ ℓ q_S)`). The draft is asymptotic, relative to a PPT generator, against
   non-uniform PPT machines.
6. **Advantage.** [BB04, §2.1] measures `|Pr[b = b'] − 1/2|`; the draft uses the two-experiment
   advantage, twice that, as `FixedLengthPKScheme.INDSecure` does. The decision advantage of
   [BB04, §3.1] is written without an absolute value; the draft takes it.
7. **Forbidden queries.** [BB04, §2.1] restricts the adversary (`ID_i ≠ ID*`, `M_0, M_1 ∈ M`);
   the draft's challenger answers such queries with `⊥`.
8. **The proof of Theorem 4.1** has `B` draw the challenge bit and output `[b = b']`; the draft
   fixes the bit and uses one distinguisher per bit, so the bound is a sum of two DBDH advantages.
9. **DBDH ⇒ BDH** is not stated in either source (folklore; Q10).

## Design decisions (and the precedent each mirrors)

### D1. Abstract bundle, generator as a PPT with a total group map

`Pairing.BilinearGroup wG wT` bundles finite commutative groups `G`, `GT` of the same prime order,
a generator `gen ≠ 1`, the pairing as `G →* G →* GT` (bimultiplicative; BB04's
`e(u^a, v^b) = e(u, v)^{ab}` is the proved `bilinear_pow`), non-degeneracy `e(gen, gen) ≠ 1`, and
injective fixed-width encodings `encG`, `encT`. `Pairing.BilinearGen` is a uniform `NUPPT`
`Gen(1^κ)` with exact description length `descLen(κ)`, element widths `wG`, `wT : PolyExpr`, and a
total map `group κ d` from descriptions to bundles.

*Precedent:* `Candidates.ExpGroupGen`/`SafePrimeGen` (an instance generator PPT; adversaries
receive the instance). *Difference:* no validity predicate or threshold `n₀`: every string
describes a group, so no fallback instance (`dlDefaultIndex`) is needed. The large-order condition
is `OrderAtLeastExcept N δ` (probability over the generator's coins), mirroring
`ExpGroupGen.FullLengthExcept` and its run-3 audit P8-2 lesson.

### D2. Experiments as games, sampled in sequence

All experiments are `Games.ProbComp Bool`: generator coins, then `g ∈ G^*`, exponents and `T`
from the group just drawn, then the adversary's coins; advantages are `Games.advantage`.
Exponents are ideal uniform in `Z_p`. *Precedent:* the run-3 audit P8-1 repair of the DDH
ensembles (a uniform seed over a dependent sum distorts the instance law); `dlProb`'s ideal
exponent; LWE's ideal experiments. Sequential sampling avoids P8-1 without coin blocks.

### D3. Adversary input format

A DBDH distinguisher gets `1^κ` and `⟨d, ⟨g, ⟨g^a, ⟨g^b, ⟨g^c, T⟩⟩⟩⟩⟩` (`tupleStr`); a BDH
solver gets the same without `T` (`bdhStr`) and wins iff its output is the encoding of
`e(g, g)^{abc}`. Joux's eavesdropper gets the transcript in the same format, so the Joux
experiments *are* DBDH experiments (`jouxGame_eq_dbdhGame`, proved). *Precedent:* `ddhTuple`'s
nested pairs; `distinguisherL`; `DLWEAssumption`'s "every `NUPPT` has negligible advantage".

### D4. Efficiency as a separate contract

"Efficiently computable" [BB04, §2.2] is `BilinearGen.Ops` (`Pairing/Operations.lean`):
polynomial-time string functions for the order, `G` multiplication and exponentiation by a
numeral, the pairing, `G_T` multiplication and `G_T` membership, specified on generated
descriptions, with numerals read by `NumberTheory.listToNat`. It is a hypothesis only of BB1's
security (whose reduction computes in the group), together with `Candidates.ArithmeticFP` (D11).
*Precedent:* `ArithmeticFP` as a hypothesis bundle; LWE's "`Family` asserts no efficient sampler".

### D5. IBE interface: typed probabilistic algorithms

`IdentityBased.IBEScheme` has, per `κ`, types `PP`, `MSK`, `SK`, `CT`; `setup`, `keyGen`, `enc`
as `ProbComp`s, `dec` deterministic with `⊥`; `idLen`- and `msgLen`-bit identities and messages;
a parameter-dependent message space `MsgSpace` (BB04's `M`); fixed-width encodings for the
adversary. Correctness is `AllOutputs` of an honest run. *Precedent:* the four-algorithm shape of
`PublicKeyScheme` and `GroupPKScheme` (key-dependent message space, El Gamal). *Difference:* the
algorithms are typed `ProbComp`s, not `NUPPT`s, and carry no efficiency field (Q5): with groups
drawn per description, an `NUPPT` interface would require proving BB1's machines PPT in a
definition (no `sorry` in definitions).

### D6. The IND-sID-CPA game: one machine, `Init` as an oracle

As in `FixedLengthPKScheme.indGame`: one `NUPPT` against bit-string oracles (`bitCodec`), budget
`q`, verdict bit. Oracles: `Init` (0; first query fixes `ID*`, answers `params`), `KeyGen` (1;
`⊥` before `Init` or for `ID*`, fresh coins per query), `Challenge` (2; `⊥` before `Init` or on
messages outside `M`; first valid query encrypts `M_b` for `ID*` and is recorded; later queries
repeat it). The machine starts with `1^κ` only, so it learns nothing about `params` before
committing; `Setup` is sampled before the run but revealed only at `Init`, which is [BB04, §2.1]'s
order in distribution. `SIDSecure` copies `INDSecure`'s quantifier shape. `oracleImpl` builds the
three oracles from typed handlers so that simulators in other files never read `inLens`/`outLens`
through their bodies (Rule 10).

### D7. BB1 over the generator

`bb1Scheme G ℓ` tags parameters, keys and ciphertexts with the description (`Σ d, …`); `dec` is
`⊥` on mismatched descriptions. Over one group, `BB1.setup/keyGen/encrypt/decrypt` follow
[BB04, §4.1] at depth 1, including the order of `Setup`'s samples (`g`, `α`, `h`, `g_2`) and a
random generator `g ∈ G^*`. Messages are `G_T` encodings (`decodeT` reads `1` off the message
space; never exercised, the game refuses).

### D8. The security proof as named steps

The paper's simulator `B` is defined beside the scheme as typed handlers (`bb1SimInit`,
`bb1SimKeyQ`, `bb1SimChal`, `bb1SimImpl`, `bb1SimGame`) with ideal exponents. The headline
`bb1_sidSecure` is **proved** by the triangle inequality from three sorried steps: perfect
simulation on `P_BDH` up to identity collisions (`bb1_sim_real`), bit-independence on `R_BDH`
(`bb1_sim_random`), and the machine step (`exists_bb1_distinguisher`). *Precedent:* Gate 12's
`exists_adaptive_cpa` proved from sorried statements.

## Module layout (statement draft)

| Module | Lines | Content |
|---|---|---|
| `Pairing/Group.lean` | 299 | `BilinearGroup`, `BilinearGen`, `desc`, `inst`, `OrderAtLeastExcept`; group facts |
| `Pairing/Assumptions.lean` | 221 | `tupleStr`, `bdhStr`, `dbdhGame`, `dbdhAdv`, `DBDHAssumption`, `bdhGame`, `BDHAssumption`; T1 |
| `Pairing/Operations.lean` | 117 | `BilinearGen.Ops` |
| `Pairing.lean` (facade) | 31 | |
| `KeyExchange/Joux.lean` | 193 | protocol, correctness, key indistinguishability (all proved) |
| `KeyExchange.lean` (facade) | 23 | |
| `AdvancedEncryption/IdentityBased/Defs.lean` | 408 | `IBEScheme`, `Correct`, IND-sID-CPA game, `oracleImpl` |
| `AdvancedEncryption/IdentityBased/BonehBoyen.lean` | 553 | BB1, `bb1Scheme`, correctness (proved), the simulator |
| `AdvancedEncryption/IdentityBased/BonehBoyenMachine.lean` | 78 | T4 (Q11: its own module) |
| `AdvancedEncryption/IdentityBased/BonehBoyenSecurity.lean` | 170 | T2, T3 and `bb1_sidSecure` |
| `AdvancedEncryption/IdentityBased.lean`, `AdvancedEncryption.lean` (facades) | 32, 25 | |
| `TCSlib.lean` | +3 imports | separate commit |

Every file is under 1000 lines and no line exceeds 100 characters. Layout deviation from the
initial proposal: `Operations.lean` (keeps `Group.lean` free of the arithmetic layer's imports)
and `BonehBoyenSecurity.lean` (definitions separate from the heavyweight theorem file, policy §1);
`BonehBoyenMachine.lean` (T4 alone, so that its fill unit owns its own file; ruling Q11).

## Statements

Proof sizes are estimates for the remaining targets.

| Statement | Source | Status | Est. size |
|---|---|---|---|
| `BilinearGroup.bilinear_pow`, `pair_pow_left`, `pair_pow_right` | BB04 §2.2 item 1 | proved | — |
| `BilinearGroup.pair_comm` | BB04 §2.2, remark after item 2 | proved | — |
| `BilinearGroup.exists_pow_eq`, `pow_order(_GT)`, `pow_val_mul(_GT)` | group facts | proved | — |
| `BilinearGroup.pair_ne_one` (`e(x, x) ≠ 1` on `G^*`) | BB04 §2.2 item 2 | proved | — |
| `BilinearGroup.pow_val_bijective` (`a ↦ e(x, x)^a` bijective) | BB04 §3.1 ("`T` uniform") | proved | — |
| **T1** `BilinearGen.bdhAssumption_of_dbdhAssumption` | folklore (Q10) | **sorry** | 150–300 |
| `jouxKey_eq`, `joux_correct` | Jou00 p. 388 | proved | — |
| `jouxGame_eq_dbdhGame`, `jouxKeyIndist_of_dbdhAssumption` | Jou00 §5 + BB04 §3.1 | proved | — |
| `IBEScheme.sidImpl_*` (9), `oracleImpl_*` (3), readers | BB04 §2.1 | proved | — |
| `BB1.decrypt_encrypt` | BB04 §4.1 ("for a valid ciphertext") | proved | — |
| `BB1.decodeT_encT` | — | proved | — |
| `bb1_correct` | BB04 §4.1 | proved | — |
| `bb1Sim*` case lemmas (9) | BB04 §4.2 proof | proved | — |
| **T2** `bb1_sim_real` | BB04 §4.2, proof of Thm 4.1 (P_BDH case) | **sorry** | 400–800 |
| **T3** `bb1_sim_random` | BB04 §4.2, proof of Thm 4.1 (R_BDH case) | **sorry** | 150–350 |
| **T4** `exists_bb1_distinguisher` | BB04 §4.2 (B is efficient) | **sorry** | 700–1400 |
| `bb1_sidSecure` | BB04 Theorem 4.1 at depth 1 | proved from T2–T4 | — |

Definitions (all complete, each with a reader): `BilinearGroup`, `BilinearGen`, `desc`, `inst`,
`OrderAtLeastExcept`, `tupleStr`, `bdhStr`, `dbdhGame`, `dbdhAdv`, `DBDHAssumption`, `bdhGame`,
`BDHAssumption`, `Ops`, `jouxMsg`, `jouxKey`, `jouxGame`, `jouxAdv`, `JouxKeyIndist`, `IBEScheme`,
`honestRun`, `Correct`, `inLens`, `outLens`, `sidSpec`, `SidState`, `sidImpl`, `oracleImpl`,
`sidCodec`, `sidGame`, `SIDSecure`, `BB1.{Params,Key,Ciphertext,F,setup,keyGen,encrypt,decrypt,
idToZ,decodeT}`, `bb1Scheme` (simps field equations, non-simp), `BB1SimState`, `bb1SimParams`,
`bb1SimKey`, `bb1SimInit`, `bb1SimKeyQ`, `bb1SimCt`, `bb1SimChal`, `bb1SimImpl`, `bb1SimGame`.
Instances: `BilinearGroup.factPrime`, `neZeroOrder`, `nonempty_ne_one` and the bundle's field
instances. No `@[simp]`. Abbrevs: `sidSpec`, `SidState`, `BB1SimState` (each with `_eq`).

Every target carries a `**Proof sketch.**` following the paper. The draft also *proves* the Joux
results and BB1 correctness; the statement gate audits those proofs too.

## Unit split for fills

Each unit owns its target's file; helper modules are allowed beside it.

| Unit | Targets | Files | Notes |
|---|---|---|---|
| `pair-bdh` | T1 | `Pairing/Assumptions.lean` | machine composition (`NUPPT` re-pairing and a string-equality test), a `1/p` bound and `OrderAtLeastExcept` |
| `bb1-sim` | T2, T3 | `IdentityBased/BonehBoyenSecurity.lean` | typed coupling of two `simulate` runs (state relation), re-randomization of `h` and `r`, lazy sampling of `T` (`Games.Hopping` eager/lazy lemmas) |
| `bb1-machine` | T4 | `IdentityBased/BonehBoyenMachine.lean` | handler theorem T1 (`Games.exists_handlerMachine`), `Ops`, `ArithmeticFP`, exponent sampling with `Candidates.sampleBelowL` and `statClose_sampleBelowL` |

T2/T3 and T4 are independent statements. T4 is in its own module (Q11, applied on
`stmt/pairings`), so `bb1-sim` and `bb1-machine` own disjoint files and can run in parallel;
`BonehBoyenSecurity` imports `BonehBoyenMachine` for `bb1_sidSecure` (proved-modulo rule).

## Modelling choices for the statement gate

1. The pairing is the field `pair : G →* G →* GT` of a bundle; bilinearity and non-degeneracy
   are fields (non-degeneracy at the bundle's `gen`; `pair_ne_one` extends it to `G^*`).
2. Groups are drawn by a uniform `NUPPT` generator; the group is a total function of the
   description; descriptions have exact polynomial length.
3. Elements are fixed-width injective encodings; decoding of adversary strings is
   `Function.partialInv` (`decodeT`), with membership as the message-space predicate.
4. The generator `g` is uniform in `G^*` in DBDH, BDH, Joux and BB1's `Setup`.
5. Exponents are `ZMod p` and act by `x ^ a.val`; `T` in `R_BDH` and Joux's random key are uniform
   in `G_T`.
6. Large order is `OrderAtLeastExcept N δ` with negligible `δ` (DBDH ⇒ BDH: `N = 2^κ`; BB1:
   `N = 2^ℓ`).
7. Efficiency of group operations is the separate contract `Ops`; honest IBE algorithms carry no
   efficiency requirement.
8. Identities are `ℓ(κ)`-bit strings, embedded in `Z_p` by binary value (BB04 §4.4).
9. Messages are `G_T` encodings; the message space is "is an encoding".
10. Selective-ID shape: one machine, `Init` oracle, `Setup` sampled first and revealed at `Init`,
    forbidden queries answered `⊥`, one polynomial budget for all queries.
11. Advantage: two experiments (twice BB04's guess advantage).
12. Parameters, keys and ciphertexts carry the description `d`; `dec` is `⊥` across descriptions.
13. Joux: single-point `F_W` form; security is the maintainer's formalization of Jou00 §5.

## Questions for Seyoon (recommended option first)

- **Q1. Group model.** (A) Abstract bundle drawn by a PPT generator with a total description map
  (current). (B) A fixed group per `κ` (no generator randomness; simpler types, the non-uniform
  reading of BB04's fixed `G`). (C) Abstract bundle with a validity predicate and threshold, as
  `ExpGroupGen`.
- **Q2. The generator `g`.** (A) Uniform in `G^*` everywhere (BB04 §3.1, §4.1; current). (B) The
  bundle's fixed `gen` everywhere (modern "generator outputs `g`" convention).
- **Q3. Joux's protocol.** (A) Single-point `F_W(x, P, Q) = e(P, Q)^x` over the symmetric bundle
  (current). (B) Joux's two-point form `(P_X, Q_X)` with an abstract pairing allowing
  `e(P, P) = 1`.
- **Q4. Joux's security.** (A) Key indistinguishability under DBDH only (current, proved). (B)
  Also the computational form: the key is hard to compute under BDH. (C) Correctness only.
- **Q5. Efficiency of honest algorithms.** (A) Typed algorithms without an efficiency field; the
  generator's `Ops` only where a reduction needs it; a BB1-is-PPT statement deferred (current).
  (B) Add a string-level `IBEScheme.Efficient` predicate now, with a BB1 efficiency target under
  `Ops` and `ArithmeticFP` (one more unit, machine-heavy). (C) An `NUPPT`-based IBE interface like
  `FixedLengthPKScheme`.
- **Q6. Identities.** (A) `ℓ(κ)`-bit strings by binary value with `p ≥ 2^ℓ` except negligibly
  (BB04 §4.4; current). (B) Identities as elements of `Z_p` in a BB1-specific game. (C) Arbitrary
  identities hashed by a CRH from `Hashing.CollisionResistant`.
- **Q7. Game shape.** (A) One machine with an `Init` oracle (current; mirrors the PK games). (B)
  A two-stage adversary `A₁(1^κ) → (ID*, st)`, `A₂(st, params)` with shared coins.
- **Q8. Messages outside `M`.** (A) The challenge is refused (`⊥`; BB04's "`M_0, M_1 ∈ M`";
  current). (B) Canonicalized to `1`, as El Gamal's `egCanon`.
- **Q9. Advantage.** (A) Two-experiment form, as `INDSecure` (current). (B) Guess-the-bit form
  (`Games.guessAdv`), BB04's literal `|Pr[b = b'] − 1/2|`.
- **Q10. DBDH ⇒ BDH.** (A) Keep T1 as a target, flagged "not in the sources" (current). (B) Drop
  it; BDH stays a definition with its reader.
- **Q11. Fill units.** (A) Three units `pair-bdh`, `bb1-sim`, `bb1-machine`, moving T4 to its own
  module (`IdentityBased/BonehBoyenReduction.lean`) at the statement PR so the two BB1 units run
  in parallel. (B) The same three units, with `bb1-machine` after `bb1-sim` on one file. (C) One
  BB1 unit for T2–T4.
- **Q12. Source ingest (policy §2).** (A) Keep the PDFs uncommitted; ingest later from Markdown
  transcriptions of the consumed passages only (BB04 §2.1–§4.4, Jou00 §3 and §5), as the LWE
  campaign's scoped review. (B) Commit full Markdown transcriptions now. (C) No ingest; the
  docstring tags suffice for this campaign.
- **Q13. Efficiency contract `Ops`.** (A) As drafted: order, `mulG`, `powG`, `pairStr`, `mulT`,
  `memT`, numerals by `listToNat`, specified at generated descriptions. (B) Only what BB1's
  reduction uses (drop `pairStr`). (C) Add `invG`, `powT`, `memG` for future consumers.

## Risks

- **T4 is the largest job**: a polynomial-time handler with group operations through `Ops`,
  modular arithmetic through `ArithmeticFP` (inverse of `ID − ID*`), exponent sampling from coin
  blocks with a statistical hybrid over `q + 1` samples, and T1's state and length bounds.
- **T2 needs a relational simulation argument** (two `simulate` runs with different states and
  re-randomized coins). If `Games.Hopping` lacks a state-relation coupling lemma, the fill should
  request it as a shared lemma rather than proving a private one (policy §1, duplication).
- **Dependent types.** Groups depend on the description; consumers outside `BonehBoyen.lean` must
  move between `(bb1Scheme G ℓ).sidSpec κ` and typed handlers through `oracleImpl_*` and cast
  readers; fills may need `_onSpec` reader variants (as in `OracleSecurity`).
- **Typed honest algorithms** (Q5) may draw an audit finding if the gate expects PPT schemes.
- **Order hypotheses** (`OrderAtLeastExcept`) are assumptions about the generator; whether a given
  generator satisfies them is not formalized (as for `FullLengthExcept`).
- **Root not elaborated.** The three facades and every new module are checked; the library root
  `TCSlib` is not (it needs the whole library on the tree).
- **Shared facade.** `AdvancedEncryption.lean` will conflict with the GSW statement PR on one
  import line; the second PR to land adds its child.

## Verification (statement draft)

Evidence: `briefs/pairings/statement-phase/evidence/` (summary in `EVIDENCE.md` there).

- **Tree.** `$SP/dl-oleans-2` only. Snapshot before: 1230 files, SHA-256
  `457ba704d26757307f14131aa534929ffd70d30a732b0c744b104ca3fc96a15f` (the required value).
- **Base delta.** The tree holds the `eff2dcd0` sources. In the new modules' import closure (73
  modules at the base `e7a9f70f`), only `Foundations/BitLists` changed since (13 added lines). It
  and its 7 downstream closure modules (`Asymptotic/Adversary`, `Games/BitCodec`,
  `Encryption/PrivateKey/{Scheme,OracleSecurity}`, `Asymptotic/CollectionsHelpers`,
  `NumberTheory/Primality`, `Candidates/Arithmetic`) were backed up (hashes equal to the
  snapshot) and rebuilt at the base source: 8/8 rc 0.
- **Checks.** `scripts/lean_check_tree.sh`, one process at a time, final sweep of all 11 new
  modules in order: 11/11 rc 0, 0 errors, warnings only the 4 target `sorry`s (`Assumptions` 1,
  `BonehBoyenSecurity` 3).
- **Axioms** (`#eval` over every constant of the 11 modules, `Lean.collectAxioms`): 320
  declarations and 52 auxiliary constants; every one uses only `propext`, `Quot.sound`,
  `Classical.choice`, except the 4 targets and `bb1_sidSecure` (proved from 3 of them), which add
  `sorryAx`.
- **Rule 10.** Seven whole-file seal probes (`attribute [local irreducible]` on 2–51 foreign
  TCSlib definitions per module; names outside a module's closure are reported "unknown" and
  cannot be read; they are the only diagnostics in three probes): 7/7 with 0 other errors.
  Earlier runs found four reads (`intro` through `Correct` and through `SIDSecure`, and
  `DBDHAssumption` applied as a function in `Joux` and in `BonehBoyenSecurity`), now through
  `correct_iff`, `sidSecure_iff` and `dbdhAssumption_iff`. Controls: sealed `intro` through `Correct` fails;
  the same through `correct_iff` passes.
- **Style.** `scripts/style_lint.py`: 0 findings in 11 files. `campaign_style_lint.py --check8b`:
  0 FAIL, 2 WARN, both the check-8 acronym heuristic (`DBDHAssumption`, `BDHAssumption`,
  `SIDSecure` have readers `dbdhAssumption_iff`, `bdhAssumption_iff`, `sidSecure_iff`; the LWE
  precedent of `dlweAssumption_iff`).
- **Restore.** 8 backups copied back (0 hash failures), 15 new oleans deleted, 4 emptied
  directories pruned; snapshot after: 1230 files, `457ba704…a15f`, byte-identical (SNAPSHOT
  EQUAL).

- **Round 2 (Q11 split, 2026-11-16).** `stmt/pairings` rebased onto `523d80d2` (records only
  since `e7a9f70f`; range-diff identical, Lean sources unchanged) and T4 moved, byte-identical,
  to `BonehBoyenMachine.lean`. 12 modules: 12/12 rc 0, 0 errors, 4 target `sorry`s
  (`Assumptions` 1, `BonehBoyenMachine` 1, `BonehBoyenSecurity` 2). Axioms: 320 declarations and
  52 auxiliary constants, standard only except `sorryAx` in the 4 targets and `bb1_sidSecure`.
  Rule 10: the round-1 seal probes for the two changed modules pass (controls as before), and
  whole-file seals A/B, strict and coe, of `BonehBoyenMachine`, `BonehBoyenSecurity` and the
  `IdentityBased` facade pass 12/12 (`-DmaxErrors=0`). Lint unchanged (0 findings; 0 FAIL,
  2 WARN). Root `TCSlib` builds: 278 modules rebuilt from source on the tree (the closure's
  changed and missing modules and their downstream), 278/278 rc 0, root included. Evidence:
  `briefs/pairings/statement-phase/EVIDENCE.md`, round 2.

## Decision log

| Date | Decision / evidence | Status |
|---|---|---|
| 2026-11-16 | **Ruling (Seyoon): pairing campaign approved.** Abstract symmetric bilinear groups in the asymptotic/NUPPT framework with BDH and DBDH; Joux tripartite DH (protocol, correctness, key indistinguishability under DBDH); Boneh–Boyen BB1 selective-ID IBE in the standard model (IND-sID-CPA, scheme, correctness, security from DBDH). Out: Boneh–Franklin (no random-oracle layer), Type-3 pairings, concrete groups. Records on `cryptography/pass-shelat-ch2-4` in this file and `briefs/pairings/`; Lean by PR into that branch. | Approved scope |
| 2026-11-16 | **Sources received (Seyoon; not committed):** Jou00 publisher copy `dd423b93…f6df9`; BB04 ePrint 2004/172 full version `63c1c7b0…35de` (its numbering used). Both read; formulation differences recorded in § Sources. | Record |
| 2026-11-16 | **Ruling (Seyoon): IBE under `AdvancedEncryption/IdentityBased/`** (namespace `TCSlib.Cryptography.AdvancedEncryption.IdentityBased`); `Pairing/` and `KeyExchange/Joux` stay. `AdvancedEncryption.lean` is shared with GSW; the second statement PR adds its child import. Applied in the draft before commit. | Approved layout |
| 2026-11-16 | **Statement draft committed locally** on `stmt/pairings` (base `e7a9f70f5c1f11c2670f427ef813f2a6d8c53543`): modules `b02e6ce4a3dcc7c945825d1f1d3b636c5e377a01`, root exports `ce9c3728ec582be45fc33ca68d64b5533701093d` (both SSH-signed). 11 modules, 4 sorried targets; Joux and BB1 correctness proved; `bb1_sidSecure` proved from T2–T4. Checks, axioms, seals and style as in § Verification. Not pushed. | Ready for the statement PR (maintainer) and Codex statement gate |
| 2026-11-16 | **`dl-oleans-2` restored** to snapshot `457ba704d26757307f14131aa534929ffd70d30a732b0c744b104ca3fc96a15f` (8 backups restored, 15 new oleans deleted; SNAPSHOT EQUAL). | Done |
| 2026-11-16 | Questions Q1–Q13 (§ Questions) await Seyoon's rulings. | Open |
| 2026-11-16 | **Rulings Q1–Q13 (Seyoon): all recommendations accepted.** Q1: abstract bilinear bundle from a uniform PPT generator with a total description map. Q2: `g` uniform in `G*`. Q3: Joux in the single-point `F_W` form. Q4: Joux key indistinguishability under DBDH only. Q5: typed IBE algorithms; a "BB1 is PPT" statement is deferred. Q6: `ℓ`-bit identities read in `Z_p`. Q7: one machine with an `Init` oracle. Q8: out-of-space challenge messages refused with `⊥`. Q9: the two-experiment advantage. Q10: keep T1 (DBDH ⇒ BDH). Q11: three fill units (`pair-bdh`, `bb1-sim`, `bb1-machine`), with T4 moved to its own module before the statement PR. Q12: PDFs uncommitted, with Markdown transcriptions of only the passages used, ingested later. Q13: `Ops` as drafted. Noted: Joux 2000 states no security theorem, so key indistinguishability under DBDH formalises its §5 remark. Draft branch `stmt/pairings` pushed at `ce9c3728`. | Approved |
| 2026-11-16 | **Q11 applied** on the local `stmt/pairings`: rebased onto `523d80d2d4dd8e4ed6799358831e5b3806c6187b` (records only since `e7a9f70f`; range-diff 2/2 identical: `8aa111658bd0509c0fd204d605538ff440f08d02`, `b7ca25477c1685795f2ea45cd895889f7ecaf1c8`) and T4 `exists_bb1_distinguisher` moved byte-identically to `AdvancedEncryption/IdentityBased/BonehBoyenMachine.lean`: head `110c2f9db810d243693b9a5e8976a5ad205f1bab` (SSH-signed). `bb1-sim` owns `BonehBoyenSecurity.lean` (T2, T3), `bb1-machine` owns `BonehBoyenMachine.lean` (T4). 12/12 modules rc 0 with the 4 target `sorry`s; axioms, seals and lint as in § Verification, round 2; root `TCSlib` builds. `dl-oleans-2` restored (SNAPSHOT EQUAL). Not pushed: `origin/stmt/pairings` is still `ce9c3728`. The records branch then advanced to `a32ad0df` (#318, #319, #323 merged); none of their Lean files is in the pairing closure and `stmt/pairings` merges into it cleanly (`git merge-tree`). | Ready for the statement PR (maintainer) |
| 2026-11-16 | **Gate 40 pack** (Codex statement gate, standing ruling): `briefs/pairings/gates/40-pairings-statements/` for draft [PR #331](https://github.com/Shilun-Allan-Li/tcslib/pull/331) at `110c2f9db810d243693b9a5e8976a5ad205f1bab` (base `523d80d2`; 3 commits, 13 files +2153/−0). Statement audit of the definitions under Q1–Q13 (bundle and generator, BDH/DBDH, IBE interface, selective-ID game, BB1, the simulator), truth and sufficiency of T1–T4 (`bb1_sidSecure` uses T2–T4 only), and the proved results audited as proofs (Joux, `jouxGame_eq_dbdhGame`, BB1 correctness, `bb1_sidSecure`); Rule 10 (canonical seals cover 3 of the 12 modules; the other 9 rest on the round-1 hand-list seals, put to Codex), docstrings and sketches, the Q11 unit split, duplication, policy. Source excerpts of only the passages used ([Jou00] §2, §3, §5; [BB04] §2.1–§3.1, §4.1–§4.2, §4.4), PDF hashes re-checked. Evidence `stmt-pairings-r2.zip` (`83b05fbe`) filed at `statement-phase/evidence-r2/` with its manifest (411/411) and PROVENANCE. Merge interaction (git objects): clean with the tip `0542dd92` (#326 merged), #324, #327, #332; add/add conflict with #333 in `AdvancedEncryption.lean` and `TCSlib.lean`, resolved by union (all open heads in two orders give one tree `1fc1b521`). Merge conditions: union by whichever of #331/#333 lands second; rebuild `Pairing/Operations` and its 6 downstream modules (closure meets #326's `DTIME.lean`) and the root on the merged tree. verification.zip `348ce61f` (99 entries), sources.zip 86 files, pack `278ce323`. | Ready to stage |
| 2026-11-16 | **Gate 40 staged** on the exchange (local commit, for the maintainer to verify and push): `outbox/gates/40-pairings-statements-gate/` at `870bed6ca6d79f43599ab2972f74834137672b2a` (on the exchange tip `da8f8f66`; bundle 18 sections, SHA-256 `34a4a1b7`; SHA256SUMS `eaf1dfab`, 13/13 from a fresh archive; `verification.zip` `348ce61f`, 98/98 inner; records pin `356321accdd29b9ec73391b1c7b211b7d4cabf0f`, signed; Lean head `110c2f9d` (#331)). Local branch `stage/gate40-exchange`. Dispatch prompt `briefs/pairings/gates/40-pairings-statements/dispatch.md`. | Ready to dispatch once pushed |
| 2026-11-16 | **Gate 40 findings** (Codex, round 1) filed at `briefs/pairings/gates/40-pairings-statements/findings/gate40-pairings-statements-findings.md`: **HOLD**, 0 blockers, 2 majors, 4 minors, on #331 head `110c2f9d`. G40-01 (major): the generic `IBEScheme` encodings carry no fidelity law, so a plaintext-revealing scheme with constant `encCT` is `Correct` and `SIDSecure` (countermodel; not a defect of BB1 or of T1–T4). G40-02 (major): canonical Rule 10 seals cover only `BonehBoyenMachine`, `BonehBoyenSecurity` and the facade; `Group`, `Joux`, `Defs`, `BonehBoyen`, `Assumptions`, `Operations` need term-collected seals, controls and the unfold scan. Minors: G40-03 explicit T4 sampler parameters (`n = κ + wG(κ) + 1`, `sampleBelowL p (Nat.size p) n n`); G40-04 T4 source tag, T1 attribution, `bilinear_pow` domain wording; G40-05 `**Proof sketch.**` markers on `decrypt_encrypt` and `bb1_correct`; G40-06 README checkpoint and PR-description coverage wording. T1–T4 judged true and T2–T4 sufficient for `bb1_sidSecure`; fill note for T2: `ProbComp.expect_simulate_congr` has one state type, so the fill needs a common augmented state or a shared relational lemma in `Games`. G40-01 formulation put to Seyoon. | Awaiting ruling (G40-01) |
| 2026-11-16 | **Ruling G40-01** (Seyoon): **injectivity fields.** `IBEScheme` gains three Prop fields: `encPP` injective on the parameters of setup outputs; `encSK` and `encCT` injective on the keys and ciphertexts reachable under one setup output. All three are proved for `bb1Scheme` in #331, with no new admissions; efficiency stays deferred (Q5). The maintainer writes LE-gate40 (fields, BB1 proofs, minors G40-03 to G40-06) and runs the G40-02 canonical seals on `Group`, `Joux`, `Defs`, `BonehBoyen`, `Assumptions` and `Operations`, then stages Gate 40 round 2. | In progress |
| 2026-11-16 | **G40-06 (records part)**: `briefs/pairings/README.md` current checkpoint refreshed to #331 at `110c2f9d` (base `523d80d2`), the Gate 40 hold, ruling G40-01 and LE-gate40; seal coverage stated explicitly (canonical 12 probes over 3 modules; 6 modules hand-list only until LE-gate40). Historical entries kept. The PR-description part follows with LE-gate40. LE-gate40 started (maintainer job; waits for a free olean tree). | In progress |
| 2026-11-16 | **Integration builds for #331, #332, #333: all PASS** (`dl-oleans-2`; evidence `briefs/pass-shelat-ch5-8/maintainer/int-stmt-331-333-2026-11-16/`, zip `9ffa41bbb1fb703bcd36ff15bc810a7ee09f3236445f81e1096eb63144617172`, 1141 files). Scratch merges on the tip `c58597e6` (unpushed, unsigned scratch): C1 tip+#332 `df4cfea4` (clean; #323's `isFaninTwo_iff` intact); C2 C1+#333 `18777085` (clean); C3 tip+#331 `c67f94a4` (clean); C4 C2+#331 `cbfa9d85` (tree `26a68b89`; add/add on `AdvancedEncryption.lean` and content conflict on `TCSlib.lean`, resolved by union; resolved files in `resolved/`, to be applied by the maintainer when #331 is updated for merge). Builds, every module rc 0 with 0 `error:`/`error(`: 3 tip+#331 652/652; 2 tip+#332+#333 292 rebuilt; 1 tip+#332 3 rebuilt; 4 combined 4 rebuilt; reuse keyed on source and import closure, state check OK after each; whole-tree check at C4 (1299 modules) OK. Admissions: tip 202, C1 202, C2 237 (+35 GSW targets), C3 206 (+4 T1–T4), C4 241; no other change. Axioms: #332 readers standard; Joux and `bb1_correct` sorry-free; T1–T4 and the 10 GSW headlines each reach `sorryAx` only through themselves; `bb1_sidSecure` inherits exactly T2–T4. Lint Cryptography 92/101 at tip, C1, C2; 92/103 with #331 (two new check-8 WARNs: `SIDSecure`; `BDHAssumption`/`DBDHAssumption`; passed to LE-gate40). `dl-oleans-2` restored to `457ba704` (SNAPSHOT EQUAL). Stray `/lint-a` at the filesystem root (a mistyped redirect, tip lint lines) left for Seyoon; its deletion was refused to the job. #332 and #333 marked ready. | #332, #333 clear to merge |
| 2026-11-16 | **#332 and #333 merged** (Seyoon): the records tip now holds the DAGCircuit readers and the GSW statements. GSW fills `gsw-core`/`gsw-security` were issued on `486f44f8`, now an ancestor of the tip. Cross-build tip × #327 × #324 running on `dl-oleans-2` (#327 and #324 touch `SequentialZK`, `ComposeSecurity` and `ZeroKnowledge/Defs`, downstream of `DAGCircuit`); #327 (Gate 39 CLOSED) marked ready. #331 must take the resolved facade union (`maintainer/int-stmt-331-333-2026-11-16/resolved/`) when it is updated after LE-gate40. | #327, #324 after cross-build |
| 2026-11-16 | **LE-gate40 pushed** on #331: `stmt/pairings` fast-forwarded `110c2f9d` → `70c1f44432a41bcdb6f6d8602d957d2fc68ce0da` (signed: `3f9c49e5` landing edit, `70c1f444` a two-line proof fix; 5 files +189/−28). **G40-01:** `IBEScheme` gains `encPP_inj`, `encSK_inj`, `encCT_inj` (injectivity on setup outputs and on keys/ciphertexts reachable under one setup output; Deviation note: injectivity on reachable objects, not efficient decoding nor global injectivity; Q5 kept); proved for `bb1Scheme` via `bb1_encPP_inj`, `bb1_encSK_inj`, `bb1_encCT_inj` (public lemmas only; no generic helper, no private copies). **G40-03/04/05** doc-only (sampler parameters `n = κ + wG(κ) + 1`; T4 tag [BB04, §4.2]; T1 as folklore; natural vs signed exponent law; two `**Proof sketch.**` markers); strip-verified. Build of the 20-module pairing closure on the base: 20/20 rc 0, 0 `error:`/`error(`; sorry only T1–T4. Axioms: 384 constants, `sorryAx` only in T1–T4 and `bb1_sidSecure`; new lemmas and fields standard. **G40-02:** canonical seals on 10 owners (Group, Assumptions, Operations, Joux, Defs, BonehBoyen, Machine, Security, two facades): strict A/B and coe A/B 10/10 each, 0 errors; controls strict and coe ALL_OK True (43 sealed negatives each, each failing once); unfold scan 0 foreign. Lint: the two check-8 WARNs (`SIDSecure`, `BDH`/`DBDHAssumption`) are heuristic false positives (readers `sidSecure_iff`, `bdhAssumption_iff`, `dbdhAssumption_iff` exist). `dl-oleans` restored (SNAPSHOT EQUAL). Evidence `gates/40-pairings-statements/landing-r1/gate40-le-evidence.zip` (`5be013be`). Next: merge the tip (with #332, #333) into #331 with the resolved facade union, rebuild, then stage Gate 40 round 2. | Update and r2 next |
| 2026-11-16 | **#331 updated onto the tip** (local, unpushed until verified): signed merge `39d42e235a62b7085ffc19b01f371015c20d7795` of the records tip `673a2715` (with #332, #333) into `70c1f444`; the two facade conflicts resolved by the filed union (`maintainer/int-stmt-331-333-2026-11-16/resolved/`, byte-identical; the union keeps both sides' imports, contents entries and references). Diff against the tip: #331's 13 files only (+2293). Full-closure build on `dl-oleans` running; push, then Gate 40 round 2 staging, follow. | Build running |
| 2026-11-16 | **DW-7 ingests** (records `6078f369`): Jou00 (`joux-2000-tripartite-dh`) and BB04 (`boneh-boyen-2004-selective-id-ibe`) scoped passages ingested. **Correction:** the page images show BB04 writing absolute values in §2.1, in the §3.1 Decision BDH advantage and in the proof of Theorem 4.1, so this plan's item 6 ("written without an absolute value") is wrong; the Lean's absolute decision advantage therefore follows BB04, and any docstring calling it a deviation should be corrected in a later doc edit (to be checked against #331's docstrings). | Correction noted |
| 2026-11-16 | **#331 updated and pushed**: `stmt/pairings` fast-forwarded `70c1f444` → `9e7a96481785d6cac4dea3b2e990c49ac278b060` = the signed merge `39d42e23` (tip `673a2715` with #332, #333 into `70c1f444`; facades by the filed union) plus LE-doc-abs `9e7a9648` (docstring only, strip-equal: [BB04, §3.1] writes the absolute difference, per the DW-7 transcription). Build of `39d42e23` on `dl-oleans` (evidence `gates/40-pairings-statements/integration-tip/int-331-tip-evidence.zip`, `3227f70b`): diff vs tip = #331's 13 files; facades equal the resolved files; code tree = C4 except the 5 LE-gate40 files; closure 1299 modules, 661 rebuilt, 661/661 rc 0, 0 `error:`/`error(`; sorry totals tip 237 → head 241 (T1–T4 only); whole-tree check OK; axioms: `bb1_correct`, Joux results and the three `bb1_enc*_inj` standard; T1–T4 each the only sorry in its closure; `bb1_sidSecure` inherits exactly T2–T4; lint only the two known check-8 false positives. `dl-oleans` restored (SNAPSHOT EQUAL). A 09:00 UTC disk-full incident (this job's full `git archive` for lint) stopped the other build; this build's 31 modules from that window re-verified identical. Next: Gate 40 round 2 pack. | Gate 40 r2 to stage |
