# Pass–shelat ch. 5–8: the spine (shared design, before any parallel prong)

Draft of 2026-11-04 by the maintainer agent of the Arora–Barak ch. 3–4 campaign. Status:
**proposal**; nothing here is decided until the user rules on the open decisions (end of this
file). The inventory is `inventory-ch5-8.md` (IDs below are its IDs); the plan is
`PassShelatChapter5-8Plan.md` at the repository root.

## Why a spine

The four fill prongs (A authentication, B secure computation, C composability, D randomness) are
independent at statement level: no prong cites another prong's theorem. They do share
infrastructure: two oracle-game shapes, a two-party execution model with private inputs and
outputs, a circuit carrier and a bridge between randomized-machine models. Built inside the
prongs, each would be built twice. The spine builds them once, freezes every statement in one
statement phase and passes one external statement gate. The prongs then fill in parallel on
frozen interfaces.

The spine has four steps, run in order.

## S1. The base and the frozen interface

- **Base.** A commit of `cryptography/pass-shelat-ch2-4` that builds: today the head does not.
  Two duplicate public names, `zipWith_xor_ofFn` (`Asymptotic/Encryption`, `Asymptotic/HardCoreLoops`)
  and `zipWith_xor_ofFn_eq_add` (`Asymptotic/MultiMessage`, `Asymptotic/MultiMessageLemmas`), are
  declared twice. This is the ch. 2–4 owner's fix (Frederick Dehmel), or a one-commit fix agreed
  with him. Ideally the base is also merged up to current `main`, which gained `ClassP/BinaryArith`
  and ch7's randomized classes after the branch forked (2026-10-08).
- **The interface list.** The ch. 2–4 declarations that ch. 5–8 statements cite, frozen by
  agreement: a change is announced, and the prongs re-sync. From the inventory:
  - machines and probability: `Complexity.NUPPT` (with `PPT`, `Uniform`, `runAt`, `Computes`,
    `ofPolyTime`), the closure calculus of `Complexity/Randomized/Closure`, `Negligible`,
    `Ensemble`, `Ensemble.Indist`, `Ensemble.Samplable`;
  - primitives: `FunFamily`, `StrongOneWay`, `PRG` with `PRG.Secure` and the expansion theorem `prg_expand` (`Asymptotic/HardCore`),
    `PRF`, `OracleEnsemble` and `OracleMove`, `PrivateKeyScheme` with `SingleMessageSecure` and
    `MultiMessageSecure`, the multi-message scheme of §3.9, `PublicKeyScheme`,
    `BitPublicKeyScheme`, `Collection`, `PermCollection`, `TrapdoorCollection`,
    `Collection.HardCore`;
  - candidates: `Candidates.ExpGroupGen` and `Candidates.DLAssumption`, conditional on
    `Candidates.ArithmeticFP`;
  - interaction: `Protocol`, `Strategy`, `View`, `InteractiveProof`, `ZK`, `PerfectZK`,
    `PerfectZKAbort`, `Commitment`.
- **Ownership.** ch. 5–8 code goes in new directories only (proposal below). Nothing is added to
  his files. A missing closure or machine lemma is requested from him, or stated in our own file
  with a note to fold it in later.

Proposed layout (all new):

| Directory | Content | Prong |
|---|---|---|
| `TCSlib/Cryptography/SecretSharing/` | additive sharing, Shamir | P0 |
| `TCSlib/InformationTheory/Extractors.lean` (beside `LeftoverHash`) | closeness, extractors, entropy, sources, the leftover hash bridge | P0 |
| `TCSlib/Cryptography/Games/` | the oracle-game layer (S2) | S |
| `TCSlib/Cryptography/Authentication/` | MACs, signatures, Lamport, CRHs, hash-and-sign | A |
| `TCSlib/Cryptography/SecureComputation/` | two-party execution (S3a), special encryption, garbling, OT, Yao | B |
| `TCSlib/Cryptography/Composability/` | CPA/CCA, `π′`, non-malleability, ZK composition | C |
| `TCSlib/Cryptography/Randomness/` | the learning game, derandomization, extractor impossibility | D |

## S2. The oracle-game layer (one design for A and C)

Two experiment shapes recur.

- **Search games** (A): MAC forgery, signature forgery, collision finding, one-time variants.
  The challenger samples a key, the adversary adaptively queries an oracle (`Tag_k`, `Sign_sk`) and
  outputs a candidate (a pair `(m, σ)`, or a collision). It wins on a predicate that may mention the
  transcript ("`m` was not queried"). The adversary's success probability must be negligible.
- **Two-phase distinguishing games** (C): IND-CPA/CCA1/CCA2 and non-malleability. In phase 1
  the adversary uses oracles `O₁`, then outputs `(m₀, m₁, state)`. The challenger encrypts `m_b`.
  In phase 2 the adversary uses oracles `O₂` with the challenge and outputs a bit. CCA2's
  decryption oracle refuses the challenge.

**What exists to build on.**
- The concrete layer (Garg, `Pseudorandom/Functions/OracleAdversary`) has adaptive query trees
  (`QueryTree`, `boundedBy`, evaluation against an oracle).
- His asymptotic PRF layer models an oracle adversary as a next-query NUPPT: `OracleMove` is
  decoded from the machine's output, `OracleEnsemble.Indist` is the oracle-indistinguishability
  of [PS10, Def 96.1], and `prfAdv_toOracleAdversary` links it to the concrete advantage.
- So the shape is a **generalization of his `OracleEnsemble`**:
  - from one oracle to an oracle *family* indexed by a finite tag type (encryption and
    decryption);
  - from a final bit to a final output tested by a game predicate over the transcript;
  - with a phase split for the challenge.

**Design requirements:**
1. The concrete game is an exact probability on finite types, and the asymptotic game wraps it
   with a NUPPT adversary and `Negligible`. This is his D2 pattern, so reductions are concrete
   inequalities plus machine closure.
2. The transcript is part of the game's state, so "unqueried message" and "not the challenge"
   are predicates over the transcript, not side conditions.
3. A bound on the number of queries, a polynomial `PolyExpr`, as in his PRF layer.
4. Bridges proving that his `OracleEnsemble.Indist` is the one-oracle, no-challenge instance,
   so the PRF results are reused, not restated.

**Coordination point.** This touches the design of his PRF layer. Agree with the ch. 2–4 owner
whether the generalization lives in a new file that only cites `OracleEnsemble` (proposal), or
becomes the common base that `OracleEnsemble` is restated over (cleaner; it changes his files).

## S3. The other shared layers

**S3a. Two-party execution with private inputs and outputs** (B, and C's Thm 175.1). His
`Protocol`, `Strategy` and `View` carry the interaction model of [PS10, §4.4] for provers and
verifiers. Def-155.1 needs, for each party, its view jointly with the *other* party's output,
compared with a simulator given that party's input and output. Proposal:
- a two-party functionality type (the inputs, and a pair of outputs);
- the honest execution's joint distribution of `(view_A, out_B)` and `(view_B, out_A)`, built on
  his `View`;
- Def-155.1 as two `Ensemble.Indist` statements.

His `View` already has the common input `x`, the party's auxiliary input `z`, its random tape `r`
and its `received` messages, so a party's private input can travel as its auxiliary input. The
pre-ship probe confirms that an execution gives each party its own `z`, and that the outputs are
readable from the strategies (`Strategy.out`).

**S3b. Circuits for Yao** (B). Use `main`'s `CircuitComplexity/DAGCircuit` (`DAGGate`,
`GateKind`, `FaninTwo`, `WellFormed`). Its `runWith (f : DAGGate → List β → β)` evaluates a gate
list over any value type, so the garbled evaluation runs over wire keys (`β := key`) with the same
traversal as the Boolean one, and correctness becomes a simulation lemma between two `runWith`
instances.

**S3c. The model bridge** (D's Thm 180.1). His `NUPPT` and ch7's randomized model on `main`
(`Randomized/PolyTimeModel`, `Randomized/Classes`: `randProb`, `VerifierModel`, `InBPP`) are two
models of probabilistic polynomial time. Thm 180.1 needs a language in ch7's BPP decided by a
coin-bounded machine, its coins replaced by a PRG's output, and a deterministic seed enumeration in
`DTIME`. Options:
- **a bridge lemma:** an `InBPP` language has a NUPPT decider with explicit coin and time
  polynomials (recommended for this campaign);
- **one model for the library:** a larger question, shared with ch. 2–4's integration.

**S3d. The learning game** (D's Def-179.a): a small self-contained prediction game in the crypto
style (recommended), not a PAC framework.

## S4. The statement phase and its gate

1. **Statements.** Every core item of the inventory is stated in its prong's files, each proof a
   `sorry` under a literal `**Proof sketch.**`, everything compiling on the base. This includes
   the spine's own definitions and bridges (S2, S3), whose small lemmas may be proved at once.
2. **Probes,** run before the gate as pre-ship checks:
   - an import probe of every cited ch. 2–4 and `main` name;
   - a route probe per prong for the hardest step:
     - A: the forgery-to-PRF-distinguisher reduction of Thm 135.4, stated through S2;
     - B: one garbled gate evaluated through `runWith`;
     - C: the CCA2 game instantiated for `π′`;
     - D: the BPP bridge's statement.
3. **One external statement gate** for all of ch. 5–8: the pack, the bundle and the auditor's
   findings, as in the ch. 3–4 campaign (`WORKFLOW.md`). Blockers and majors are repaired before
   any fill.
4. **The freeze.** The gated statements are the prongs' interfaces. A prong that needs a changed
   statement escalates; it never restates one.

## Decisions for the user (with recommendations)

| # | Decision | Recommendation |
|---|---|---|
| D-1 | Where P0 lands (Shamir and the extractor basics need nothing from ch. 2–4) | on `main` (or the campaign branch) directly, now, as a separate small PR; it does not wait for S1 |
| D-2 | S2's home: a new layer that cites his `OracleEnsemble`, or a common base his PRF layer is restated over | the new layer citing his, plus a bridge; restating is for the integration of ch. 2–4, with its owner |
| D-3 | Thm 144.1's domain: messages of bounded length, or `{0,1}^*` with the source's unproved domain extension (Constr-143.b) | bounded length `≤ p(n)` as the core statement; the unbounded form optional |
| D-4 | Scope of the deferred and optional items (§5.7 many-message signatures, Thm 165.2, Thm 175.9, Prot 176.2, §5.5.2 attacks) | as in the inventory: §5.7 and Thm 175.9 optional; Thm 165.2 statement-only; Prot 176.2 deferred until proofs of knowledge exist |
| D-5 | The learning game: crypto-style, or PAC in `TCSlib/LearningTheory` | crypto-style (S3d) |
| D-6 | The randomized-model question for Thm 180.1 | the bridge lemma (S3c); one model for the library is a separate, larger decision |
| D-7 | Fill agents per prong | per the soft rule of the ch. 3–4 campaign: Codex for first attempts; Claude for slow single fills |
