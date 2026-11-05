# S2 design note: one framework for security games and two-party protocols

Status: **draft, 2026-11-04.** It implements the user's rulings of 2026-11-04:
- S2 is home-built at TCSlib's pins, adapting VCVio's design, and **VCVio is cited**;
- two-party protocols are carried by the same framework ("protocols unified");
- D-2: a common base, with `OracleEnsemble` restated over it, by agreement with Frederick.

Open decisions for the user are marked **R-n**; points needing Frederick's agreement are marked
**F-n**.

## Citation (policy.md §2, design adaptation)

```
* [VCVio] D. Tuma and the VCVio contributors, *VCVio: machine-checked cryptographic proofs in
  Lean*, https://github.com/dtumad/VCV-io, commit 9054989327a7185ff19ef9ff0f119cccea479501
  (2026-11-04), Apache License 2.0. Design adapted (no code transcribed): oracle specifications
  indexed by a type of oracle names (`VCVio/OracleComp/OracleSpec.lean`), oracle computations as
  a free monad over them (`OracleComp.lean`, `OracleQuery.lean`), probabilistic computations as
  computations over the uniform-selection oracles (`OracleComp/ProbComp/Basic.lean`), and
  simulation of oracles by stateful handlers with query logging and composition (`SimSemantics/`,
  `SimSemantics/QueryImpl/Compose.lean`, `QueryTracking/LoggingOracle`).
```

The source of every mathematical notion stays [PS10] (with [KL] and [Gol04] where [PS10] is
silent). The game-playing method is from [BR06] M. Bellare, P. Rogaway, "The security of triple
encryption and a framework for code-based game-playing proofs", EUROCRYPT 2006 (the fundamental
lemma), and [Sho04] V. Shoup, "Sequences of games", ePrint 2004/332. The rule for when each tag
is used is in `CITATION-VCVio.md`.

## Why (the finding behind the ruling)

Ch. 2–4 expresses each security notion by hand:
- the fixed functionals `invProb`, `predProb`, `acceptProb`, `distAdv` over uniform seeds;
- one deterministic oracle `I → O` with a Boolean output (`QueryTree`, `OracleAdversary`);
- a custom NUPPT decoder per notion (`inverter`, `distinguisherL`, `toOracleAdversary`).

Ch. 5–8 needs several things that model cannot express directly:
- **randomized, stateful oracles:** CPA's `Enc_k` draws fresh coins per query;
- **oracle families:** CCA's `Enc` and `Dec`;
- **non-Boolean adversary outputs:** forgeries, collisions, message pairs;
- **phases with adversary state:** CPA/CCA, non-malleability;
- **transcript predicates:** "`m` was not queried", "the challenge was not decrypted";
- **two-party executions with views:** Def 155.1, OT, Yao, ZK composition.

## Design

**Synchronized with the code after gate 02 (2026-11-05).** The framework lives in namespace
`TCSlib.Cryptography.Games`, with `OracleSpec` inside `OracleComp.lean`. Query bounds are
`OracleComp.CostBoundedBy cost c q`.
- **Executions** (`Party.exec`, `ExecOutcome`; fuel counts messages) run in a coroutine model that
  contains D8's. It is broader in two respects: early returns, and a return value separate from
  the last message. Agreement with D8 holds for embedded strategies, through bridge B4 (gate 02
  round 2, finding 1).
- **The executor records traces** (`Party.execT`): received messages and executed draws, not
  read from a party's log. Full [PS10] views come only from parties that sample their whole tape
  first (finding 2).
- **Interaction is defined by strategies** (ruled 2026-11-05): Frederick's `Strategy`/`View`
  remain the definitions of IP, ZK and two-party computation, and this executor is the proof
  calculus.
- **Identical-until-bad** has a semantic hypothesis: the same law to good successors.

The sketches below are the pre-gate draft; where they differ, the code and this paragraph rule.
Since gate 02 closed (2026-11-05), the round 2 findings and review are in
`gates/02-s2a/`.
**Thm 175.1 (ruled 2026-11-05):** strict or truncated simulators, a declared deviation carrying D8
into ch. 7 (`PerfectZKAbort` composes to statistical ZK with error `Q·2^-k`).

### 1. Oracle specifications and computations (after [VCVio, OracleComp/OracleSpec])

```lean
/-- A family of oracles named by `ι`: oracle `i` takes a query in `dom i` and answers in `rng i`. -/
structure OracleSpec (ι : Type) where
  dom : ι → Type
  rng : ι → Type

/-- Computations with access to the oracles of `spec`, returning an `α`: a free monad. -/
inductive OracleComp {ι : Type} (spec : OracleSpec ι) (α : Type) : Type
  | pure : α → OracleComp spec α
  | query (i : ι) : spec.dom i → (spec.rng i → OracleComp spec α) → OracleComp spec α
```

- `Monad` and `LawfulMonad` instances, with bind by structural recursion.
- Disjoint union of specs, `spec₁ + spec₂` (index `ι₁ ⊕ ι₂`), and the lifts `liftLeft`/`liftRight`.
- Garg's `QueryTree I O α` is the one-oracle case: there is a bijection
  `QueryTree I O α ≃ OracleComp (singleSpec I O) α` that commutes with `eval` and `simulate`
  (bridge B1).
- The whole framework lives in `Type` (universe 0), as `QueryTree`'s uses do. VCVio's universe
  polymorphism is not needed for [PS10].

### 2. Probability (TCSlib's: finite, uniform, real-valued)

Sampling is the oracle `unifSpec : OracleSpec ℕ` with `dom _ = Unit` and `rng m = Fin (m + 1)`
(after VCVio's uniform-selection oracle). Other finite types are sampled through an equivalence
with `Fin`: `$ᵗ T` for `[Fintype T] [Nonempty T]` (`Fintype.equivFin`). Write
`ProbComp α := OracleComp unifSpec α`.

**Semantics, by structural recursion, real-valued, with finite branching (no PMF, no `ℝ≥0∞`):**

```lean
noncomputable def ProbComp.prob (c : ProbComp α) (p : α → Prop) : ℝ   -- written Pr[p | c]
--   Pr[p | pure a]          = if p a then 1 else 0
--   Pr[p | query m () k]    = (m + 1)⁻¹ * ∑ j : Fin (m + 1), Pr[p | k j]
```

For finite `α` this gives a `FinDist α` (`ProbComp.dist`), which connects to `main`'s `statDist`,
`EpsClose` and extractors (#183).

**Bridge to `uprob` (B2):** a computation that samples `x ← $ᵗ σ`, `r ← $ᵗ ρ` and then decides
`P x r` has `Pr = uprob (fun z : σ × ρ => P z.1 z.2)`. So Garg's `invProb`, `predProb`,
`acceptProb` and `distAdv` are exactly the probabilities of four one-line games, and every
ch. 2–4 result stated through them transfers.

- **R-1 (ruled 2026-11-04: (a), the sampling oracle):**
  - (a) sampling as an oracle in the monad, as above (recommended): games read as programs, as in
    [PS10]'s experiments, and the semantics is a finite sum;
  - (b) all randomness as external finite seeds (`ρ → OracleComp spec α`, handlers reading coin
    tables): closest to today's code, but every game must declare and thread its product of
    seeds by hand.

  Both are finite, uniform and real-valued; the bridge B2 makes (a) agree with today's `uprob`.

### 3. Oracle implementations, simulation, logging (after [VCVio, SimSemantics, QueryTracking])

```lean
/-- Implement the oracles of `spec` by computations over `spec'`, with state `σ`. -/
def QueryImpl (spec : OracleSpec ι) (σ : Type) (spec' : OracleSpec ι') :=
  ∀ i, spec.dom i → σ → OracleComp spec' (spec.rng i × σ)

def simulate (impl : QueryImpl spec σ spec') : OracleComp spec α → σ → OracleComp spec' (α × σ)
```

- **Stateful, randomized oracles** are handlers into `spec' = unifSpec` (or `unifSpec + …`). For
  example, `Enc_k` draws its coins with `$ᵗ` on each query; the state holds the key, counters and
  flags.
- **Logging** is a handler transformer `withLog impl`, which appends `⟨i, x, y⟩` to a
  `QueryLog spec` in the state. Win conditions and oracle restrictions are predicates on the log:
  - "`m` was never queried to `Tag`";
  - CCA2's refusal to decrypt the challenge is a handler that answers `⊥` on it.
- **Reductions** are `simulate` with a handler that answers the adversary's oracles by querying
  the reduction's own oracles. This generalizes `QueryTree.simulate` (`eval_simulate`) to
  families and to state.
- **Query bounds** are a structural predicate `IsQueryBound c (qb : ι → ℕ)`, preserved by
  `simulate` with a per-query cost, generalizing `QueryTree.BoundedBy`.

### 4. Games and advantages (concrete level, one security parameter value)

- A **search game** is a `ProbComp Bool` built from the adversary: forgery, collision, inversion.
  Its advantage is `Pr[= true]`.
- A **distinguishing pair** is `G₀ G₁ : ProbComp Bool`, with advantage `|Pr[G₀] − Pr[G₁]|`.
- A **guess-the-bit game** has advantage `|Pr[b' = b] − ½|`, with the standard lemma relating it
  to the distinguishing form (factor 2).

[PS10]'s definitions are then short programs over these. Examples:
- **MAC forgery** (Def 134.2): `k ← Gen; (m, σ) ← simulate (withLog (tagImpl k)) A; return
  (Ver k m σ ∧ m ∉ log)`.
- **IND-CCA2** (Def 168.1): phase 1 with `(encImpl k + decImpl k)`, then the challenge, then
  phase 2 with `decImpl` refusing `c*`. The adversary's state between phases is the value it
  returns.

### 5. Game hopping (the generic lemmas, proved once)

1. `Pr` respects bind (total probability), `map` and relabelling of finite samples.
2. **Hybrids:** advantages add along a chain of games (the triangle inequality), with the standard
   `k`-step form used by the hybrid lemma.
3. **Identical until bad** [BR06]: two games written over the same code that differ only after a
   flag is set satisfy `|Pr[G₀] − Pr[G₁]| ≤ Pr[bad]`. Here this is a lemma about two handlers that
   agree while a state flag is clear.
4. **Oracle substitution:** if two oracle implementations are indistinguishable to every
   `q`-query adversary, then a game using one is close to the game using the other. The proof is
   by `simulate`. This is the step "replace the PRF by a random function" used in
   Thms 135.4, 168.2, 170.4 and 179.1.
5. **Lazy sampling** of a random function: a handler that samples on first query and caches gives
   the same distribution as a function table sampled up front. Garg's `LazySampling.lean` proves
   this for `QueryTree`; it is re-derived through B1/B2, not re-proved, where possible.
6. **Collision and union bounds** over `q` queries: for example, the `r` collisions of Thm 168.2.

### 6. Two-party protocols in the same framework ("protocols unified")

```lean
/-- A party that sends messages of type `Out`, receives messages of type `In`, and draws coins. -/
abbrev Party (Out In α : Type) := OracleComp (exchangeSpec Out In + unifSpec) α
--   exchangeSpec Out In has one oracle: query = outgoing message,
--   answer = the other party's next message, or `none` once the other party has returned
```

- **Execution** `exec (fuel : ℕ) (A : Party M₁ M₂ α) (B : Option M₁ → Party M₂ M₁ β) :
  ProbComp (Option (α × β))` (probed in P-S2-4; the transcript comes from logging handlers) is the
  coroutine interleaving: A's exchange query is answered by running B until
  B's next exchange query, and so on. The fuel is the protocol's message count, as in
  Frederick's fixed alternation.
- **A party's view** is (its input, its coins, the messages it received), read off the log of its
  `exchangeSpec` queries and its `unifSpec` answers. Def 155.1's joint distribution
  `{(view_A, out_B)}` is then a `ProbComp` directly.
- **Simulation-based security** (Def 155.1, ZK) compares two such `ProbComp`s, or two ensembles
  of them asymptotically, through the same distinguishing advantage.
- **OT inside Yao** (the composition step [PS10] omits): a party whose sub-protocol is run by a
  handler. Sequential composition is `simulate` of the outer party's calls to an inner
  protocol's ideal functionality, so the hybrid "real OT → simulated OT" is the oracle
  substitution lemma (§5.4) applied to a protocol.
- **Bridge B4 to Frederick's model:** every `Strategy` with a fixed alternation of `rounds`
  moves induces a `Party` (a loop that keeps the history and calls `next`). `exec` of the
  induced parties gives his `Protocol.exec`, `View`, `outP`/`outV` and transcript. His ZK
  definitions (`ZK`, `PerfectZK`, `PerfectZKAbort`) then transfer, and Thm 175.1 (sequential
  composition) is stated in the framework with a proved equivalence to his `ZK`. **F-2:** whether
  his ZK layer is later restated over `Party`, or only bridged (our recommendation: bridged now,
  restated at integration, by him).

### 7. The machine layer (asymptotic security)

- **Codecs.** A `SpecCodec spec` gives, per security parameter, string encodings of oracle
  names, queries, answers and the output, with `decode (encode a) = some a` and polynomial length
  bounds. It reuses Frederick's `pairEncode`, `decodeFin` and `encodeHist`.
- **The generic decoder.** `NUPPT.toComp (A : NUPPT) (codec) (n q : ℕ) : (A.Coins n) →
  OracleComp spec α` iterates `A`'s next-query activation on the encoded history, decoding a query
  or a final output, with budget `q`. It generalizes his `toOracleAdversary`, which is its
  one-oracle, Boolean-output instance (**bridge B3, which is also the D-2 restatement of
  `OracleEnsemble.Indist`**).
- **Security, uniformly:** `Secure G := ∀ (A : NUPPT) (q : PolyExpr), Negligible fun n =>
  adv (G n) (A.toComp codec n (q.eval n))`. The same shape covers search, distinguishing and
  guess-bit games, with fixed or adversary-chosen messages.
- **The efficiency lemma (the machine-level crux, proved once).** If a reduction is a NUPPT
  adversary run under a handler whose per-query work is a `PolyTimeComputable` function of the
  encoded state and query, with a polynomial query bound and polynomial state size, then the
  composite is `NUPPT.toComp` of a single NUPPT. It is built from Frederick's closure calculus
  (`Complexity/Randomized/Closure`). Every reduction of prongs A–D then needs only its handler's
  poly-time computability, never a machine construction of its own.

### 8. Bridges to existing code (all in our files; nothing of his edited without agreement)

**Status (2026-11-04, S2b branch `cryptography/pass-shelat-ch5-8-s2b`, stacked on #185):**
- **B1 proved** (`Games/Bridges/QueryTree.lean`): a bijection `QueryTree I O α ≃ OracleComp (singleSpec I O) α`, under which evaluation, Garg's `simulate` and `BoundedBy` (as `CostBoundedBy` with unit costs) are preserved.
- **B2 proved** (`Games/Bridges/Experiments.lean`): `Pr[x ← $ α : p x] = uprob p` (through the published `uprob_eq_card_filter`), sequential sampling equals product sampling, and `invProb`, `predProb`, `acceptProb` and `distAdv` as one-line games. It reads the four definitions' bodies (F-3).
- **B3 decoder drafted** (`Games/Machines.lean`): `Move`, `MachineCodec`, `buildComp`, `NUPPT.toComp` with its query bound, and `toComp_singleCodec`, which shows that `toOracleAdversary` is the one-oracle instance. The efficiency lemma is not started.
- **B4, B5 not started:** B4 waits for gate 02's findings on `Protocols`; B5's asymptotic part needs B3.

| Bridge | Relates | Purpose |
|---|---|---|
| B1 | `QueryTree I O α` ≃ one-oracle `OracleComp`; `eval`, `simulate`, `BoundedBy` | reuse Garg's PRF/GGM/lazy-sampling results |
| B2 | `uprob`-functionals (`invProb`, `predProb`, `acceptProb`, `distAdv`) = `Pr` of one-line games | reuse every ch. 2–4 concrete result |
| B3 | `NUPPT.toOracleAdversary` = one-oracle instance of `NUPPT.toComp`; `OracleEnsemble.Indist` = a one-oracle distinguishing `Secure` | D-2's restatement (**F-1**) |
| B4 | `Strategy`/`Protocol.exec`/`View` = induced `Party`s and `exec` | reuse his ZK layer (**F-2**) |
| B5 | `PrivateKeyScheme.SingleMessageSecure`/`MultiMessageSecure`, `PublicKeyScheme.Secure` = games with fixed message vectors | Thm 168.2, Claim 172.a |

### 9. Layout (new directory, on `cryptography/pass-shelat-ch2-4` per D-0)

`TCSlib/Cryptography/Games/`:
- `OracleSpec.lean`, `OracleComp.lean` (monad, sums of specs, query bounds);
- `Probability.lean` (`unifSpec`, `$ᵗ`, `Pr`, `dist`);
- `Simulate.lean` (handlers, `simulate`, logging);
- `Advantage.lean` (game shapes);
- `Hopping.lean` (§5);
- `Protocols.lean` (`Party`, `exec`, views);
- `Machines.lean` (codecs, `NUPPT.toComp`, the efficiency lemma);
- `Bridges/` (B1–B5);
- the facade `Games.lean`.

The namespace is `TCSlib.Cryptography`, with the framework's types `OracleSpec`, `OracleComp`,
`ProbComp`, `QueryImpl` and `Party`. Each module docstring's `## References` carries [VCVio] (the
block above), plus [BR06]/[Sho04] for `Hopping.lean`, and [PS10] for the protocol layer's §4.4
and §6.2.

**Size estimate:** 3–5k lines, including the protocol layer and the machine layer (the plan's
1–2k for S2 assumed the narrower design). The machine layer (§7) is the largest risk.

## Route probes before the statement phase (pre-ship, run in Lean)

| Probe | Shows |
|---|---|
| P-S2-1 | the monad, `Pr`, and B2 on `invProb` (one ch. 2–4 functional, transferred). **Passed 2026-11-04** (`probes/P-S2-1-monad-prob-bridge.lean.txt`): the free monad, `unifSpec` sampling, the finite-sum `expect`/`prob`, total expectation (`expect_bind`), `expect_sample`, and `invProb f A = Pr[game]`, with standard axioms. It reads `invProb` and `uexp` by their bodies, for want of published equations (F-3) |
| P-S2-2 | Thm 135.4's concrete reduction: a forger, run under a handler that answers `Tag` with a PRF-or-random oracle, gives a distinguisher with advantage `≥ ε − 2^{-n}` |
| P-S2-3 | the CPA game for Alg 99.1 with a stateful, fresh-coin `Enc` oracle, and one hop of Thm 168.2's proof. **Passed in part, 2026-11-04** (`probes/P-S2-3-handlers-log-cpa.lean.txt`). Done: sums of specs and of handlers, `simulate` with state, logging, `simulate_withLog` (logging is conservative; proved), the fresh-coin `encImpl`, the IND-CPA experiment as a program (phases, adversary state, challenge), `cpaAdv`, and the bad event of Thm 168.2 as a log predicate. **Not yet:** the hop itself, which needs the oracle-substitution and identical-until-bad lemmas (§5) and is scheduled for the statement-phase probes |
| P-S2-4 | one OT execution (Prot 160.4) through `exec`, with the receiver's view read from the log. **Passed in part, 2026-11-04** (`probes/P-S2-4-protocol-exec.lean.txt`): `Party` over `exchangeSpec` + `unifSpec`, `step`/`finish`, `exec` with fuel and role swap, a toy protocol executing by `rfl`. Design fix found: an exchange answers `Option In`, where `none` means the other party has returned, so a waiting party can finish. **Not yet:** OT itself and views from logs |
| P-S2-5 | B3: his `toOracleAdversary` as an instance of `NUPPT.toComp`, at the level of definitions |

## Coordination with Frederick (adds to the S1 note)

**Superseded 2026-11-05.** Frederick has left the branch, and these items are now this campaign's
own work, as ruled:
- F-1: the root restatement of oracle adversaries;
- F-2: the strategies define, and B4 proves;
- F-3: the equations, done in S2b.

The list below is kept as written.

- **F-1 (D-2):** `OracleEnsemble` and `toOracleAdversary` restated over `Games`, or bridged by
  B3; who does it, and when relative to his external gate.
- **F-2 (protocols unified):** his `Strategy`/`View`/`ZK` bridged by B4 now, and restated at
  integration.
- **F-3:** the framework adapts his `encodeHist`/`pairEncode` codecs and cites his closure
  calculus; any machine lemma we need in his `Closure.lean` is requested, not added.
  It also requests published equations for `invProb`, `predProb`, `acceptProb` and `uexp`
  (`Foundations/`): bridge B2 reads them by their bodies today (P-S2-1).

## Decisions for the user (ruled 2026-11-04: R-1 (a) the sampling oracle; R-2 reuse via bridges)

- **R-1:** sampling as an oracle inside the monad (recommended), or external finite seeds (§2).
- **R-2:** the generic lemmas of §5, re-derived through B1/B2 from Garg's concrete layer where
  possible (recommended), or proved fresh in the framework (simpler proofs, more duplication;
  each duplicate goes to the ledger).
