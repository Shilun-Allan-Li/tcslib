# Gate 03e: review of the auditor's findings, with resolution proposals

- **Reviewed:** `briefs/pass-shelat-ch5-8/gates/03-ch2-4/findings/gate03e-findings.md`. It has 17 findings: 2 majors, 4 minors and 11 notes.
- **Code:** worktree `wt-g03` at `a3c5fa8b72e50939822f22364647dc844a3914a0`. Line numbers below refer to that commit.
- **Downstream code read:** `wt-prong-c` at `aa71d0e7` (`Composability/SequentialZK.lean`), `wt-prong-b` at `1cf007d1` (`SecureComputation/`), `wt-s2b` at `afe5982f` (`Games/Bridges/Strategies.lean`).
- **Source text:** `wt-g03/blueprint/src/references/pass-shelat-2010-ch4.raw.md` and `pass-shelat-2010-appendix.raw.md`. I did not build Lean. The axiom facts below come from the 03e evidence (`gates/03-ch2-4/evidence/e/`) and from the full gate 03 print log (`scratchpad/g03-checks.log`).

## Summary

- **No finding is false.** The two majors hold, and Major 2 holds in a stronger form than the auditor gives (see below). I agree with every severity: 2 majors, 4 minors, 11 notes.
- **Corrections to the auditor:**
  - **#1, proposed fix.**
    - A message-prefix cap does not make `ProverBounded` a lemma. `ProverBounded` quantifies over every tape and every history, and the witness length must also be bounded.
    - The 3-colouring prover and verifier do not read a polynomial prefix as defined. So "packs 03g and 03k do theirs" understates the work.
    - The auditor's fallback, "add the caps as conjuncts to the Thm 124.1 headlines", is false for the 3-colouring protocols as they stand.
  - **#5(c).** The 22 core sorries come from `main` (MIG-1 stage S). The run-3 sentence about `TuringMachine/Build/*` in fact describes `Complexity/Randomized/Build/*`, which has 0 sorries.
  - **#13.** Its premise is out of date: `exists_owp_hardCore` is now proved and prints clean.
  - **#12.** Its pointer is already met: the 3-colouring verifier checks the lengths.
  - **Pack labels.** #5, #10, #12, #14 and #16 send work to the wrong pack: 03g is 3-colouring and 03k is graph isomorphism. Pack 03e's own scope line lists them in the wrong order.
- **Major 1** (`InteractiveProof` and `EfficientProverProof` accept parties that are only `Efficient`).
  - The HALT counterexample checks.
  - `InteractiveProof`'s docstring already states the cost. `EfficientProverProof`'s docstring and the four field docstrings do not: they say "PPT".
  - **Recommended (ruling R-03e-1, option 1):** the ch. 6 convention.
    - `Efficient` plus bounded honest messages, in the definitions.
    - `Protocol.ProverBounded` moves from prong C into ch. 2–4, as a field of `EfficientProverProof`.
    - Honest completeness messages are bounded in `InteractiveProof`.
  - Under option 1:
    - Undecidable languages are excluded, by capping the verifier.
    - Thm 175.1's hypothesis becomes derivable.
    - No theorem statement text changes.
    - The Q-1 choice stands: D8's `Efficient` is kept and no `ReadsPrefix` is required.
- **Major 2** (`PerfectZK` and `PerfectZKAbort` have no source instance). The obstruction is inherent: any graph-isomorphism prover that draws π from finitely many fair coins fails, since 6 does not divide 2^c.
  - The graph-isomorphism file already says so (`GraphIsomorphismZK.lean:39–43`). The definitions, DESIGN §5 item 11 and ch. 5–8's `SequentialZK.lean` do not.
  - **Recommended (ruling R-03e-2, option 1):**
    - Correct the docstrings.
    - Prove `PerfectZKAbort.statZK`, which retries the simulator |x| times with the proved `polyTimeComputable_iterateFind`.
    - Ch. 5–8 cites `StatZK.seqRep` with negligible δ (instance `gi_statZK`) for the source's "perfect" case.
    - `PerfectZKAbort.seqRep` becomes a corollary, which removes one `sorry`.
- **User rulings needed:** R-03e-1 (Major 1), R-03e-2 (Major 2), R-03e-3 (the 15 `@[simp]` lemmas, #17) and R-03e-4 (scope: the text's Thm 124.1 with negligible soundness needs a soundness-amplification statement in ch. 7, which prong C lacks). Everything else is a maintainer fix.
- **Pending packs this pack's fixes do not affect:** 03d, 03f1, 03f2, 03h, 03i, 03j and 03l. **Affected:** 03g (3-colouring) and 03k (graph isomorphism, `NPLemmas`). Under R-03e-1 option 2, both see only docstring pointers.

---

## 1. Major 1: the proof systems require only `Strategy.Efficient`

### Verdict: **true**. Severity: **major (agree)**.

**Evidence at `a3c5fa8b`.**
- `InteractiveProofs.lean:99–108`. `InteractiveProof` has `efficientV : π.V.Efficient` and nothing else on V. The field docstring at :100 says "The verifier is a PPT strategy." `InteractiveProofErr` repeats this at :119–120.
- `InteractiveProofs.lean:265–275`. `EfficientProverProof` is documented as "an interactive proof whose prover is a PPT strategy", and its field `efficientP : π.P.Efficient` (:272) also says "PPT strategy". There is no D8 caveat. `EfficientProverProofErr` repeats this at :282.
- `InteractiveProofs.lean:92–98` and `:115–117` already declare, for `InteractiveProof` and `InteractiveProofErr`, that "this predicate alone does not bound the verifier's work in `|x|` … the class `IP` adds the message-prefix cap". So the RE cost is stated there; it is missing only for the efficient-prover structures and the field docstrings.
- `InteractiveProofs.lean:139–140`. Only `IP` requires `π.V.ReadsPrefix m` (run-3 repair P9-1).
- Source, ch. 4 raw text pp. 116 and 119: Def 116.1 says "V is a p.p.t. machine" and Def 119.5 says "P is p.p.t.". On p. 116 the time complexity is "an upperbound on the running time of A independently of the content of the messages it receives".

**The HALT counterexample checks.**
- V outputs `[T ⟨x, m⟩]` on the whole message m, with no `take`, so it is `Efficient`. P copies y, so it is `Efficient` (as in `npProtocol_efficientP`).
- Completeness holds: P sends a halting history. Soundness holds with ε = 2⁻ⁿ, because no history exists for x ∉ HALT.
- So `EfficientProverProof π HALT R_hist` holds.
- The echo prover against a doubling V\* (part (b)) also checks. Both are `Efficient`, and the view reaches length 2^rounds.

**Corrections to the auditor's analysis.** These change the cost of the options, not the verdict.
1. **A cap on P does not make `ProverBounded` a lemma.**
   - `ProverBounded` (prong C, `SequentialZK.lean:343–344`) is `∀ x y r hist, R x y → (π.P.next x y r hist).length ≤ B.eval x.length`, over arbitrary lists r and hist.
   - `ReadsPrefix m` removes only the dependence on message bits past m(|x|). The number of messages, |r| and |y| still enter the activation's input, and `NUPPT.output_length_le` (`PPT.lean:185`) bounds the output only by the time bound in that input length.
   - So the cap yields only a restricted bound: |r| = coinLen, `hist.length` at most rounds, and |y| bounded, which needs `WitnessRelation.bounded` and is not part of `EfficientProverProof`.
2. **The 3-colouring parties are not prefix-reading for any cap.**
   - The prover decodes the challenge as `edgeIdxOfMsg m w := w.length % m` (`ThreeColoring/Language.lean:321`), and `colProver` uses it at `ThreeColoring/Protocol.lean:419`. Truncating 1^(c+1) to c bits changes the opened edge.
   - The verifier reads `msgAt com i := pairFstD (pairSndD^[i] com)` (`Protocol.lean:101`) inside `colVerify` (`Protocol.lean:145–146`). Make component 0 of `com` longer than the cap and challenge an edge (1, 2): truncation destroys components 1 and 2 and flips the verdict.
   - Option (i) therefore needs both parties redefined (§1.2). The auditor's fallback, adding the caps as conjuncts to the Thm 124.1 headlines, cannot be done for the 3-colouring protocols as they stand.
3. The graph-isomorphism side is as cheap as the auditor says:
   - `giProver` reads one bit (`GraphIsomorphism.lean:495`).
   - `gniVerifierRep` reads `headD` (:469).
   - `giVerifier` compares with n²-bit encodings and `decPerm` reads positions below n² (`Encoding.lean:170–174`). A cap of `var + 1` suffices.
4. **Bounded honest messages exclude the RE examples at the language level.** Suppose the honest prover's messages are at most B(|x|) on the completeness witness. Replace V by V′ := V reading `hist.map (take B(|x|))`.
   - V′ is complete, since the honest messages are untouched.
   - V′ is prefix-reading by construction.
   - V′ is sound: against any P\*, V′ behaves as V does against "P\* with its messages truncated", which is another `Strategy`. By induction on the moves, P\* receives the same messages in both executions.
   - Hence L ∈ `IP`. This is the cheap way to close the RE gap, and it is what option 1 below uses.
   - The bound must sit in `InteractiveProof`'s completeness clause, not only in `EfficientProverProof`. With R = ∅, `EfficientProverProof π HALT ∅` holds already, because `completeWitness` and any R-relative bound are then vacuous.

### 1.1 Option 1, recommended: `Efficient` plus bounded honest messages (the ch. 6 convention)

```lean
-- Interaction.lean (moved here from Composability/SequentialZK.lean, same body)
/-- The honest prover's messages have at most `B(|x|)` bits on every instance with an
`R`-witness, whatever it has received and whatever its tape [PS10, §4.4: a machine of time
complexity `t(|x|)` writes at most `t(|x|)` bits per message]. -/
def Protocol.ProverBounded (π : Protocol) (R : List Bool → List Bool → Prop) (B : PolyExpr) : Prop :=
  ∀ x y r hist, R x y → (π.P.next x y r hist).length ≤ B.eval x.length

-- InteractiveProofs.lean
structure InteractiveProof (π : Protocol) (L : Language Bool) : Prop where
  efficientV : π.V.Efficient
  /-- Completeness, with honest-prover messages of at most `B(|x|)` bits. -/
  complete : ∃ B : PolyExpr, ∀ x ∈ L, ∃ y : List Bool,
    (∀ r hist, (π.P.next x y r hist).length ≤ B.eval x.length) ∧
    ∀ z, uprob (fun r : π.ExecCoins π.P x => π.outV π.P x y z r = [true]) = 1
  sound : …                                        -- unchanged
-- InteractiveProofErr: the same `complete`.
structure EfficientProverProof … extends InteractiveProof π L where
  efficientP : π.P.Efficient
  boundedP : ∃ B : PolyExpr, π.ProverBounded R B
  completeWitness : …                              -- unchanged
-- EfficientProverProofErr: the same `boundedP`.
theorem InteractiveProof.exists_accept … -- the old `complete`, for consumers
theorem EfficientProverProof.proverBounded (h : EfficientProverProof π L R) : ∃ B, π.ProverBounded R B
-- optional, needs a machine lemma `Strategy.Efficient.capTo` (truncate every encoded message):
theorem InteractiveProof.mem_IP (h : InteractiveProof π L) : L ∈ IP
```

**Docstrings.**
- `Strategy.Efficient` and the structures: "time polynomial in the total input (D8); the honest messages are polynomially bounded (the source's p.p.t. writes at most t(|x|) bits); against a cheating prover the verifier's work is polynomial in the message length, not in |x|. With bounded honest messages the verifier can always be capped (`InteractiveProof.mem_IP`), so the structures are satisfiable only for languages in `IP`."
- DESIGN §5 item 8: amend it to match.

**New proof obligations.** Each takes a few lines.
- `npProtocol_proverBounded hp : (npProtocol T p).ProverBounded R p`.
- `ProverBounded.pullback`, with bound `B.subst p` along a `LevinReduction`, using `witness` and `length_eq`.
- `giProtocol` and `giProtocolRep` with bound `var`: the messages are n²-bit `encGraph` and `encPerm`, whatever the tape and history.
- GNI prover with bound `const 1`: one bit (`GraphIsomorphism.lean:426`).
- `colProtocol` and `colProtocolRep`: `∃ B` from `hC.easy` through `PolyTimeComputable.output_length_le` (`ClassNP/PolyTime.lean:91`). `colCommit` and `colOpen` have a fixed shape for every tape and history, and no definition changes.

**Theorems re-proved with unchanged statement text.**
- 03e:
  - `InteractiveProofErr.interactiveProof`, `InteractiveProof.exists_err` and `exists_uprob_accept_lt`.
  - `EfficientProverProofErr.efficientProverProof`, `EfficientProverProof.exists_err` and `npProtocol_interactiveProof`.
  - `LevinReduction.efficientProverProofErr` and `.efficientProverProof`.
  - The four Thm 124.1 forms. Their proofs are compositions, so they do not change.
  - `WitnessRelation.mem_IP` and `NP_subset_IP` are unchanged.
- 03k:
  - `gni_interactiveProofErr` (`GraphIsomorphism.lean:899`) and `gni_interactiveProof` (:918).
  - `gi_efficientProverProofErr` (:937), `gi_rep_efficientProverProof` (:954) and `gi_rep_interactiveProof` (:959).
  - Their copies in `GraphIsomorphism/{Soundness, SoundnessRep, SoundnessRepGI}.lean`.
- 03g:
  - `col_efficientProverProofErr` (`Protocol.lean:812`).
  - `colRep_efficientProverProof` (:851; it is sorried, so only a sketch line changes) and `colRep_interactiveProof` (:856).
  - `col_zeroKnowledgeProof` (`Simulator.lean:782`) is unchanged.
- `LevinReduction.zk` and the ZK definitions are untouched.

**Ch. 5–8 (prong C, `SequentialZK.lean`).**
- Delete the local `Protocol.ProverBounded` (:343–344) and use the ch. 2–4 one.
- `ZK.seqRep`, `StatZK.seqRep`, `PerfectZK.seqRep` and `PerfectZKAbort.seqRep` keep `hB`. Optionally they can take `EfficientProverProof π L R` instead: the text's "(P, V) is a ZK proof". `hB` then comes from `.proverBounded`.
- `InteractiveProof.seqRep` gains one sketch line: `seqProver` emits π.P's messages or `[]`, so the same B works.
- Prong B is unchanged; its `Functionality.PolyTime` already follows this convention. S2b `Strategies.lean` is unchanged.

**Packs that audit the change.**
- 03e: delta re-audit of `InteractiveProofs.lean`, `Interaction.lean` and the `NP.lean` docstrings.
- 03k (graph isomorphism and GNI) and 03g (3-colouring): the new bound lemmas.

**Relation to the rulings.**
- It keeps Q-1's substance: D8's `Efficient` stays, `ReadsPrefix` is not required in ch. 2–4, and Thm 175.1 rests on `ProverBounded`.
- It reverses only the cost note "no ch. 2–4 change", by placing `ProverBounded` in the definitions.
- It applies the ch. 6 ruling ("`Efficient` plus polynomially bounded honest messages, in the definition") to Defs 116.1 and 119.5.

### 1.2 Option 2: `ReadsPrefix` in the structures (the auditor's proposal (i))

```lean
structure InteractiveProof … where
  efficientV : π.V.Efficient
  readsPrefixV : ∃ m : PolyExpr, π.V.ReadsPrefix m
  …
structure EfficientProverProof … where
  efficientP : π.P.Efficient
  readsPrefixP : ∃ m : PolyExpr, π.P.ReadsPrefix m
  …
def IP : Set (Language Bool) := {L | ∃ π, InteractiveProof π L}          -- statement change
theorem Strategy.ReadsPrefix.pullback (h : S.ReadsPrefix m) (hx : ∀ x, (f x).length = p.eval x.length) :
    (S.pullback f g p).ReadsPrefix (m.subst p)
```

**Ch. 2–4 cost.**
- **03e:**
  - The two structures, their conversions, `IP` and its docstring, `npProtocol` (the prover ignores the history, so a trivial lemma) and `ReadsPrefix.pullback`.
  - The Levin transfer and the four Thm 124.1 forms are re-proved.
- **03k:** prefix lemmas for `giVerifier`, `giVerifierRep`, `gniVerifierRep`, `giProver` and `giProverRep`. These are plausible: prefix-determined decoders, and equality with n²-bit strings.
- **03g:** a redesign.
  - `edgeIdxOfMsg` must become prefix-reading, for example `(w.take m).length % m`. A cap of `var` suffices, since |E| ≤ n² ≤ |x|.
  - `colVerifier` and `colVerifierRep` need a length guard on `com` and `opn`. The guard needs a polynomial bound on `Com`'s output length, which `Commitment` does not carry (only `PolyTimeComputable Com`). So either `colProtocol` gains a parameter (which changes the statements of `zk_proof_of_levinReduction` and every Thm 124.1 form), or `Commitment` gains an output-length field (which changes a ch. 5–8 interface type).
  - Re-done: efficiency (`ThreeColoring/Machines.lean`), completeness and soundness (`Protocol.lean`, `ProtocolProofs.lean`) and the ZK sketch (`Simulator*.lean`).

**Ch. 5–8.**
- `InteractiveProof.seqRep` must supply `ReadsPrefix` for `seqVerifier`. It inherits m from π.V, because truncation commutes with `drop`, `take` and `length`.
- `ProverBounded` is not derived (correction 1). Thm 175.1 keeps `hB`, or `ProverBounded` is restated over executions (|r| = coinLen, `hist.length < rounds`) with a `WitnessRelation` hypothesis.

**Fidelity.** This is closest to the text for V. For P it still does not bound the messages unless |y| is bounded.

### 1.3 Option 3: keep the definitions and declare the cost

**Docstring-only changes.**
- `InteractiveProofs.lean:100, 119, 272, 282` become "efficient in the sense of D8 (`Strategy.Efficient`)".
- `EfficientProverProof(Err)` (:265–285) gains: "**Deviation (D8):** P is only `Efficient`: its messages are not bounded in |x| (Thm 175.1 assumes `ProverBounded`), and with `InteractiveProof` the structure is satisfiable for languages outside the text's IP, e.g. HALT."
- Add a DESIGN §5 entry.
- The Thm 124.1 docstrings say "efficient (D8)".

**Costs.**
- No code or proof changes. 03g and 03k are untouched. Prong C is unchanged.
- The user must acknowledge explicitly that "is an interactive proof (with efficient prover)" in every ch. 2–4 and ch. 5–8 theorem asserts less than Defs 116.1 and 119.5.
- Ch. 4 and ch. 6 keep different efficiency conventions.

### 1.4 Ruling needed: yes (R-03e-1, §6)

---

## 2. Major 2: `PerfectZK` and `PerfectZKAbort` have no source instance

### Verdict: **true, and stronger than stated**. Severity: **major (agree)**.

**Evidence.**
- `Defs.lean:136–139`: `PerfectZK := StatZK π R (fun _ => 0)`.
- `Defs.lean:141–152`: `PerfectZKAbort`, Goldreich's abort form with ⊥ = `[]`.
- No lemma leaves `PerfectZKAbort`; grep finds no user outside `Defs.lean`, apart from docstring mentions in `GraphIsomorphismZK.lean`.
- DESIGN §5 item 11 reads "`PerfectZKAbort` stated as the perfect form".
- Prong C presents it as the handling of the text's expected-time simulators: `SequentialZK.lean:41–45` ("perfect zero-knowledge with abort (Goldreich's form, with which the text's expected-polynomial-time simulators are handled)") and :397–399.
- `PerfectZK.seqRep` (:392) and `PerfectZKAbort.seqRep` (:407) sit on the ch. 5–8 interface.

**The counterexample checks.** G₀ = G₁ = the empty graph on 3 vertices. All six σ are `Riso` witnesses.
- `giProver` sends `encPerm (π * σ⁻¹)` on challenge 1 (`GraphIsomorphism.lean:495`), with π = `samplePerm` and the identity on failure (:348–349).
- `permFromCoins 3 2 18`: the range-1 position accepts one value in four, so it fails with probability (3/4)¹⁸ > 0 (`Sampling.lean:604–608`, `Permutations.lean:109–112`).
- So γ has a law that depends on σ. A simulator sees only (x, z), so no exact or conditional-exact match exists.

**Strengthening (missed).**
- **No sampler repair helps.** Take any honest prover of Protocol 120.6's shape that draws π from finitely many fair bits, with D8's polynomial `coins`. The law of γ = πσ⁻¹ is the same for all six witnesses only if π's law is invariant under right multiplication by S₃, that is, uniform. Probability 1/6 is not dyadic. So both perfect notions fail for every such prover, and even for the honest verifier.
- **`PerfectZK` fails a second time, on the simulator side.** Even with an exactly uniform prover, a strict simulator with bit coins outputs only dyadic probabilities. The honest-verifier view on the same instance has, for example, Pr[b = 1 ∧ γ = id] = 1/12. `PerfectZKAbort` escapes this second obstruction (conditional laws are ratios), but not the first.
- **The cost is half-declared already.** `GraphIsomorphismZK.lean:39–43` (03k) says the abort form "is not claimed for `giProtocol` itself, whose honest prover's rejection-sampled π is not exactly uniform". The concrete layer proves the abort form with ideal permutations (`giSimAttempt_perfectAbort`, :283–297). What is missing is the cost at the definitions, in DESIGN §5 item 11 and in prong C.
- **Context.** Gate 02 note 11 (`gates/02-s2a/resolutions-r1.md:39`) already records that exact non-dyadic sampling is not fair-bit-efficient. The ch. 5–8 game layer has exact `sampleFin`, but its machine bridge is restricted to dyadic sampling.

### 2.1 Option 1, recommended: keep, state the cost, prove the bridge, cite `StatZK`

```lean
/-- … **Cost (D8, D10):** with strict bit-coin simulators the simulator's output
probabilities are dyadic, and with honest parties drawing polynomially many fair coins a
graph-isomorphism prover's permutation cannot be uniform on `S_n` (`n! ∤ 2^c`, `n ≥ 3`), so
no protocol of the source attains this notion; [PS10, Theorem 122.3] is formalized as
`StatZK` with negligible error (`gi_statZK`). -/
def PerfectZK …
/-- … **Cost (D8, D10):** as for `PerfectZK`, the honest graph-isomorphism prover's view
depends on the witness, so no source protocol attains this notion; the abort form holds for
ideal permutations at the concrete layer (`giSimAttempt_perfectAbort`). It implies
statistical zero-knowledge with error `2^{-|x|}` (`PerfectZKAbort.statZK`). -/
def PerfectZKAbort …
/-- Retry the aborting simulator `|x|` times on disjoint coin blocks and output the first
non-`⊥` result (`Complexity.polyTimeComputable_iterateFind`); all attempts abort with
probability ≤ `2^{-|x|}`, and given success the output has the law of the view. -/
theorem PerfectZKAbort.statZK (h : PerfectZKAbort π R) : StatZK π R (fun n => (2 : ℝ)⁻¹ ^ n)
theorem PerfectZKAbort.zk (h : PerfectZKAbort π R) : ZK π R := h.statZK.zk negligible_two_pow_neg
/-- Sanity (finding #10): the protocol with no messages is perfectly zero-knowledge. -/
theorem perfectZK_zeroRounds (P V : Strategy) (b : Bool) (R) : PerfectZK ⟨P, V, .const 0, b⟩ R
```

`iterateFind` is proved and prints clean (`g03-checks.log:25`). An optional negative lemma, `¬ PerfectZKAbort giProtocol Riso`, would turn the cost into a theorem; its cost is the q > 0 computation above.

**DESIGN §5 item 11** becomes: "`PerfectZK`, `PerfectZKAbort` stated; no source protocol attains them under D8/D10; GI is `StatZK` with negligible δ."

**What ch. 5–8 should cite.**
- The source's "perfect" case of Thm 175.1 is `StatZK.seqRep` with `Negligible δ`, giving error Q·δ, which is negligible. Its instance is `gi_statZK`. The computational case is `ZK.seqRep` (3-colouring).
- `PerfectZKAbort.seqRep` becomes `StatZK.seqRep h.statZK hB Q`. The statement is unchanged and one `sorry` goes away.
- `PerfectZK.seqRep` stays (it is proved) with "no source instance under D8/D10".
- Rewrite `SequentialZK.lean:41–45` and :397–399, and the Thm-175.1 row of `inventory-ch5-8.md`.

**Ripple.**
- 03e: `Defs.lean`, delta re-audit.
- 03k: a cross-reference in `GraphIsomorphismZK.lean:39–43`.
- Prong C: `SequentialZK.lean`.
- 03g is unaffected, since 3-colouring is computational.

### 2.2 Option 2: docstrings only, and drop the perfect forms from ch. 5–8

Apply the docstrings of 2.1 without the bridge. Delete `PerfectZK.seqRep` and `PerfectZKAbort.seqRep`, and remove `PerfectZKAbort` from the S1 interface list. This is the cheapest option. The abort form stays as an unused ch. 2–4 definition.

### 2.3 Option 3: change the model so that graph isomorphism is perfect ZK as in the text

Honest parties and simulators would get exact uniform sampling over finite ranges, or expected-time machines. This changes D8 and D10 (`Strategy.coins`, `NUPPT`) and every ch. 2–4 efficiency and ZK proof. With strict simulators, `PerfectZK` still fails; only expected time fixes the simulator side. Not recommended.

### 2.4 Ruling needed: yes (R-03e-2, §6)

It touches ruling G02-#4, which says that `PerfectZKAbort` composes to statistical ZK and that this is how the text's expected-time simulators are handled.

---

## 3. Minors

| # | Verdict | Severity | Fix | Ripple | Ruling? |
|---|---|---|---|---|---|
| 3 | **True.** `npProtocol_interactiveProof hR T p hT hTR hp` witnesses `∃ π, EfficientProverProof π L R` without `Com` (`InteractiveProofs.lean:402–407`). For `_owp_levinReduction`: the 3-colouring `npProtocol` pulled back along (f, w) (`R3COL_witnessRelation`; its `decidable` is still sorried, `Protocol.lean:784`). The bold titles at `NP.lean:520` and `:549` overclaim; the bodies are accurate. | minor (agree) | Retitle (`NP.lean:520, 549, 598, 623`), e.g. "a ZK protocol with soundness error 1 − 1/p + 2^{−p} whose n\|E\|-fold repetition is an interactive proof". Restate the `_owp_` forms as `∃ Com ℓ, Commitment Com ℓ ∧ <conclusion of zk_proof_of_levinReduction>`, which ties the two protocols together. Record the text's Thm 124.1 (ZK with negligible soundness) as debt. **Missed:** prong C cannot discharge that debt. `InteractiveProof.seqRep` (`SequentialZK.lean:426`) needs negligible ε and uses only phase 0. No `InteractiveProofErr.seqRep` (error s^Q) exists (R-03e-4). | 03e (`NP.lean`); 03g lists Thm-124.1 in its inventory; prong C if R-03e-4 option 1 | R-03e-4 for the debt; the rest is the maintainer's |
| 4 | **True.** The proof (`NP.lean:618–621`) uses only `hR` and `h3 L R hR`. | minor (agree) | State `zk_proof_of_mem_NP` and `_of_owp` for every `R` with `WitnessRelation L R` (conclusion without `∃ R`). Keep the `L ∈ NP` form as a one-line corollary through `exists_witnessRelation_of_mem_NP`. | 03e only; ch. 5–8 does not cite Thm 124.1 | no |
| 5 | **Partly true.** (a) and (b) are true: the evidence has no prints of `LevinReduction.zk`, `.efficientProverProof(Err)`, `Strategy.pullback_efficient` or `Commitment.multiHiding`. (c) is reconciled: the core sorries are in `main`'s code (`TuringMachine/Build/Loop.lean` last touched by `700bd8c8` "MIG-1 stage S … 17 sorried"). Run 3's line "the `TuringMachine/Build/*` files of run 3b print 0" (`run3-audit-summary.md:17`) means `Complexity/Randomized/Build/*`: the six run-3b files, all at 0 sorries now. The non-ZK count is 22, or 21 without `NonUniform`. The sorried declarations behind the four `sorryAx` prints are almost certainly `colRep_efficientProverProof` (`Protocol.lean:851`) and `col_zk` (`Simulator.lean:764`): `col_efficientProverProofErr` prints clean (`g03-checks.log:349`). The missing `LevinReduction.*` prints would confirm this. | minor (agree) | Add prints for (b) to `audits/pass-shelat/Checks.lean`. Annotate each `sorryAx` print with "reaches `colRep_efficientProverProof`, `col_zk` (pack 03g)". Correct the path in the run-3 summary line. Note in 03e's attestation that the 22 core sorries are `main`'s. | evidence and records only; 03g (the stubs) | no |
| 6 | **(a), (b) true; (c) unverified.** (a) `Defs.lean:72–73` has no tag; `:50`, `:141` cite "[Goldreich, …]". The same in `GraphIsomorphismZK.lean:284` (03k) and `SequentialZK.lean:82–84` (prong C). (b) Checked against the ingested p. 116: the source says "regardless of the content of A and B's random tapes" and, separately, "independently of the content of the messages it receives". `ReadsPrefix` (`Interaction.lean:170–171`) quotes the second verbatim. `Efficient` (:148, "regardless of the messages") and the module docstring (:42, "regardless of messages") misquote. (c) AB09 ch. 2 is not ingested. My recollection agrees with the auditor (§2.3.6), but this is not verified. | minor (agree) | (a) Tag `[Gol01]` (prong B uses `[Gol04]` for vol. 2) in `Defs.lean`, `GraphIsomorphismZK.lean` and `SequentialZK.lean`. (b) Replace the quotation marks at :42 and :148 with a paraphrase, or quote the "independently of …" sentence. (c) Check against AB09. If the book is not at hand, cite `[AB09, §2.3]`. | 03e; 03k (tag); prong C (tag) | no |

---

## 4. Notes

| # | Verdict | Severity | Fix | Ripple |
|---|---|---|---|---|
| 7 | **True.** No ch. 2–4 ZK theorem depends on the gap. `LevinReduction.zk` (`NP.lean:449`) handles every `Efficient` V\*. The graph-isomorphism and 3-colouring honest messages have a fixed shape. This answers Q-1, which the user has already ruled (option 1: no cap on V\*). Under R-03e-1 option 1, the honest prover's messages are bounded, so every `Efficient` V\* has a polynomially bounded view: the auditor's reasoning. | note (agree) | Record the ruling in `Defs.lean`'s `ZK` docstring ("V\* is uncapped; with `ProverBounded` its view is polynomially bounded"). No statement change. | 03e docstring; none in ch. 5–8 |
| 8 | **True.** The convention already exists in three places: the dummy fourth move of `giProtocolRep` (`GraphIsomorphism.lean:554–558`) and `colProtocolRep`, and prong C's filler moves (`SequentialZK.lean:21–26`). | note (agree) | One sentence in `Interaction.lean`'s module docstring naming the dummy-move convention and these users. | 03e docstring |
| 9 | **True.** DESIGN §3 gives the weaker reason. Necessity follows because the distinguisher's time is polynomial in the encoded view, which contains z. | note (agree) | Add the necessity argument to `Defs.lean:32–39`. Add the source issue to DESIGN §7. | 03e docstring; DESIGN |
| 10 | **True.** **Pack labels swapped:** `gi_statZK` is 03k and `col_zk` is 03g. | note (agree) | Add `perfectZK_zeroRounds` (§2.1). Name `gi_statZK` as the substantive instance in the `Defs.lean` module docstring. | 03e |
| 11 | **True**, checked against the appendix raw text (lines 139–148): Def 191.11 bounds only the counting witnesses. | note (agree) | One docstring sentence at `InteractiveProofs.lean:177–183`. | 03e |
| 12 | **True, and already met.** `colVerify` requires `ri.length = ℓn ∧ rj.length = ℓn` (`ThreeColoring/Protocol.lean:144`), and the values are `List.ofFn (padColor n a)`, n bits. The pointer belongs to **03g**, not 03k. | note (no action) | None. Optionally, one sentence in `Commitment`'s docstring: "users must check lengths, as `colVerify` does". | none |
| 13 | **True; premise out of date.** `exists_owp_hardCore` (`HardCorePermutation.lean:676`) is proved, and both it and the GL modules print clean (`g03-checks.log:395`; replay `sorry=0`). | note (agree) | Add `exists_commitment_of_owp (h : ∃ P, OneWayPermutation P) : ∃ Com ℓ, Commitment Com ℓ := exists_commitment_of_owp_hardCore (exists_owp_hardCore h)`, in `Commitment.lean` (importing `HardCorePermutation`) or in `NP.lean`. Optionally give `zk_proof_of_*_of_owp` the text's hypothesis. | 03e only; 03i's files untouched (consumer only) |
| 14 | **True.** The padding remark (`NP.lean:35`) needs instance lengths q(N)², since `encGraph` lengths are perfect squares. Achievable with p := q·q. The pointer belongs to **03g** (`L3COL` lives in `ThreeColoring/Language.lean`). | note (agree) | Weaken to "assumed (padding with isolated vertices gives p = q², q ≥ √N)", or prove it in 03g. | 03e docstring; 03g |
| 15 | **True** (Barak–Lindell matches my knowledge). | note (agree) | Record (a) and (b) in the ch. 5–8 bridge notes (S1 note addendum). | ch. 5–8 records |
| 16 | **Partly true.** Thm-124.1 and Claim-124.d are missing from **03e**'s list, but they are already in **03g**'s inventory list (`03g-pack.md:39`, where `NP.lean` is context). Def-119.e and Claim-122.b are optional (`inventory-ch4.md:161, 173`). | note (agree) | Add the two ids to 03e's list with "(also 03g)", or say in 03e that 03g owns them. | pack text |
| 17 | **True.** 15 lemmas: `Interaction.lean` 10, `InteractiveProofs.lean` 2, `Commitment.lean` 3 (grep). | note (agree) | Approve rather than remove. Downstream proofs `simp` through them: `SequentialZK.lean:118–174` (moverIsV and exec goals) and `Strategies.lean:162`. Removal would need a sweep of the ch. 5–8 proofs. | 03e; prong C and S2b if removed |

**Q1 (also asked of 03g and 03k).** Both decoders map `[]` to a legitimate challenge:
- graph isomorphism: `(hist.headD []).headD false = false`, so b = 0 (`GraphIsomorphism.lean:495`);
- 3-colouring: `edgeIdxOfMsg m [] = 0`, so edge 0 (`Language.lean:321`).

---

## 5. What the auditor missed

1. `ProverBounded` is not derivable from `ReadsPrefix`: it quantifies over every tape and history, and |y| must be bounded (§1, correction 1).
2. The 3-colouring prover and verifier are not prefix-reading (§1, correction 2). Option (i) and the "caps as conjuncts" fallback both need 3-colouring redefinitions and a bound on `Com`'s output.
3. The bound must sit in `InteractiveProof`'s completeness clause. With R = ∅, `EfficientProverProof π HALT ∅` holds whatever is added on the R side (§1, correction 4).
4. Major 2's obstruction is inherent to fair-bit honest provers (6 ∤ 2^c). `PerfectZK` fails a second time on the simulator side (§2).
5. The cost of Major 2 is already declared in `GraphIsomorphismZK.lean:39–43`. The misleading text is in DESIGN §5 item 11 and `SequentialZK.lean:41–45, 397–399`.
6. The text's Thm 124.1 debt cannot be discharged by ch. 7 as stated: no soundness amplification for `seqRep` exists (#3, R-03e-4). Note also that `colProtocolRep` is not `colProtocol.seqRep`; the move layouts differ.
7. Pack labels: 03g is 3-colouring and 03k is graph isomorphism (PLAN.md). The labels are wrong in #5, #10, #12 (pointer), #14 and #16, and in 03e's own scope line ("graph isomorphism, 3-colouring: packs 03g and 03k").
8. #12 is already met; #13's premise is out of date; #5(c) is reconciled (main's sorries, a path slip in the run-3 summary).
9. The field docstrings "The verifier/prover is a PPT strategy" (`InteractiveProofs.lean:100, 119, 272, 282`) and the second misquote (`Interaction.lean:42`).
10. Removing the 15 `@[simp]` attributes would break downstream proofs (#17).

---

## 6. Rulings for the user (multiple choice; recommended option first)

**R-03e-1. Efficiency of the parties in ch. 2–4's proof systems (Major 1).** Defs 116.1 and 119.5 say "p.p.t."; the structures require only `Strategy.Efficient`.
1. **`Efficient` plus bounded honest messages, as ruled for ch. 6 (recommended).** `InteractiveProof`'s completeness uses honest-prover messages of at most B(\|x\|) bits, and `EfficientProverProof(Err)` carries `∃ B, π.ProverBounded R B`. `ProverBounded` moves from prong C into `Interaction.lean`.
   - *Cost:* about five short bound lemmas (`npProtocol`, graph isomorphism, GNI, 3-colouring through `PolyTimeComputable.output_length_le`, pullback). The affected theorems are re-proved with unchanged statement text. 03g and 03k audit the new lemmas, and 03e gets a delta re-audit.
   - *Ch. 5–8:* `ProverBounded` moves and becomes derivable from `EfficientProverProof`. Thm 175.1 may state the text's "ZK proof".
   - *Excludes undecidable languages*, since the verifier can be capped. Residual declared deviation: V's work against a cheating prover is polynomial in the message length. Q-1's choice (`Efficient` kept, no `ReadsPrefix`) stands.
2. **Keep the definitions and acknowledge the cost.** Only docstrings change ("efficient (D8)", a deviation note, a DESIGN §5 entry).
   - *Cost:* no code changes. You acknowledge that the structures are satisfiable for languages outside the text's IP (e.g. HALT), so "is an interactive proof" in ch. 2–4 and 5–8 theorems asserts less than the text. Ch. 4 and ch. 6 keep different conventions. Thm 175.1's `ProverBounded` has no ch. 2–4 source.
3. **Require `ReadsPrefix` of V (and of P) in the structures**, as the auditor proposes. Closest to the text for V.
   - *Cost:* the 3-colouring prover and verifier must be redefined, and the verifier's cap needs an output-length bound for `Com`: a new `colProtocol` parameter, which changes the Thm 124.1 statements, or a new `Commitment` field, which changes an interface type. `IP` changes.
   - `ProverBounded` is still not derived, so Thm 175.1 keeps `hB` or `ProverBounded` is restated over executions. This is the largest 03g rework.

**R-03e-2. Perfect zero knowledge (Major 2).** No source protocol attains `PerfectZK` or `PerfectZKAbort` under D8 and D10.
1. **Keep both, state the cost, prove the bridge `PerfectZKAbort.statZK` (error 2^{−\|x\|}) and `.zk`, and have ch. 5–8 cite `StatZK.seqRep` with negligible δ (`gi_statZK`) as Thm 175.1's "perfect" case (recommended).**
   - *Cost:* one ch. 2–4 lemma with a retry machine (`iterateFind` is proved), docstrings in `Defs.lean`, DESIGN §5 item 11 and `SequentialZK.lean`, and the inventory row.
   - `PerfectZKAbort.seqRep` becomes a corollary (one `sorry` fewer). The wording of G02-#4 is corrected; its substance (strict or truncated simulators) stands.
2. **Docstrings only, and drop `PerfectZK.seqRep`, `PerfectZKAbort.seqRep` and `PerfectZKAbort` from the ch. 5–8 interface.**
   - *Cost:* the lowest. Ch. 7 states composition for `ZK` and `StatZK` only, and the abort form stays unused.
3. **Change the model** (exact uniform sampling over finite ranges, or expected-time machines) so that graph isomorphism is perfect ZK as in the text.
   - *Cost:* D8 and D10 change, and every ch. 2–4 efficiency and ZK proof is redone. `PerfectZK` still fails without expected time. Months of work.

**R-03e-3. The 15 `@[simp]` lemmas of this pack (#17).**
1. **Approve all 15 (recommended).** They are definitional unfoldings (`rfl`, apart from `withV_self`), and ch. 5–8 proofs rely on them. *Cost:* none.
2. **Approve the 10 in `Interaction.lean`; remove the other 5.** *Cost:* re-check the users of `mem_witnessLanguage`, `mem_witnessSet`, `bitCom_*` and `owpComLen_eval` (03e, 03g, 03k).
3. **Remove all 15.** *Cost:* a sweep of ch. 2–4 and ch. 5–8 proofs (`SequentialZK.lean`, `Strategies.lean`).

**R-03e-4. The text's Thm 124.1 (ZK with negligible soundness) (#3).**
1. **Add `InteractiveProofErr.seqRep` to prong C (sequential repetition multiplies the soundness error: s^Q), plus a ch. 7 corollary combining `ZK.seqRep` with it for `colProtocol` (recommended).**
   - *Cost:* one new ch. 5–8 statement and one corollary.
   - *Benefit:* discharges the declared DQ5 debt in the text's form.
2. **Record the debt only.** *Cost:* none now; Thm 124.1 stays in the one-iteration form.

---

## 7. Ripple map

| Change | ch. 2–4 files (gate 03 pack) | ch. 5–8 files |
|---|---|---|
| R-03e-1 option 1 | `Interaction.lean`, `InteractiveProofs.lean`, `NP.lean` (03e); `GraphIsomorphism.lean`, `GraphIsomorphism/{Soundness, SoundnessRep, SoundnessRepGI}.lean` (03k); `ThreeColoring/{Protocol, Simulator}.lean` (03g) | prong C `SequentialZK.lean` (`ProverBounded` moved; `InteractiveProof.seqRep` sketch) |
| R-03e-1 option 2 | docstrings in `Interaction.lean`, `InteractiveProofs.lean`, `NP.lean` (03e) | prong C docstring cross-reference |
| R-03e-1 option 3 | 03e as in option 1 plus `IP`; 03k prefix lemmas; 03g redefinitions (`Language.lean:321`, `Protocol.lean:406–502`, `ProtocolProofs.lean`, `Machines.lean`, `Simulator*.lean`); possibly `Commitment.lean` (03e) | prong C `InteractiveProof.seqRep`; `ProverBounded` kept or restated |
| R-03e-2 option 1 | `Defs.lean` (03e); `GraphIsomorphismZK.lean:39–43` cross-reference (03k) | prong C `SequentialZK.lean` (docstrings; `PerfectZKAbort.seqRep` becomes a corollary); `inventory-ch5-8.md` |
| #3, #4, #13 | `NP.lean`, `Commitment.lean` (03e) | none |
| #5 | `audits/pass-shelat/Checks.lean`, evidence, run-3 summary line | none |
| #6 | `Defs.lean`, `Interaction.lean`, `NP.lean` (03e); `GraphIsomorphismZK.lean` (03k, tag) | `SequentialZK.lean` (tag) |
| #17 (if removed) | 03e files | `SequentialZK.lean`, `Strategies.lean` |

**Prong B** (`SecureComputation/*`) uses `Protocol`, `Strategy.Efficient` and its own `Functionality.PolyTime`. No option above touches it. **S2b** `Games/Bridges/Strategies.lean` uses `Strategy`, `exec` and `Protocol` only, so it is untouched except under R-03e-3 option 3.

**Pending packs:**
- **Unaffected** by any fix of this pack: 03d, 03f1, 03f2, 03h, 03i, 03j, 03l. 03i is only a consumer of `exists_owp_hardCore` (#13); 03l is only a consumer of `iterateFind` (R-03e-2 option 1).
- **03g** (3-colouring) carries the R-03e-1 obligations (option 1: one bound lemma; option 3: a redesign), the #14 pointer, the #5 stubs and the Q1 confirmation.
- **03k** (graph isomorphism, GNI, `NPLemmas`) carries the R-03e-1 bound or prefix lemmas, the R-03e-2 cross-reference and the #6(a) tag.
- Before dispatch, correct 03e's scope line and point 03g and 03k at the rulings.

## 8. Proposed closing condition for 03e

The pack closes when:
- R-03e-1 and R-03e-2 are ruled, and their ch. 2–4 parts have landed;
- the docstring corrections of §3 and §4 are in;
- a delta check confirms the changed statements: the structures in `InteractiveProofs.lean` and `Interaction.lean`, and `Defs.lean`'s docstrings and bridge.

The ch. 5–8 re-syncs (prong C) follow in the same PR, per PLAN.md.
