# Gate 03e — findings ([PS10] ch. 2–4: interaction, interactive proofs, ZK definitions, commitments, the NP layer)

- **Pack:** `briefs/pass-shelat-ch5-8/gates/03-ch2-4/03e-pack.md` (brief and severity guide of pack 03a).
- **Commit audited:** `a3c5fa8b72e50939822f22364647dc844a3914a0`, branch `cryptography/pass-shelat-ch2-4`.
- **Files under audit:** `TCSlib/Cryptography/ZeroKnowledge/{Interaction, InteractiveProofs, Defs, Commitment, NP}.lean`.
- **Auditor:** external statement audit, 2026-11-05.
- **Source availability:** the [PS10] PDF was **not** in the upload (only the bundle arrived), and the session's
  network policy refused `www.cs.cornell.edu`. I checked fidelity to the source against the bundle's
  transcriptions (mainly `inventory-ch4.md` §3, DESIGN §7) and my own knowledge of [PS10]. Three items that
  need the page itself are marked **verify against PDF**. No other conclusion depends on the PDF.

## Verdict

**The pack does not close: 0 blockers, 2 majors, 4 minors, 11 notes.**

- **Major #1.** The run-3 repair P9-1 put the message-prefix cap only on the class `IP`. The proof-system
  structures that the theorems conclude and that ch. 5–8 cites (`InteractiveProof`, `InteractiveProofErr`,
  `EfficientProverProof`, `EfficientProverProofErr`) still accept parties whose work is polynomial in the
  length of the other party's messages rather than in |x|. These structures can be satisfied for undecidable
  languages. The uncapped honest prover is also the root cause of the maintainer's "known consequence" (Q-1).
- **Major #2.** `PerfectZK` and `PerfectZKAbort` are faithful as definitions. In this model, though, the
  source's perfect-ZK protocol (graph isomorphism) cannot satisfy them, no lemma connects `PerfectZKAbort` to
  `ZK`, and neither docstring states either cost. Both are on the ch. 5–8 interface.

No statement in the five files is false, and every run-3 repair in scope holds for what it touched (§3).

## 1. Findings

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | **major** | `InteractiveProofs.lean` · `InteractiveProof`, `InteractiveProofErr`, `EfficientProverProof`, `EfficientProverProofErr`. Every theorem concluding them inherits the problem: in this pack `LevinReduction.efficientProverProof(Err)`, `zk_proof_of_levinReduction`, `zk_proof_of_owp_levinReduction`, `zk_proof_of_mem_NP(_of_owp)`, `npProtocol_interactiveProof`. | Def 116.1 says "V is PPT" and Def 119.5 says "P is PPT". Both mean time t(\|x\|) whatever the messages. The structures only require `Strategy.Efficient`, which allows time polynomial in \|x\|+\|z\|+\|messages\|. P9-1 added `ReadsPrefix` to `IP` alone, so the proof systems themselves are still not the source's: they are satisfiable for languages outside the text's IP, and every theorem concluding them asserts less than the source does. `EfficientProverProof`'s docstring calls P "a PPT strategy" with no D8 caveat. The uncapped honest prover is exactly what makes the maintainer's ZK blow-up possible, which is why ch. 5–8 has to assume `ProverBounded`. | **(a) RE counterexample.** L = HALT. R x y holds iff y is a halting computation history of x. π is shaped like `npProtocol`, but V outputs `[T ⟨x, m⟩]` on the *whole* message m, with no `take`. V is `Efficient` (T is polynomial in \|⟨x,m⟩\|). P copies y and is `Efficient`. Completeness: P sends the history. Soundness holds with ε n = 2⁻ⁿ, since no history exists for x ∉ HALT. So `EfficientProverProof π HALT R` holds. This is P9-1's own counterexample for `IP`, and it still applies to the structures. **(b) The blow-up.** A prover that echoes V\*'s message is `Efficient`, and so is a V\* that doubles its message each turn. After k turns the view has length at least 2ᵏ. If instead `P.ReadsPrefix m`, then `P.next … hist = A.runAtL … (trunc hist)`. The output length is then at most `Ct·(poly(\|x\|+\|y\|+rounds·m(\|x\|))+1)^ct`, whatever V\* sends, so `ProverBounded` becomes a lemma. **(c)** All four Thm 124.1 forms conclude only `Efficient` for both parties. | Add `readsPrefixV : ∃ m : PolyExpr, π.V.ReadsPrefix m` to `InteractiveProof` and `InteractiveProofErr`, and `readsPrefixP : ∃ m, π.P.ReadsPrefix m` to `EfficientProverProof(Err)`. Then `IP := {L \| ∃ π, InteractiveProof π L}`. Add `ReadsPrefix.pullback`: a pulled-back party reads m(p(\|x\|)) bits, so the cap is `m.subst p`. Discharge the caps: `npProtocol` already has them (`npProtocol_readsPrefix`; P ignores the history); packs 03g and 03k do theirs. Decoders with exact-length checks are determined by the m-bit prefix once m exceeds the decoded length. Then prove `ProverBounded` from `EfficientProverProof` for ch. 5–8. *Alternative:* keep D8, record an explicit human acknowledgment of the cost above, change "PPT" to "Efficient (D8)" in the docstrings, and add the caps as conjuncts to the Thm 124.1 headlines. |
| 2 | **major** | `Defs.lean` · `PerfectZK`, `PerfectZKAbort` (cited by ch. 5–8) | Both are faithful definitions: Def-122.a with a strict simulator, and Goldreich's Def 4.3.1 with ⊥ = `[]` (never a view encoding, so the conditional-law clause is right). In this model, however (honest parties drawing bit coins, strict-PPT simulators), the source's perfect-ZK protocol satisfies neither. Nothing derives `ZK` or `StatZK` from `PerfectZKAbort`. Neither docstring states these costs; DESIGN D-register 11 even calls `PerfectZKAbort` "the perfect form". A ch. 5–8 statement that instantiates either with a source protocol cannot be proved; one that assumes either has no ch. 2–4 instance. | GI as specified in DESIGN §2.15 (run-3 repair): the honest prover draws π with `samplePerm … = (permFromCoins …).getD 1`, sends H = π(G₀), and on b = 1 sends γ = π·σ⁻¹. Take G₀ = G₁ = the empty graph on 3 vertices. All 6 permutations are witnesses. `permFromCoins 3 (Nat.size 3) (2·3²)` rejection-samples the Fisher–Yates offsets from 2-bit blocks, so it fails with some probability q > 0. By run-3 P2-1, the range-1 position alone fails with probability (1 − 2⁻²)¹⁸. Let V\* always answer 1. Then γ has law (1−q)·Unif(S₃) + q·δ_{σ⁻¹}, which depends on the witness σ. The simulator never sees σ, so its law, or its law conditioned on not aborting, can match at most one witness. Hence `PerfectZK giProtocol Riso` and `PerfectZKAbort giProtocol Riso` are both false. `gi_statZK` is unaffected: the distance is at most q. 3COL is only computationally hiding. The only instances of either notion are degenerate protocols, e.g. 0 messages, where the simulator outputs ⟨x, z, r, []⟩. | (1) In both docstrings, state that with bit-coin parties the source's perfect-ZK protocol (GI) does not attain these notions, and that it is formalized as `StatZK` with negligible δ. (2) Either prove `PerfectZKAbort.statZK : PerfectZKAbort π R → StatZK π R (fun n => 2⁻¹ ^ n)` (run the simulator \|x\| times on fresh coins with the proved `iterateFind`) together with `PerfectZKAbort.zk`, or drop `PerfectZKAbort` from the ch. 5–8 interface. (3) Tell ch. 5–8 to state the source's "perfect ZK" results as `StatZK δ` with `Negligible δ`, which is the form `gi_statZK` supplies. |
| 3 | minor | `NP.lean` · `zk_proof_of_owp_levinReduction`, `zk_proof_of_mem_NP`, `zk_proof_of_mem_NP_of_owp`; title of `zk_proof_of_levinReduction` | The first conjunct of the ∃-forms, `∃ π, EfficientProverProof π L R`, says nothing about the ZK protocol, because `npProtocol` already witnesses it. So these headlines only assert: some π is ZK with soundness error 1 − 1/p + 2^{−p}. No protocol is shown to be ZK with negligible soundness. The bold titles say "has a zero-knowledge proof" (`_owp_levinReduction`) and "give a zero-knowledge proof for L" (`_levinReduction`). The one-iteration scope (DQ5) is declared, but splitting the ∃ hides the link to `colProtocolRep` that the named form shows. | `zk_proof_of_mem_NP`: from `hR`, `⟨npProtocol T p, (npProtocol_interactiveProof hR T p hT hTR hp)⟩` proves the first conjunct without `Com` or `h3`. In `zk_proof_of_owp_levinReduction`, the 3COL `npProtocol` pulled back along `(f, w)` does the same, provided `R3COL` is a witness relation. | Retitle, e.g. "…give a zero-knowledge protocol with soundness error 1 − 1/p(\|x\|) + 2^{−p(\|x\|)} whose repetition is an interactive proof". In the ∃-forms, either drop the uninformative conjunct or tie the two protocols together (∃ Com ℓ, statements about `colProtocol Com ℓ` and `colProtocolRep Com ℓ`, as the named form does). Record the text's Theorem 124.1 ("ZK proof", negligible soundness) as debt that ch. 7's sequential composition discharges. |
| 4 | minor | `NP.lean` · `zk_proof_of_mem_NP`, `zk_proof_of_mem_NP_of_owp` | The theorems are stated for ∃ R, namely the canonical relation chosen inside `exists_witnessRelation_of_mem_NP`. ZK is relative to a witness relation, and `LevinNPHard` already covers every `WitnessRelation`. So the statement is weaker than it could be at no cost, and a user with a natural relation (e.g. `Riso`) cannot apply it. | The proof only uses `h3 L R hR` and `hR.mem_iff`, both available for any R. | State `∀ R, WitnessRelation L R → (∃ π, …) ∧ ∃ π p, …` and keep the ∃ R version as a one-line corollary from `hL : L ∈ NP`. |
| 5 | minor | Attestation: `evidence/e/axioms.log`, `replay.log`, D11 | (a) The four `sorryAx` prints (the Thm 124.1 forms) do not name the admissions they rest on, as D11 requires. (b) Some of the pack's own headlines have no print: `LevinReduction.zk`, `LevinReduction.efficientProverProof(Err)`, `Strategy.pullback_efficient` (Claim-124.d), and `Commitment.multiHiding` (Claim-126.a, listed under Main results). (c) The closure has 21 `sorry` warnings in core machine modules. The run-3 summary records the `TuringMachine/Build/*` files at 0, and nothing in the pack reconciles the two. | My tally of `replay.log`: 358 modules, all rc=0, 0 errors, 25 `sorry` warnings. These are `TuringMachine/Build/{Loop 5, Primitives 3, RecordTable 4, Wrappers 2}`, `TuringMachine/{Composition 3, Encoding 1, Simulation 1}`, `ClassP/TimeConstructible 2`, `Randomized/NonUniform 1`, `ThreeColoring/Protocol 2` and `ThreeColoring/Simulator 1`. The 22 clean prints show the core-module sorries are not on *their* paths; the bundle does not show this for the four `sorryAx` prints. | Append prints for (b) to `Checks.lean`. For each `sorryAx` print, list the sorried declarations it reaches; I expect the three 3COL stubs of pack 03k. Reconcile the 21 core-module sorries with run 3's record and D11's admissions policy, or name them. |
| 6 | minor | Attribution (policy §2): `Defs.lean`, `Interaction.lean`, `NP.lean` | (a) `Defs.lean` lists Goldreich's *Foundations I* without a short tag, and its declarations cite "[Goldreich, Definition 4.3.1]". (b) `Strategy.Efficient` quotes the text as "regardless of the messages", while `Strategy.ReadsPrefix` quotes "independently of the content of the messages it receives". Both purport to quote the same sentence on p. 116, so at most one is verbatim. **Verify against PDF.** (c) `NP.lean` cites "[AB09, §2.3.3, Levin reductions]". To my knowledge, AB09's remark on Levin reductions is in §2.3.6 ("More thoughts on the Cook–Levin theorem"). **Verify.** | Policy §2 requires full citations with short tags, and quotation marks must be accurate. | Add a tag (e.g. `[Gol01]`). Quote p. 116 verbatim in one place and paraphrase elsewhere. Correct the AB09 section if needed. |
| 7 | note | `Defs.lean` · `ZK`, `StatZK`, `PerfectZKAbort` (maintainer's Q-1) | **Answer to Q-1.** No ch. 2–4 ZK theorem depends on the gap. `LevinReduction.zk` is proved for the stronger (uncapped-V\*) notion and uses nothing about message lengths. The GI and 3COL honest provers send fixed-length messages, so V\*'s view is polynomially bounded for every `Efficient` V\*. No ch. 2–4 theorem composes ZK protocols. **Should `ZK` require `ReadsPrefix` of V\*?** It is not needed once the honest prover is capped (#1): then V\*'s received messages are bounded, its activations run in time polynomial in bounded inputs, and every V\* behaves like a capped one. In that situation the current `ZK` is at least as strong as Def 121.2 and still attainable. Capping V\* too would make `ZK` exactly the text's notion; that is optional. | Capping V\* would need a small change in `LevinReduction.zk`. `liftVerifier V*` reads m(\|x\|) bits, where x = `pairFstD z'` is arbitrary, so it is not literally `ReadsPrefix m` at parameter \|x'\|. A lift that first truncates each message to m(\|x'\|) bits is capped by m, and it agrees with `liftVerifier V*` on every execution the proof uses, because there \|x\| ≤ \|x'\|. | Recommend fix #1, which handles both the blow-up and the RE problem, and decide Q-1 as "no cap on V\* needed". If the user prefers to cap V\* instead, add `∀ m, V'.ReadsPrefix m →` to `ZK`, `StatZK` and `PerfectZKAbort` (and to the honest V in `HVZK`, `StatZK.hvzk` and `ZK.hvzk`). Either way, record the ruling. |
| 8 | note | `Interaction.lean` · `exec`, `Protocol`, `outV` (Q1, D8) | **Fixed alternation is benign for ch. 4** (details in §2, Q1). It costs two things. Sequential repetition of a protocol with an odd number of messages (GI and 3COL iterations go P,V,P) is not a strict-alternation `Protocol` until consecutive same-party messages are merged or dummy messages are inserted. The n-fold protocols of 03g/03k and ch. 7's composition operator must fix one convention. The verdict convention (P9-3) rules out no source protocol: append one dummy prover message. | See §2, Q1. | None required. Record the merge-or-dummy convention once, in `Interaction.lean`, so that ch. 7 cites it. |
| 9 | note | `Defs.lean` · the `∀ Lz` clause of `ZK` and `HVZK` (D8) | The bound on \|z\| is *necessary*, not just convenient. The distinguisher's running time is polynomial in its input, which is the encoded view and contains z. With \|z\| ≥ 2ⁿ it could invert the OWP on n-bit inputs and open the unopened 3COL commitments, so computational ZK would fail for every protocol whose hiding is only computational. Read literally, the text's Def 121.2 ("∀ z ∈ {0,1}\*", D running in time polynomial in its input) has the same defect. The docstring gives weaker reasons ("what a t(\|x\|)-time verifier can read", Prop 128.8). Indexing D's advice by \|x\| rather than by input length is likewise necessary. | Adversarial instantiation I3 (§4). | Add the necessity argument to the D8 docstring, and add this source issue to DESIGN §7 (beside item 50). |
| 10 | note | `Defs.lean` (non-vacuity) | No declaration in the pack shows that any ZK notion is satisfiable. The substantive instances are `gi_statZK` (03g, outside this closure) and `col_zk` (03k, which reaches `sorry`). | Within this closure, every `ZK` headline about a non-degenerate protocol prints `sorryAx`. | Add the trivial sanity lemma: the 0-message protocol is `PerfectZK` and `ZK` for every R. Name `gi_statZK` in the module docstring as the substantive instance. |
| 11 | note | `InteractiveProofs.lean` · `WitnessRelation` | The definition makes R itself polynomially bounded (`∀ x y, R x y → \|y\| ≤ p(\|x\|)`). Def 191.11 bounds only the witnesses that count (`∃ y, \|y\| ≤ p(\|x\|) ∧ (x,y) ∈ R_L`). The two agree at the level of languages (intersect R_L with the bound). The bounded form suits Def 119.5's "for every y ∈ R_L(x)", since a time-t(\|x\|) prover cannot read a longer y. | Benign. | State the daylight in the docstring. |
| 12 | note | `Commitment.lean` · `Commitment.binding` | Binding is required only for values of the same length n with randomness of length exactly ℓ(n), as in the text. For a general `Commitment`, the 3COL verifier (03k) must therefore check \|opened value\| = n and \|r\| = ℓ(n), or a cheating prover may open to an out-of-range pair. `owpComStr` is in fact binding for all randomness strings (`owpComAt_inj` has no length hypotheses), but `zk_proof_of_levinReduction` is stated for an arbitrary `Commitment`. | — | Pointer for pack 03k: confirm that the verifier checks lengths. |
| 13 | note | `Commitment.lean` · `owp_commitment`, `exists_commitment_of_owp_hardCore` | The text's form of Thm 126.4, "if OWPs exist then commitments exist", is not stated. The hard-core predicate is a declared hypothesis. The text's form needs GL (`exists_owp_hardCore`, in `HardCorePermutation.lean`; sorried at run 3 and not in this closure). Neither `_of_owp` form of Thm 124.1 is the text's form either. | Declared deviation; benign. | Add `exists_commitment_of_owp : (∃ P, OneWayPermutation P) → ∃ Com ℓ, Commitment Com ℓ` from `exists_owp_hardCore`, so the debt shows up in `#print axioms`. |
| 14 | note | `NP.lean` · `LevinReduction` (length regularity), `LevinNPHard` | The `length_eq` and `le_eval` conditions are necessary. Without p ≥ id, an f that shrinks lengths makes ε′(\|f x\|) non-negligible in \|x\| and leaves the lifted verifier and distinguisher short of coins and parameter. The remark "achievable by padding with isolated vertices" depends on `L3COL`'s encoding admitting instances of every length p(N) (pack 03k). `LevinNPHard` is an unproved hypothesis; I find it plausible. Form (A) is non-vacuous via `LevinReduction.refl L3COL R3COL`. At N = 0 the error 1 − 1/p(0) + 2^{−p(0)} may be ≥ 1, because Lean's 1/0 = 0; this is a boundary case only. | — | Pointer for 03k: prove that `L3COL` can be padded, or weaken the docstring remark to "assumed". |
| 15 | note | D8 as a whole (fitness for ch. 5–8) | (a) Strict-PPT simulators: Barak–Lindell (SICOMP 2004, "Strict polynomial-time in simulation and extraction") show that constant-round zero-knowledge with *black-box* strict-PPT simulation exists only for BPP. If ch. 5–8 reaches constant-round ZK with negligible soundness, D8 cannot express it black-box; sequential composition (the 2026-11-05 ruling) is unaffected. (b) Everything is indexed by \|x\|: coins, rounds, simulator and distinguisher parameter, ε(\|x\|), and `Commitment`'s n = \|v\|. A ch. 5–8 protocol with a separate security parameter must encode it into x (e.g. ⟨1ⁿ, x₀⟩) or pad values to n bits. | — | Record both limits in the ch. 5–8 bridge notes. |
| 16 | note | Inventory | Def-119.e (interactive argument) and Claim-122.b (view-based vs output-based ZK) are not formalized. Both are optional per DESIGN §6.2. Thm-124.1 and Claim-124.d are in `NP.lean` but missing from the pack's inventory list; I audited them anyway (§5). | — | Add the two ids to the pack's list, or move them explicitly to 03k. |
| 17 | note | Policy §1: `@[simp]` | 15 lemmas in the five files carry `@[simp]`. `Interaction.lean` has 10 (`encodeMsgs_nil/cons`, `moverIsV_true/false`, `exec_zero`, `withV_V/P/rounds/verifierFirst/self`), `InteractiveProofs.lean` has 2 (`mem_witnessLanguage`, `mem_witnessSet`) and `Commitment.lean` has 3 (`bitCom_castSucc/last`, `owpComLen_eval`). The user rule of 2026-10-16 requires a gate to approve each. The bundle records no approval. | — | Approve them at this gate or remove the attribute. |

## 2. Answers to the pack's specific questions

**Q1. Interaction model (Defs 114.a–116.b, D8).**
- *Is fixed alternation benign for ch. 4?* Yes:
  - Every ch. 4 protocol has a fixed number of messages once its iteration count is a `PolyExpr` in |x|.
  - A text V\* that halts early corresponds to a formal V\* that sends `[]` and then sees the honest
    prover's remaining messages. Its text view is a prefix of the formal view. A simulator for the formal
    view, followed by truncation (efficient closure), simulates the text view. So formal ZK implies text ZK
    for such verifiers.
  - The honest prover's reaction to `[]` is part of the protocol's specification. Because the decoders are
    total, `[]` should decode to a default, legitimate challenge, revealing nothing a legitimate V\* could not
    learn. Packs 03g and 03k should confirm this for the GI and 3COL decoders, which are not in this bundle.
  - A cheating prover that halts early: the formal reading (the verdict is computed on the full history) is
    the only one under which Def 116.1 can be satisfied (DESIGN §7 item 50).
  - The cost is #8: repeating a 3-message iteration requires a merge-or-dummy convention.
- *Does the verdict convention (P9-3) exclude a source protocol?* No. In every single-iteration protocol of
  ch. 4 the prover moves last. Any protocol whose verifier would send a final message different from its
  verdict becomes expressible by adding one dummy prover message (`rounds + 1`). The dummy appears in V\*'s
  view, but it is a constant. `outV_eq_getLast_of_moverIsV` is proved (it prints `propext` only).

**Q2. Efficiency (Def 116.b).**
- *Is `Efficient` ∧ `ReadsPrefix m` faithful to "time t(|x|) regardless of messages"?* Yes, at the level of
  functions. The next message is a function of the m(|x|)-bit prefixes, computable in time polynomial in
  |x| + |z| + rounds·m(|x|) once the interaction model has truncated the messages. Two differences remain,
  both benign:
  - z is not capped. Completeness and soundness quantify over all z (so z = `[]` is covered), and ZK bounds
    |z| by `Lz`.
  - The cap is per message rather than on the total.

  `Efficient` alone is not faithful: see the RE counterexample and the blow-up in #1.
- *Is `ReadsPrefix` required wherever the source needs it?* **No.** The honest V of Defs 116.1/117.a and the
  honest P of Def 119.5 lack it (#1). For V\* in Def 121.2, see #7.
- *The known consequence.* It is confirmed: an echoing honest prover and a doubling V\* produce a view of
  length at least 2^rounds. No ch. 2–4 ZK theorem depends on it (#7). My recommendation for Q-1 is to cap the
  honest prover, which is faithful to Def 119.5 and makes `ProverBounded` a lemma, and not to require a cap
  on V\*.

**Q3. Interactive proofs (Def 116.1).** Completeness and soundness are as in the source:
- Completeness is perfect: ∃ y ∀ z, Pr = 1 over both tapes.
- Soundness: ∃ negligible ε, then ∀ x ∉ L, ∀ `Strategy` P′ (an arbitrary next-message function, hence
  unbounded), ∀ z, with P′'s auxiliary input `[]` (the text's P\*(x)), and the literal strict
  `1 − ε(|x|) < Pr[out_V = [false]]`.
- Restricting provers to polynomial coin tapes loses nothing: every deterministic prover is a `Strategy`
  (coins `const 0`), and a randomized prover is dominated by its best fixed tape (averaging;
  `exists_proverCoins_le` is the `Strategy`-level form of that argument).
- `InteractiveProofErr` uses `1 − s ≤ Pr[[false]]`.
- A garbage verdict (neither `[true]` nor `[false]`) counts against both clauses, so it cannot buy soundness.

The one caveat is the verifier's efficiency (#1).

**Q4. Zero knowledge (Defs 121.1, 121.2, 122.a).**
- `HVZK` and `ZK` are faithful, with quantifier order ∀V\* ∃S ∀Lz ∀D ∃ε ∀x,y,z and D non-uniform at
  parameter |x|. The declared D8 deviations are a strict simulator, `∀ Lz` placed after S (necessary, #9),
  and encoded views.
- `StatZK` uses the sup-over-test-sets distance for all z.
- `PerfectZK` and `PerfectZKAbort` are faithful but cannot be attained by the source's perfect-ZK protocol
  (#2).
- *Is `PerfectZKAbort` an adequate stand-in?* Only in one direction. The abort form implies the source's
  expected-time perfect ZK (rerun until success; expected at most 2 runs). The converse is not known:
  truncating an expected-time simulator biases its conditional law. In this formalization it has no source
  instance and no bridge to `ZK` (#2). For GI, the adequate stand-in for "perfect ZK" is `StatZK δ` with
  negligible δ, which is `gi_statZK`.

**Q5. Commitments (Def 126.3, Thm 126.4, Alg 127.a).**
- Hiding is computational and at the source's strength: ∀ nuPPT D ∃ negligible ε ∀ n ∀ v₀, v₁ ∈ {0,1}ⁿ, with
  D at parameter n.
- Binding is perfect: distinct same-length values and randomness of the right length never collide. The
  source's missing `v₀ ≠ v₁` is fixed and declared.
- The OWP scheme is Blum's bitwise commitment `f(r) ‖ (b ⊕ h(r))` with ℓ(n) = n², stated correctly:
  - binding comes from injectivity of `f`;
  - one-bit hiding is the exact predictor reduction (advantage at most 2ε_h);
  - n-bit hiding is the hybrid argument (n·ε);
  - `owpComStr` is computable in polynomial time from evaluators of `f` and `h`.
- The hard-core predicate is a hypothesis. The text's form of the theorem is not stated (#13).

**Q6. NP and Levin reductions (Def 124.a, Def 191.11; `NP.lean`).**
- `WitnessRelation` is Def 191.11: the relation is bounded, and decidable in polynomial time on `⟨x, y⟩`
  (daylight in #11). `WitnessRelation.mem_NP` and `exists_witnessRelation_of_mem_NP` bridge to
  `Complexity.NP` in both directions, and both print clean.
- `LevinReduction` has exactly what form (A) needs:
  - `f` computable in polynomial time (both parties apply it);
  - `w` computable in polynomial time on the pair (the prover applies it);
  - `mem_iff` (used for soundness);
  - `witness` (used for completeness for every witness);
  - length regularity with `p ≥ id` (used for negligibility and to align coins and parameters; necessary,
    #14).
- The P11-1 hypothesis `hLR` supplies the ∃ y completeness clause. The ZK transfer correctly does without it.
- What form (A) concludes: see #1, #3 and #4.

## 3. Run-3a repairs in scope

| Repair | Status at `a3c5fa8` | Comment |
|---|---|---|
| P9-1 (IP contained RE) | **Holds for `IP`; incomplete in scope** | `Strategy.ReadsPrefix`, `.next_congr` and `.mono` (clean) are present. `IP` requires the verifier's cap, `npProtocol T p` truncates the message, and `npProtocol_readsPrefix`, `WitnessRelation.mem_IP` and `NP_subset_IP` print clean. I agree that the repaired `IP` coincides with the text's IP, up to a dummy final prover message (Q1). The same defect remains in the structures the theorems conclude (#1). This is a gap in the resolution's scope, not a re-report of P9-1. |
| P9-3 (verdict convention) | Holds | The deviation appears on `Protocol`, `outV` and in the module docstring. `outV_eq_getLast_of_moverIsV` is proved. |
| P11-1 (`hLR`) | Holds | `hLR` is present in `LevinReduction.efficientProverProofErr`, `.efficientProverProof`, `zk_proof_of_levinReduction` and `zk_proof_of_owp_levinReduction`. `zk_proof_of_mem_NP` passes `(hR.mem_iff x).1`. `LevinReduction.zk` rightly lacks it. |
| P11-2 (vacuous `∃ s`) | Holds as stated | The error is explicit, `p ≥ id` is exported, and `one_sub_inv_add_half_pow_lt_one` prints clean. A new observation, not a re-report: the separate `∃ π, EfficientProverProof` conjunct is uninformative (#3). |
| P9-2, P11-3 | Out of this pack's files | They live in `Encoding.lean` and the 3COL files. |

## 4. Adversarial instantiations

| # | Attempt | Outcome |
|---|---|---|
| I1 | **A verifier that is efficient but reads exponentially long messages** (pack example 1). The verifier checks a halting history sent by the prover. | It satisfies `InteractiveProof` and `EfficientProverProof` for HALT (#1). Only `IP` excludes it. The ZK-side variant (V\* doubles, P echoes) blows the view up to 2^rounds; a cap on the honest prover prevents it (#1, #7). |
| I2 | **A "proof" whose soundness holds only because the verdict is ill-defined** (pack example 2). | It fails. `outV` is always defined (`V.next` on the full history). Soundness needs the literal `[false]` and completeness the literal `[true]`, so a garbage verdict fails both. A prover that halts by sending `[]` still gets a defined verdict. The vacuous `s ≥ 1` was removed from the headlines by P11-2. The boundary case \|x\| = 0 with p(0) = 0 gives an error ≥ 1, which is harmless (#14). |
| I3 | **A simulator that is efficient only because the auxiliary input is bounded** (pack example 3). | It fails as stated: S is fixed before `Lz` and runs in time polynomial in its whole input, so the bound does not create its efficiency. The bound matters on the distinguisher's side. Without it, a D running in time polynomial in a view with \|z\| ≥ 2ⁿ breaks the 3COL commitments (#9). In `StatZK`, z is unbounded, which is harmless because a long z only helps S, and S must still handle short z. |
| I4 | **Perfect ZK for GI with an honest prover drawing bit coins.** | It fails: the view depends on the witness through the identity fallback of `samplePerm` (#2). |
| I5 | **A Levin reduction that shrinks instances** (f maps everything to a constant-size graph). | `le_eval` excludes it. Without that condition, ε′(\|f x\|) would not be negligible in \|x\|, and V\*' would have fewer coins than V\* (#14). |
| I6 | **Make the Thm 124.1 ∃-forms say less than they appear to.** | It succeeds: `npProtocol` witnesses the interactive-proof conjunct (#3). |
| I7 | **A degenerate protocol (0 messages).** | It is `PerfectZK`, `PerfectZKAbort` and `ZK` for every R. These are the only instances of the perfect notions (#2, #10). |

## 5. Inventory check

These are the rows of `inventory-ch4.md` whose location is one of this pack's files. "Faithful" means
faithful up to the deviations named.

| Id | Declaration(s) | Verdict |
|---|---|---|
| Def-114.a | `Strategy` | Faithful under D8: the next-message function doubles as the output function. |
| Def-114.b | `Protocol` | Faithful under D8. `rounds` counts messages. |
| Def-115.a | `exec`, `Protocol.execution` | Faithful. |
| Def-115.b | `View`, `viewV`, `viewP`, `execution` | Faithful. `viewV` exists only for the honest prover, which is all the ZK definitions need. |
| Def-115.c | `transcriptWith`, `transcript` | Faithful. |
| Def-115.d | `outV`, `outP`, `Strategy.out` | Faithful under D8 and the verdict convention. |
| Def-116.a | `ExecCoins`, `uprob_outV_eq_uexp`, `exists_proverCoins_le` | Faithful. |
| Def-116.b | `Strategy.Efficient`, `Strategy.ReadsPrefix` | Faithful only as a pair. `Efficient` alone is not (#1). |
| Def-116.1 | `InteractiveProof` | **Not faithful in "V is PPT"** (#1). Completeness and soundness are faithful (Q3). |
| Def-117.a | `InteractiveProofErr` | Same as Def-116.1. |
| Def-117.b | `IP` | Faithful (P9-1). |
| Claim-117.c | `npProtocol*`, `WitnessRelation.mem_IP`, `NP_subset_IP` | Faithful and proved (prints clean). |
| Def-119.5 | `EfficientProverProof(Err)` | **Not faithful in "P is PPT"** (#1). The "every y ∈ R_L(x)" clause is faithful. |
| Def-119.e | — | Absent; optional (#16). |
| Def-191.11 | `WitnessRelation`, `witnessLanguage`, `witnessSet`, `mem_NP`, `exists_witnessRelation_of_mem_NP` | Faithful, with the bounded-R daylight (#11). The text's typo is fixed and declared. |
| Def-121.1 | `HVZK` | Faithful under D8. |
| Def-121.2 | `ZK` | Faithful under D8. V\*'s class is larger than the text's (#7). |
| Def-122.a | `StatZK`, `PerfectZK`, `PerfectZKAbort` | Faithful definitions. The perfect forms cannot be attained here (#2). |
| Claim-122.b | — | Absent; optional (#16). |
| Def-124.a | `LevinReduction` | Faithful plus declared length regularity (#14). |
| Def-126.3 | `Commitment` | Faithful, with the declared source fix. |
| Claim-126.a | `Commitment.multiHiding`, `exists_pairRed_ge` | Faithful, and stronger than the text (values chosen after ε). No axiom print (#5). |
| Thm-126.4 | `owp_commitment`, `exists_commitment_of_owp_hardCore` | Faithful with the hard-core predicate explicit. The text's form is missing (#13). |
| Alg-127.a | `bitCom`, `owpCom`, `owpComAt`, `owpComStr`, `owpComLen` | Faithful. |
| Claim-127.b | `bitCom_inj`, `owpCom_inj`, `owpComAt_inj`, `owpComStr_binding` | Faithful and proved. |
| Claim-127.c | `exists_bitComPredictor`, `HardCore.bitHiding`, `BitHiding` | Faithful and proved, via the exact reduction of [Gar26, Thm 3.2] instead of [PS10, Lemma 73.8]; declared. |
| Claim-127.d | `BitHiding.owpComStr_hides` | Faithful and proved. |
| *(also in `NP.lean`)* Claim-124.d | `LevinReduction.efficientProverProof(Err)`, `LevinReduction.zk`, `pullback*` | Faithful: ZK and efficient-prover proofs transfer, with the soundness error composed with p. Not printed (#5). |
| *(also in `NP.lean`)* Thm-124.1 | the four `zk_proof_*` forms | Form (A) as planned, with the one-iteration ZK of DQ5. Wording and strength issues (#3, #4); rests on `sorryAx` (#5). |

## 6. Definitions: my restatement and the daylight

For each definition I wrote the restatement from the Lean before comparing it with the docstring.

| Declaration | Restatement | Daylight |
|---|---|---|
| `Strategy` | A function (x, z, r, received messages) ↦ next message, plus a polynomial c giving tape length c(\|x\|). | None. The output is the same function on the full history (declared). |
| `Strategy.coinLen`, `Coins` | c(n), and the type of c(n)-bit tapes. | None. |
| `encodeMsgs` | A list [m₁,…,m_k] encoded as ⟨m₁,⟨m₂,…⟨m_k,[]⟩⟩⟩. It is injective and nonempty when the list is nonempty. | None. |
| `ofNUPPT A` | The strategy whose next message is one activation of A at parameter \|x\| on ⟨⟨x,z⟩, encoded history⟩ with tape r. | None. |
| `Efficient S` | Some uniform machine with the same coin polynomial computes S's next-message function on all inputs. | None against the docstring. Against the source: time is polynomial in the total input (declared; #1). |
| `ReadsPrefix S m` | S's next message is unchanged when every received message is truncated to m(\|x\|) bits. | The docstring says "together with `Efficient` this is the text's PPT machine". That holds except that reading of z is uncapped, which is benign (Q2). |
| `moverIsV` | Who moves at step k: if V moves first, V moves at even k; otherwise at odd k. | None. |
| `exec` | Pairs (messages received by P, messages received by V) after k strictly alternating moves. Each mover applies its strategy to what it has received so far. | None. |
| `View`, `View.encode` | (x, z, r, received), encoded as ⟨⟨x,z⟩,⟨r, msgs⟩⟩. The encoding is never `[]`. | None. |
| `Strategy.out` | The next-message function applied to a full view. | None. |
| `Protocol` | (P, V, a polynomial number of messages, first mover). | None. The cost of the verdict convention is stated. |
| `ExecCoins`, `withV` | The tapes of P′ and V at parameter \|x\|; the protocol with V replaced. | None. |
| `transcriptWith`, `transcript`, `outV`, `outP`, `viewV`, `viewP`, `execution` | The execution run for rounds(\|x\|) moves. outV is V's next message on its full history. The views are the four components. | None. |
| `InteractiveProof π L` | V is `Efficient`. ∀x∈L ∃y ∀z, the honest execution ends in V outputting `[true]` on every tape pair. ∃ negligible ε such that ∀x∉L ∀ strategy P′ ∀z, Pr[V outputs `[false]`] > 1−ε(\|x\|), with P′'s auxiliary input `[]`. | The docstring is accurate and states the cost. Against the source: "V is PPT" is not captured (#1). |
| `InteractiveProofErr π L s` | The same, with soundness Pr[`[false]`] ≥ 1 − s(\|x\|). | As above. |
| `IP` | Languages with some proof π whose V reads only a polynomial prefix of each message. | None. |
| `WitnessRelation L R` | L = {x : ∃y R x y}; every y with R x y is polynomially bounded in \|x\|; R is decided on ⟨x,y⟩ by a polynomial-time test T. | R itself is bounded (#11). |
| `witnessLanguage`, `witnessSet` | {x : ∃y R x y} and {y : R x y}. | None. |
| `EfficientProverProof π L R` | An `InteractiveProof` with an `Efficient` honest P, accepting with probability 1 for every y with R x y and every z. | The docstring says "P is a PPT strategy"; it is only `Efficient` (#1). |
| `EfficientProverProofErr` | The same, with soundness error s. | As above. |
| `npProtocol T p` | One message, prover first, no coins. P sends its auxiliary input; V outputs `[T ⟨x, m.take p(\|x\|)⟩]`. | None. |
| `NUPPT.simulate S x z r` | One activation of S at parameter \|x\| on ⟨x,z⟩. | None. |
| `HVZK π R` | ∃ uniform S ∀ polynomial Lz ∀ nuPPT D ∃ negligible ε ∀x,y,z with R x y and \|z\| ≤ Lz(\|x\|): D's advantage at parameter \|x\| between the encoded honest-verifier view and S(x,z) is ≤ ε(\|x\|). | None. The proof property is not assumed (declared). |
| `ZK π R` | As `HVZK`, but ∀ `Efficient` V′ ∃ S, with V′'s view. | Against the source: V′'s class is larger (#7). Otherwise only the declared D8 deviations. |
| `StatZK π R δ` | ∀ `Efficient` V′ ∃ uniform S ∀x,y,z with R x y: every test set has probability gap ≤ δ(\|x\|) between the view and S(x,z). | None. |
| `PerfectZK` | `StatZK` with δ = 0. | Its cost is not stated (#2). |
| `PerfectZKAbort` | ∀ `Efficient` V′ ∃ uniform S ∀x,y,z with R x y: Pr[S = `[]`] ≤ 1/2, and conditioned on S ≠ `[]` the law of S equals the law of the view. | Its cost and the missing bridge to `ZK` are not stated (#2). |
| `Commitment Com ℓ` | `Com` is polynomial-time. Binding: ∀n, distinct n-bit v₀, v₁ and ℓ(n)-bit r₀, r₁ give different commitments. Hiding: ∀ nuPPT D ∃ negligible ε ∀n ∀v₀,v₁ ∈ {0,1}ⁿ, D's advantage at parameter n between Com(v₀,·) and Com(v₁,·) is ≤ ε(n). | None. The source fix `v₀ ≠ v₁` is declared. |
| `pairTuple`, `pairHybrid`, `pairRed` | The coordinatewise product of samplers; the k-th hybrid (coordinates below k from Y, the rest from X); the reduction that plants the challenge at coordinate k. | None. |
| `multiCom` | The `encodeMsgs` of the list (Com(v_i, r_i))_i. | None. |
| `bitCom`, `owpCom`, `owpComAt`, `owpComStr`, `owpComLen` | f(r) ‖ (b ⊕ h(r)); bitwise for n bits with n independent n-bit r_i; read from strings at n = \|v\| with r padded to n²; ℓ(n) = n². | None. |
| `BitHiding P h` | ∀ nuPPT D ∃ negligible ε ∀n, D's advantage between Com(0,·) and Com(1,·) is ≤ ε(n). | None. |
| `LevinReduction` | f and w are polynomial-time; x∈L ↔ f x∈L′; R x y → R′(f x)(w x y); \|f x\| = p(\|x\|) with p ≥ id. | Length regularity is a declared extra condition (#14). |
| `Strategy.pullback`, `Protocol.pullback` | Run S on (f x, g x z) with coins `S.coins.subst p`; P gets (f x, w x y), V gets (f x, z), and there are `rounds.subst p` messages. | None. |
| `LevinNPHard L′ R′` | Every (L, R) with a `WitnessRelation` has a length-regular Levin reduction to (L′, R′). | None; it is an unproved hypothesis (#14). |

## 7. Theorems: does each statement say what its docstring claims?

- **`Interaction.lean`**
  - `encodeMsgs_nil/cons`, `pairFstD_encodeMsgs`, `ofNUPPT_next`, `moverIsV_true/false`, `exec_zero/succ`,
    `withV_*`, `outV_eq_out`, `outP_eq_out`, `transcript_eq` and `outV_withV` are unfolding equations and
    match their docstrings. `outV_withV`'s "depends on P′ only through the transcript" is a paraphrase of
    the equation.
  - `ofNUPPT_efficient` (non-vacuity) and `Efficient.exists_uniform`: as claimed.
  - `ReadsPrefix.next_congr` and `.mono`: as claimed. `.mono` needs the pointwise inequality m ≤ m′.
  - `exec_length`: exactly k messages after k moves, as claimed.
  - `outV_eq_getLast_of_moverIsV`: if the verifier makes the last of the k+1 moves, the last message P′
    received is `outV`. As claimed.
  - `uprob_outV_eq_uexp` (Fubini over the two tapes) and `exists_proverCoins_le` (for each event, some fixed
    prover tape does at least as well as the average): as claimed. The latter is the `Strategy`-level form of
    the "deterministic P\* without loss of generality" argument (Q3).
- **`InteractiveProofs.lean`**
  - `InteractiveProofErr.interactiveProof` (negligible s gives a proof with ε = s + 2⁻ⁿ), `.exists_err` and
    `exists_uprob_accept_lt`: as claimed.
  - `mem_witnessLanguage`, `mem_witnessSet` and `eq_witnessLanguage`: as claimed.
  - `WitnessRelation.mem_NP` and `exists_witnessRelation_of_mem_NP`: the two directions of the bridge to
    `Complexity.NP`. As claimed; both print clean.
  - `EfficientProverProofErr.efficientProverProof` and `EfficientProverProof.exists_err`: as claimed.
  - `npProtocol_outV`, `_readsPrefix`, `_efficientV`, `_efficientP` and `_interactiveProof`: as claimed.
    `_interactiveProof` gives soundness with probability 1 and ε = 2⁻ⁿ, because the clause is strict.
  - `WitnessRelation.mem_IP` and `NP_subset_IP`: as claimed, and clean.
- **`Defs.lean`**
  - `simulate_eq`: unfolding.
  - `StatZK.zk` (same S, ε := δ), `StatZK.hvzk`, `ZK.hvzk` (instantiate V′ := V; both need V `Efficient`),
    `StatZK.mono`, `PerfectZK.statZK` and `PerfectZK.zk`: as claimed.
  - `negligible_const_zero`: as claimed.
  - `negligible_inv_pow_sqrt_div` (a > 1, C > 0 imply a^{−√(N/C)} is negligible),
    `negligible_two_pow_neg_sqrt_div`, `negligible_exp_neg_sqrt_div`, `negligible_of_le_inv_pow_sqrt_div`
    and `inv_pow_le_inv_pow_sqrt_div`: as claimed (Inf-4.4).
  - Missing: `PerfectZKAbort.statZK` / `.zk` (#2).
- **`Commitment.lean`**
  - `binding_ofFn`: typed binding, as claimed.
  - `acceptProb_pairHybrid_zero/self` (they need the `Nonempty` instances), `acceptProb_pairRed_left/right`
    and `exists_pairRed_ge` (some coordinate has advantage ≥ ε/t when t ≥ 1): as claimed.
  - `Commitment.multiHiding`: Claim-126.a with values chosen after ε, a strong form. As claimed.
  - `bitCom_castSucc/last/false/true`, `bitCom_false_eq_owpGenPRG` (Com(0,·) is the generator of Thm 79.4),
    `bitCom_inj`, `owpCom_eq_pairTuple`, `owpCom_inj`, `owpComLen_eval`, `owpComStr_pairEncode`,
    `owpComAt_ofFn` and `owpComStr_ofFn`: as claimed.
  - `owpComAt_inj` needs no hypothesis on the randomness lengths, so it is stronger than binding requires.
    `owpComStr_binding`: as claimed.
  - `exists_bitComPredictor`: the prediction probability is exactly 1/2 + advantage/2, for some sign. As
    claimed; only bijectivity of `f` is used.
  - `HardCore.bitHiding`: ε := 2ε_h, as claimed.
  - `BitHiding.owpComStr_hides`: ε := n·ε_B, as claimed.
  - `owpComStr_polyTimeComputable`, `owp_commitment` and `exists_commitment_of_owp_hardCore`: as claimed,
    with the deviation declared (#13).
- **`NP.lean`**
  - `LevinReduction.polyTimeReducible`, `.refl` and `.trans` (with `p'.subst p`): as claimed.
  - `coinLen_pullback`, `pullback_outV` and `pullback_efficient`: as claimed.
  - `Negligible.comp_of_le` (ε composed with φ ≥ id is negligible): as claimed. This is a general lemma that
    policy §1 would place in `Foundations/Negligible.lean`.
  - `LevinReduction.efficientProverProofErr` (soundness error s ∘ p), `.efficientProverProof` and `.zk`:
    these are Claim-124.d, and they say what their docstrings claim. The ZK transfer needs no `hLR`.
  - `zk_proof_of_levinReduction`: the conjunction is as described in the body of its docstring; the bold
    title overclaims (#3).
  - `zk_proof_of_owp_levinReduction`, `zk_proof_of_mem_NP` and `zk_proof_of_mem_NP_of_owp`: the bodies are
    accurate, but the first conjunct is uninformative (#3) and R is existential (#4).
  - `one_sub_inv_add_half_pow_lt_one`: as claimed.

## 8. Attestation check

| Attestation | Check | Result |
|---|---|---|
| Elaboration (`replay.log`) | I tallied the 358 lines. | 358 modules, every rc=0, 0 errors, 25 `sorry` warnings (as attested). All 25 are outside the five files; their sources are listed in #5. |
| Axioms (`axioms.log`) | I counted the prints. | 26 prints: 22 standard axioms only, 4 with `sorryAx` (the Thm 124.1 forms), as attested. `outV_eq_getLast_of_moverIsV` uses `propext` only and `npProtocol_readsPrefix` uses `propext, Quot.sound`. Coverage and sources are gaps (#5). |
| Admissions (`admissions.txt`) | Compared with the replay. | 0 in the five files, consistent with `sorry=0` for all five modules in the replay. |
| Lint (`lint.log`) | Read. | "0 findings in 5 files". The `@[simp]` approvals (#17) are a policy matter the lint does not check. |
| Interface (ch. 5–8 cites `Strategy`, `View`, `Protocol`, `InteractiveProof`, `ZK`, `PerfectZK`, `PerfectZKAbort`, `Commitment`) | Fitness for use. | `InteractiveProof`: #1. `ZK`: #7, #9. `PerfectZK` and `PerfectZKAbort`: #2. `Protocol`: #8, #15. `Commitment`: #12, #15(b). `Strategy` and `View` have no finding. |

*Closing condition:* the pack closes at 0 blockers and 0 majors. #1 closes when the caps land, or when the
user explicitly acknowledges D8's cost together with the Q-1 ruling. #2 closes when the docstrings are
amended and either the bridge is proved or `PerfectZKAbort` leaves the ch. 5–8 interface.
