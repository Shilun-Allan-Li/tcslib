## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/03e-pack-r2.md =====

# Gate 03e ([PS10] ch. 2–4, interaction, proof systems, ZK definitions, commitments, NP layer), round 2: external closing audit pack

**What is audited:** the repairs of round 1, on `cryptography/pass-shelat-ch2-4` at
`e79397eaf68b156b9db091f464741f6eb75b9c28` (the branch after #201 merged; its Lean files are #201's head `0c348ff9`).
- **Round 1** audited `a3c5fa8b72e50939822f22364647dc844a3914a0` and found **0 blockers, 2 majors (#1, #2), 4 minors and 11 notes**; no severity change in the review (`gate03e-findings.md`, in the bundle,
  verbatim).
- **The repair:** the 03e repair commit (G3-3: bounded honest messages; G3-4: the perfect forms' cost and `PerfectZKAbort.statZK`; minors and notes), merged in #199; the DESIGN records it missed (§5 items 8 and 11, §7 item 51) were committed after #201 merged. The full delta is `evidence-r2/03e/repair.diff.txt`; each round 1
  row's resolution is in `resolutions-03e-r1.md` (both in the bundle). The maintainer's review of
  round 1 is `review/gate03e-review.md` (in the bundle).
- **The deliverable:** **`gate03e-r2-findings.md`**.

The bundle holds this pack, then every file named below under a `## ===== <path> =====` header.
**The source is attached separately:** [PS10], 3rd ed., January 2010 (PDF; book page = PDF page −
12).

## Errata to the round 1 pack (review of round 1)

- **Scope line** (M7): pack 03g is 3-colouring and 03k graph isomorphism (round 1's line 39 had
  them swapped).
- **Inventory** (#16): Thm-124.1 and Claim-124.d are owned by pack 03g (its inventory list); this
  pack audits `NP.lean`'s forms of them as well ("also 03g").
- **Q-1** stands as ruled (no cap on `V*`; finding 7).

## Brief for the auditor

Round 2 does two things.
1. **It verifies the round 1 resolutions.** For each row of `resolutions-03e-r1.md` (the
   findings and the review's missed items `M1`, …) say whether the resolution is adequate:
   - **fixed**: the defect is gone, and the fix introduces no new one;
   - **recorded** or **scheduled**: accepted as declared, or deferred to a named PR or gate, and
     the record is accurate;
   - **not resolved**: say why.
2. **It audits the changed surface afresh** (section A of `evidence-r2/03e/repair.diff.txt`):
   - restate every new public declaration listed below in your own words, and say whether its
     statement is what its docstring claims;
   - check every changed statement and docstring;
   - look for regressions: anything round 1 accepted that the repair broke.

Pack 03a's brief and severity guide apply (03a's pack is in the bundle). Attempt at least
**three adversarial instantiations** against the changed surface. Do not give a blanket
approval.

## What changed

- **Statements:** `InteractiveProof(Err)`'s completeness carries a message bound `B` (`ProverBounded`), and `EfficientProverProof(Err)` has the new field `boundedP`. `zk_proof_of_mem_NP` and `_of_owp` become corollaries of the witness-relation forms; the `_owp_` Levin-reduction forms tie the commitment and the protocol together (`∃ Com ℓ, Commitment Com ℓ ∧ …`).
- **New public declarations:**
- `Protocol.ProverBounded` (def), `ProverBounded.mono`, `ProverBounded.pullback`,
  `ProverBounded.exists_complete`, `npProtocol_proverBounded`;
- `InteractiveProof.exists_accept`, `InteractiveProofErr.exists_accept` (the old completeness, for
  consumers);
- `PerfectZKAbort.statZK` (error `2^{-|x|}`), `PerfectZKAbort.zk`, `perfectZK_zeroRounds`, and the
  retry construction `AbortRetry.attempt`, `retry`, `attempt_poly`, `retry_poly`,
  `statClose_retry`, `exists_retrySimulator`, `firstHit_map_getD_eq`, `uprob_not_ne_nil_le`;
- `exists_commitment_of_owp` (`Commitment.lean`);
- `zk_proof_of_witnessRelation`, `zk_proof_of_witnessRelation_of_owp`,
  `exists_commitment_zk_proof_of_owp_levinReduction` (`NP.lean`).
- Consumers re-proved by the repair (graph isomorphism, 3-colouring) are in packs 03k and 03g; they are context here (section B of the diff).

## Scope

| Item | Where |
|---|---|
| Round 1 findings, review, resolutions, repair diff | `findings/gate03e-findings.md`, `review/gate03e-review.md`, `resolutions-03e-r1.md`, `evidence-r2/03e/repair.diff.txt` |
| Under audit (the changed surface), at the pin | `TCSlib/Cryptography/ZeroKnowledge/{Interaction, InteractiveProofs, Defs, Commitment, NP}.lean` |
| Context | `03e-pack.md` (round 1), `03a-pack.md` (common brief), `policy.md`, `briefs/pass-shelat/DESIGN.md`, the duplication ledger (scheduled rows) |
| Out of scope | tactic proofs; the scheduled clean-up (G3-5, DL-9 onward) beyond checking that its record is accurate |

## Attestations (maintainer execution claims; evidence under `evidence/e2/` in the bundle)

### Attestation results at `e79397eaf68b156b9db091f464741f6eb75b9c28` (evidence under `evidence/e2/`)

1. **Elaboration** (`replay.log`): the closure of this pack's files, 126 modules, each
   checked alone into a fresh olean tree by `scripts/lean_check_tree.sh`: all pass, 0 errors;
   21 `sorry` warnings in the closure.
2. **Axioms** (`axioms.log`): 116 prints of every public theorem and lemma in this pack's files:
   109 use only the standard axioms, and 7 depend on `sorryAx`; any other axiom is listed
   in the log.
3. **Admissions** (`admissions.txt`): 0 declarations in this pack's files contain `sorry`.
4. **Lint** (`lint.log`): `scripts/style_lint.py` on this pack's files: 0 findings in 5 files.

The replay is the 416-module replay at `af91d53a` overlaid with the re-check of the 98 modules
downstream of #201's changes (`evidence-repairs/03ac/replay.log`); each line of `replay.log` is the
newest check of its module, and the Lean files at the pin equal #201's head.

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Plus one line per round 1 row: `<row>: fixed / recorded / scheduled / not resolved — <reason>`.

Severity guide: **blocker** (a downstream phase would build on a wrong statement); **major**
(fixable but materially misleading, or debt that needs explicit acknowledgment); **minor** (an edge
case, naming or attribution); **note** (no change required). The gate closes at **0 blockers and 0
majors**.

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/findings/gate03e-findings.md =====

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

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/review/gate03e-review.md =====

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

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/resolutions-03e-r1.md =====

# Gate 03e (interaction, proof systems, ZK definitions, commitments, NP layer): round 1 resolutions

- **Round 1:** findings `findings/gate03e-findings.md`, verbatim, SHA-256
  `8af18f12965eb01b594de42d60e567b4ad5cb2810652a94f70f7daf0aef0a7e3`; head
  `a3c5fa8b72e50939822f22364647dc844a3914a0`. Counts: **0 blockers, 2 majors (#1, #2), 4 minors,
  11 notes.**
- **Review:** `review/gate03e-review.md`: no finding false; by its tables 15 true (#6 (c) left
  unverified) and 2 partly true (#5, #16). No severity change (2 majors, 4 minors, 11 notes).
  Corrections to the auditor's proposed fixes for #1, #5 (c), #12, #13 and the pack labels. Ten
  items missed by the auditor (M1–M10 below).
- **Rulings (user, 2026-11-05;** `QUEUE.md:116–129`; decision log rows "Gate 03 rulings G3-1 to
  G3-4" and "G3-5 to G3-8"**):** G3-3 (A) = R-03e-1 option 1, `Efficient` plus bounded honest
  messages in the definitions (#1); G3-4 (A) = R-03e-2 option 1, keep the perfect forms, state the
  cost, prove `PerfectZKAbort.statZK` (#2); G3-6 (A) = R-03e-3, approve the 15 `@[simp]` (#17);
  G3-7 (d) = R-03e-4, `InteractiveProofErr.seqRep` in prong C (#3); G3-5 (A) for the copy
  `negligible_const_zero` (DL-13). Q-1 (no cap on `V*`) stands (#7).
- **Repair:** worker commit `30f90d36ab23d8f6b9ac99e4608c38174f3bfcb1` (on `a3c5fa8b…`), merged
  with #198's head as `b925421ece04d3189f5fc8c6ed4c6884e5caae49` = PR #199's head, merged into
  `cryptography/pass-shelat-ch2-4` by `af91d53a414cdad6bbb61cecdc13f5e0e956d0b1`. Evidence
  `evidence-repairs/03e/` (31 downstream modules on the stacked state; `Checks` 328 prints, 57
  `sorryAx`); the prints below are also in `evidence-repairs/03ac/checks-axioms.log` at #201's head
  (`0c348ff94cacf24d96d99078c9dd9e328530c8d2`, which contains #199). Line numbers are at #201's head;
  Lean paths are under `TCSlib/Cryptography/ZeroKnowledge/`.
- **Outside ch. 2–4:** G3-7 (d) is prong C commit `9e6f08bb28b2fcebfa845d47a9fd6e1ed281f951`; prong
  C's re-sync to G3-3 and G3-4 is in gate 06's integration to-do
  (`gates/06-ch5-8-statements/PLAN.md:55–57`).

| Finding | Severity (after review) | Resolution |
|---|---|---|
| 1 | major | **Fixed** (G3-3). `Protocol.ProverBounded` is in `Interaction.lean:331–337`; `InteractiveProof(Err).complete` bounds the honest messages (`InteractiveProofs.lean:126–128, 149–151`), `EfficientProverProof(Err)` has `boundedP` (:346, :361), with bound lemmas (`InteractiveProofs.lean:466`, `NP.lean:273`, `GraphIsomorphism.lean:926, 930, 935`, `ThreeColoring/Protocol.lean:562, 580, 605`), the "PPT" docstrings replaced, statements re-proved unchanged, prints standard. **Fixed (records, after #201 merged):** DESIGN §5 item 8 (`briefs/pass-shelat/DESIGN.md:1009–1014`) now states the bounded-message convention; the 03e repair had not amended (review §1.1); prong C's local `ProverBounded` is **Scheduled** for gate 06 integration. |
| 2 | major | **Fixed** in ch. 2–4 (G3-4); prong C scheduled. The cost is stated on `PerfectZK` and `PerfectZKAbort` (`Defs.lean:173–180, 189–196`) and in the module docstring (:50–57); `PerfectZKAbort.statZK` (error `2^{-\|x\|}`), `.zk` and `perfectZK_zeroRounds` are proved (:535, :596, :269), and `GraphIsomorphismZK.lean:43–48` cross-references. **Fixed (records, after #201 merged):** DESIGN §5 item 11 (`DESIGN.md:1019–1023`) no longer says "`PerfectZKAbort` stated as the perfect form": no source protocol attains the perfect forms; GI is `StatZK`. **Fixed (records):** the Thm-175.1 row of `inventory-ch5-8.md`. **Scheduled:** prong C's `SequentialZK.lean` (:41–45, `PerfectZKAbort.seqRep` through `statZK`) at gate 06 integration; the `inventory-ch5-8.md:130` row is not named there. |
| 3 | minor | **Fixed.** Titles retitled to "a zero-knowledge protocol with soundness error …" (`NP.lean:563–581, 595–607`); tied forms `exists_commitment_zk_proof_of_owp_levinReduction`, `zk_proof_of_witnessRelation(_of_owp)` (:625–634, :679, :698); the text's Thm 124.1 recorded as debt for ch. 7 (:575–576). The debt's discharge (G3-7 (d)): `InteractiveProofErr.seqRep` is in prong C (`9e6f08bb…`); the 3-colouring corollary is **Scheduled** for gate 06 integration (decision log, G3-7d row). |
| 4 | minor | **Fixed.** `zk_proof_of_witnessRelation` holds for every witness relation (`NP.lean:679`); `zk_proof_of_mem_NP` (:729) is its corollary, statement unchanged. |
| 5 | minor (partly true) | **Fixed.** (a) The `sorryAx` prints are annotated with the stubs they reach, `colRep_efficientProverProof` and `col_zk` (`audits/pass-shelat/Checks.lean:321–324`); (b) the five prints (:418–423), standard at #201's head. **Fixed (records):** (c)'s record fixes, an erratum on `audits/pass-shelat/run3-audit-summary.md:17` (it meant `Complexity/Randomized/Build/*`; of the 22 non-ZK `sorry` warnings in 03e's closure, 21 are `main`'s and one is `NonUniform`'s optional admission). The drafter found them missing: `audits/pass-shelat/run3-audit-summary.md:17` still names `TuringMachine/Build/*` (it means `Complexity/Randomized/Build/*`), and no attestation says the 22 core-module sorries are `main`'s (MIG-1 stage S), as the review found. |
| 6 | minor | **Fixed** in ch. 2–4; prong C scheduled. (a) `[Gol01]` in `Defs.lean:68, 102, 184` and `GraphIsomorphismZK.lean:87, 289`; (b) the p. 116 misquotes paraphrased (`Interaction.lean:46–48, 160–162`); (c) `[AB09, §2.3]` (`NP.lean:114–115`). **Scheduled:** the tag in prong C's `Composability/SequentialZK.lean:85`, now in gate 06's integration to-do (`gates/06-ch5-8-statements/PLAN.md`). |
| 7 | note | **Fixed.** `ZK`'s deviation records Q-1 (no cap on `V*`) and why the view is still bounded (`Defs.lean:146–152`). |
| 8 | note | **Fixed.** The dummy-move repetition convention, with its users, in `Interaction.lean:39–43`. |
| 9 | note | **Fixed.** The necessity argument for `Lz` and for advice indexed by `\|x\|` is in `Defs.lean:42–47`. **Fixed (records, after #201 merged):** the source issue is DESIGN §7 item 51, beside item 50. |
| 10 | note | **Fixed.** `perfectZK_zeroRounds` (`Defs.lean:269`); `gi_statZK` named as the substantive instance in the module docstring (:53–56). |
| 11 | note | **Fixed.** `WitnessRelation`'s docstring states the daylight with Def 191.11 (`InteractiveProofs.lean:239–249`). |
| 12 | note | **No change** needed (already met: `colVerify` checks the lengths); the optional sentence is added to `Commitment` (`Commitment.lean:107–110`). |
| 13 | note | **Fixed.** `exists_commitment_of_owp`, the text's Thm 126.4 (`Commitment.lean:905–911`); its print is standard. |
| 14 | note | **Fixed.** The padding remark now says "assumed" (`NP.lean:35, 131`); the pointer belongs to 03g. |
| 15 | note | **Fixed (records).** Both limits (Barak–Lindell on black-box strict-PPT simulation; everything indexed by `\|x\|`) are recorded in `SPINE-DESIGN.md` §S1, "Two limits of the interaction model D8 for ch. 5–8". |
| 16 | note (partly true) | **Fixed in the closing-round pack** (pack text): Thm-124.1 and Claim-124.d are owned by 03g and listed in 03e's pack as "(also 03g)". |
| 17 | note | **Recorded** (G3-6, `QUEUE.md:125`): the 15 are approved and unchanged: `encodeMsgs_nil/cons`, `moverIsV_true/false`, `exec_zero`, `withV_V/P/rounds/verifierFirst/self` (`Interaction.lean`), `mem_witnessLanguage`, `mem_witnessSet` (`InteractiveProofs.lean`), `bitCom_castSucc/last`, `owpComLen_eval` (`Commitment.lean`). |
| M1 | (review) a prefix cap does not give `ProverBounded` | **No change:** informed G3-3's option 1, which bounds the honest messages directly. |
| M2 | (review) the 3-colouring parties are not prefix-reading | **No change:** option 1 needs no redefinition; `colProtocol_proverBounded` (`ThreeColoring/Protocol.lean:605`) comes from `Com`'s polynomial time. |
| M3 | (review) the bound must sit in the completeness clause | **Fixed** (`InteractiveProofs.lean:126–128, 149–151`). |
| M4 | (review) the perfect-ZK obstruction is inherent | **Fixed:** both arguments (`n! ∤ 2^c`; dyadic simulator laws) are in `Defs.lean:173–180, 189–196` and `GraphIsomorphismZK.lean:43–48`. |
| M5 | (review) misleading text in DESIGN §5 item 11 and `SequentialZK.lean` | **Fixed** for DESIGN (§5 item 11, records); **Scheduled** for `SequentialZK.lean:41–45, 397–399` at gate 06 integration (`PLAN.md`). See #2. |
| M6 | (review) no soundness amplification for `seqRep` | **Fixed** in prong C (G3-7 (d), `9e6f08bb…`: `InteractiveProofErr.seqRep`, `EfficientProverProofErr.seqRep`); the 3-colouring corollary is **Scheduled** (gate 06 integration). |
| M7 | (review) pack labels; 03e's scope line | **Fixed in the closing-round pack:** 03g is 3-colouring and 03k graph isomorphism (`03e-pack.md:39` had them swapped). 03g's re-staged pack (`b13af7af`) points at the rulings. |
| M8 | (review) #12 met, #13's premise outdated, #5 (c) reconciled | **No change**, except #5 (c)'s record correction, which is not done (see #5). |
| M9 | (review) "PPT strategy" field docstrings; second misquote | **Fixed:** no "PPT strategy" remains in `InteractiveProofs.lean`; `Interaction.lean:46–48` paraphrases. |
| M10 | (review) removing the 15 `@[simp]` breaks proofs | **No change** (G3-6 approves them). |

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence-r2/03e/repair.diff.txt =====

# Gate 03e, round 2: the repair diff
#
# Section A: every change to this pack's Lean files between the round 1 head a3c5fa8b72e50939822f22364647dc844a3914a0 and the round 2 pin e79397eaf68b156b9db091f464741f6eb75b9c28, whichever repair made it.
# Section B: the rest of the 03e repair commit 30f90d36ab23d8f6b9ac99e4608c38174f3bfcb1 (on a3c5fa8b72e50939822f22364647dc844a3914a0; in #199): its changes outside this pack's files (consumers, Checks.lean, records).

### --- A: this pack's files, a3c5fa8b72e50939822f22364647dc844a3914a0..e79397eaf68b156b9db091f464741f6eb75b9c28 ---
diff --git a/TCSlib/Cryptography/ZeroKnowledge/Commitment.lean b/TCSlib/Cryptography/ZeroKnowledge/Commitment.lean
index 0e00e38e..f9b9bc52 100644
--- a/TCSlib/Cryptography/ZeroKnowledge/Commitment.lean
+++ b/TCSlib/Cryptography/ZeroKnowledge/Commitment.lean
@@ -8,6 +8,7 @@ import TCSlib.Cryptography.ZeroKnowledge.CommitmentLemmas
 import TCSlib.Cryptography.ZeroKnowledge.Interaction
 import TCSlib.Cryptography.Pseudorandom.Indistinguishability
 import TCSlib.Cryptography.Pseudorandom.GeneratorFromPermutation
+import TCSlib.Cryptography.Asymptotic.HardCorePermutation
 
 set_option maxHeartbeats 0
 set_option relaxedAutoImplicit false
@@ -71,15 +72,16 @@ argument, colours padded to `n` bits (DQ4). In the string form `Com ⟨v, r⟩`
   `BitHiding.owpComStr_hides` — the bitwise hybrid (Claim-127.d).
 * `TCSlib.Cryptography.owp_commitment` — **[PS10, Theorem 126.4]**: a one-way permutation
   with a hard-core predicate gives a commitment scheme; `exists_commitment_of_owp_hardCore` —
-  the existential headline; `bitCom_false_eq_owpGenPRG` — `Com(0, ·)` is the generator of
-  [PS10, Theorem 79.4]; `owpComStr_polyTimeComputable` — its `Com` is polynomial-time
-  (the bitwise loop `CommitmentLemmas.ComLoop`).
+  the existential headline; `exists_commitment_of_owp` — the text's form, from a one-way
+  permutation alone (Goldreich–Levin, `exists_owp_hardCore`); `bitCom_false_eq_owpGenPRG` —
+  `Com(0, ·)` is the generator of [PS10, Theorem 79.4]; `owpComStr_polyTimeComputable` — its
+  `Com` is polynomial-time (the bitwise loop `CommitmentLemmas.ComLoop`).
 
 ## References
 
 * [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
   (§4.7.1: Definition 126.3, Theorem 126.4; §3.3.3–3.3.4: Definition 78.3, Theorem 79.4;
-  §3.5.2: Theorem 104.4.)
+  §3.5.2: Theorem 104.4; Theorem 87.3, Goldreich–Levin.)
 * [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
   draft of 22 January 2026, §3.3.2 (Construction 3.2, Theorem 3.2) and Lemma 3.3 (the
   multicopy hybrid argument).
@@ -102,7 +104,10 @@ parameter `n`) distinguishes `{r ← {0,1}^{ℓ(n)} : Com(v₀, r)}` from
 **Deviation:** `Commitment`: binding clause with `v₀ ≠ v₁` (source error); `n` an explicit
 argument, colours padded to `n` bits (DQ4). As printed, binding is unsatisfiable (`v₀ = v₁`,
 `r₀ = r₁`); the string form's parameter is `n = |v|`, typed users supply `n` explicitly; the
-distinguisher's verdict is the string `[true]` (`NUPPT.distinguisherL`, Deviation 4). -/
+distinguisher's verdict is the string `[true]` (`NUPPT.distinguisherL`, Deviation 4). Binding
+constrains only values of the same length `n` with randomness of length exactly `ℓ(n)`, as in
+the text, so a protocol that opens a general `Commitment` must check those lengths, as the
+3-colouring verifier `colVerify` does (gate 03e, note 12). -/
 structure Commitment (Com : List Bool → List Bool) (ℓ : PolyExpr) : Prop where
   /-- `Com` is computable in deterministic polynomial time. -/
   easy : PolyTimeComputable Com
@@ -897,4 +902,12 @@ theorem exists_commitment_of_owp_hardCore
   obtain ⟨P, h, hP, hh⟩ := hex
   exact ⟨owpComStr P h, owpComLen, owp_commitment P h hP hh⟩
 
+/-- **[PS10, Theorem 126.4], the text's form: if one-way permutations exist, then commitment
+schemes exist** (gate 03e, note 13): the hard-core predicate of Goldreich–Levin for a padded
+one-way permutation (`exists_owp_hardCore`, [PS10, Theorem 87.3]) plugged into
+`exists_commitment_of_owp_hardCore`. -/
+theorem exists_commitment_of_owp (h : ∃ P : PermFamily, OneWayPermutation P) :
+    ∃ (Com : List Bool → List Bool) (ℓ : PolyExpr), Commitment Com ℓ :=
+  exists_commitment_of_owp_hardCore (exists_owp_hardCore h)
+
 end TCSlib.Cryptography
diff --git a/TCSlib/Cryptography/ZeroKnowledge/Defs.lean b/TCSlib/Cryptography/ZeroKnowledge/Defs.lean
index 39e32c86..f6c4bc5f 100644
--- a/TCSlib/Cryptography/ZeroKnowledge/Defs.lean
+++ b/TCSlib/Cryptography/ZeroKnowledge/Defs.lean
@@ -7,6 +7,8 @@ import TCSlib.Cryptography.ZeroKnowledge.Interaction
 import TCSlib.Cryptography.Asymptotic.Adversary
 import TCSlib.Cryptography.Asymptotic.Sampling
 import TCSlib.Cryptography.Foundations.Negligible
+import TCSlib.Cryptography.ZeroKnowledge.EncodingMachines
+import TCSlib.Complexity.Randomized.Closure
 
 set_option maxHeartbeats 0
 set_option relaxedAutoImplicit false
@@ -37,6 +39,22 @@ and what the non-uniform reduction of [PS10, Proposition 128.8] needs); the erro
 a function of `|x|` (the text's `e(n)` leaves `n` undefined); the honest-verifier notion is
 stated for a protocol and a witness relation without assuming the proof property, which the
 theorems add separately.
+The bound `Lz` is necessary, not only convenient (gate 03e, note 9): the distinguisher runs in
+time polynomial in its input, the encoded view, which contains `z`; with `|z| ≥ 2^n` it could
+invert a one-way permutation on `n`-bit inputs and open the unopened commitments of the
+3-colouring protocol, so computational zero-knowledge would fail for every protocol whose
+hiding is only computational. Read literally, [PS10, Definition 121.2] (every
+`z ∈ {0,1}*`, with `D` polynomial-time in its input) has the same defect. For the same reason
+the distinguisher's advice is indexed by the parameter `|x|`, not by its input length.
+
+**Perfect zero-knowledge (ruling G3-4 of gate 03).** With strict simulators and honest parties
+drawing polynomially many fair coins (D8, D10), no protocol of the source attains `PerfectZK`
+or `PerfectZKAbort` (see their docstrings). The source's perfect zero-knowledge protocol,
+graph isomorphism [PS10, Theorem 122.3], is formalized as `StatZK` with negligible error
+(`gi_statZK`, `ZeroKnowledge/GraphIsomorphismZK.lean`), the substantive instance of the
+notions of this file; `perfectZK_zeroRounds` is a degenerate one. The abort form implies
+statistical zero-knowledge with error `2^{-|x|}` (`PerfectZKAbort.statZK`), by running the
+aborting simulator `|x|` times on fresh coins (`AbortRetry.retry`).
 
 ## Main definitions
 
@@ -47,7 +65,10 @@ theorems add separately.
 * `TCSlib.Cryptography.StatZK`, `TCSlib.Cryptography.PerfectZK`,
   `TCSlib.Cryptography.PerfectZKAbort` — statistical zero-knowledge with error `δ(|x|)`,
   perfect zero-knowledge (`δ = 0`), and the abort form of perfect zero-knowledge
-  [Goldreich, *Foundations of Cryptography I*, Definition 4.3.1] (Def-122.a).
+  [Gol01, Definition 4.3.1] (Def-122.a).
+* `TCSlib.Cryptography.AbortRetry.attempt`, `TCSlib.Cryptography.AbortRetry.retry` — one
+  attempt of an aborting simulator on a coin block, and the simulator that retries it `|x|`
+  times (as functions of the machine layout).
 
 ## Main results
 
@@ -57,6 +78,15 @@ theorems add separately.
 * `TCSlib.Cryptography.ZK.hvzk` — zero-knowledge implies honest-verifier zero-knowledge.
 * `TCSlib.Cryptography.PerfectZK.zk`, `TCSlib.Cryptography.StatZK.mono` — perfect
   zero-knowledge is zero-knowledge; weakening the error.
+* `TCSlib.Cryptography.perfectZK_zeroRounds` — non-vacuity: the protocol with no messages is
+  perfectly zero-knowledge.
+* `TCSlib.Cryptography.PerfectZKAbort.statZK`, `TCSlib.Cryptography.PerfectZKAbort.zk` — the
+  abort form implies statistical zero-knowledge with error `2^{-|x|}`, hence zero-knowledge
+  (`TCSlib.Cryptography.AbortRetry.statClose_retry`: the first non-`⊥` output of `K`
+  independent runs of an aborting sampler is `2^{-K}`-close to its conditional law;
+  `TCSlib.Cryptography.AbortRetry.exists_retrySimulator`: the retrying simulator is a uniform
+  PPT, by `EncodingMachines.polyTimeComputable_firstIdx`, an instance of
+  `Complexity.polyTimeComputable_iterateFind`).
 * `TCSlib.Cryptography.negligible_inv_pow_sqrt_div`,
   `TCSlib.Cryptography.negligible_two_pow_neg_sqrt_div`,
   `TCSlib.Cryptography.negligible_exp_neg_sqrt_div`,
@@ -69,8 +99,8 @@ theorems add separately.
   (§4.6 Zero-knowledge, pp. 120–122.)
 * [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
   draft of 22 January 2026, Lemma 3.1 (statistical distance bounds every advantage).
-* O. Goldreich, *Foundations of Cryptography, Volume I: Basic Tools*, Cambridge University
-  Press, 2001, Definition 4.3.1 (perfect zero-knowledge with abort).
+* [Gol01] O. Goldreich, *Foundations of Cryptography, Volume I: Basic Tools*, Cambridge
+  University Press, 2001, Definition 4.3.1 (perfect zero-knowledge with abort).
 -/
 
 namespace TCSlib.Cryptography
@@ -114,7 +144,12 @@ the advantage of `D` between the view of `V'` in `P(x, y) ↔ V'(x, z)` and `S(x
 `ε(|x|)`.
 
 **Deviation (D8):** strict PPT simulator; auxiliary inputs bounded by `∀ Lz : PolyExpr`;
-simulator and distinguisher at parameter `|x|`; views encoded as `⟨⟨x, z⟩, ⟨r, msgs⟩⟩`. -/
+simulator and distinguisher at parameter `|x|`; views encoded as `⟨⟨x, z⟩, ⟨r, msgs⟩⟩`. The
+cheating verifier `V'` is only `Efficient`, with no message-prefix cap (question Q-1 of
+gate 03, ruled: no cap on `V*`), so its class is larger than the text's. Since the honest
+prover's messages are polynomially bounded in `|x|` in the proof systems
+(`Protocol.ProverBounded`, ruling G3-3 of gate 03), the view of every efficient `V'` — `x`,
+`z`, its tape and the honest prover's messages — is polynomially bounded all the same. -/
 def ZK (π : Protocol) (R : List Bool → List Bool → Prop) : Prop :=
   ∀ V' : Strategy, V'.Efficient → ∃ S : NUPPT, S.Uniform ∧
     ∀ (Lz : PolyExpr) (D : NUPPT), ∃ ε : ℕ → ℝ, Negligible ε ∧
@@ -134,15 +169,31 @@ def StatZK (π : Protocol) (R : List Bool → List Bool → Prop) (δ : ℕ →
     StatClose (fun r => ((π.withV V').viewV x y z r).encode) (S.simulate x z) (δ x.length)
 
 /-- Perfect zero-knowledge [PS10, §4.6, "perfect zero-knowledge"] (Def-122.a): statistical
-zero-knowledge with error `0`, i.e. the simulator's output has exactly the law of the view. -/
+zero-knowledge with error `0`, i.e. the simulator's output has exactly the law of the view.
+
+**Cost (D8, D10; ruling G3-4 of gate 03):** no protocol of the source attains this notion. A
+strict simulator with bit coins outputs every string with a dyadic probability, and an
+honest prover drawing polynomially many fair coins cannot draw a uniform permutation of
+`n ≥ 3` points (`n! ∤ 2^c`), so the reply of the honest graph-isomorphism prover
+[PS10, Protocol 120.6] depends on the witness. [PS10, Theorem 122.3] is formalized as
+`StatZK` with negligible error (`gi_statZK`); the instances of this notion are degenerate
+(`perfectZK_zeroRounds`). -/
 def PerfectZK (π : Protocol) (R : List Bool → List Bool → Prop) : Prop :=
   StatZK π R (fun _ => 0)
 
-/-- Perfect zero-knowledge with abort [Goldreich, Definition 4.3.1] (Def-122.a, the GMR form):
+/-- Perfect zero-knowledge with abort [Gol01, Definition 4.3.1] (Def-122.a, the GMR form):
 for every efficient `V'` there is a uniform PPT simulator that outputs `⊥ = []` with
 probability at most `1/2` and whose output, conditioned on not aborting, has exactly the law
 of the view of `V'`: for every test set `T`,
-`Pr[T(view)] · Pr[S ≠ ⊥] = Pr[S ≠ ⊥ ∧ T(S)]`. -/
+`Pr[T(view)] · Pr[S ≠ ⊥] = Pr[S ≠ ⊥ ∧ T(S)]` (`⊥ = []` is never a view encoding).
+
+**Cost (D8, D10; ruling G3-4 of gate 03):** no protocol of the source attains this notion:
+as for `PerfectZK`, the honest graph-isomorphism prover's permutation, drawn from fair coins,
+is not uniform, so its reply depends on the witness, which no simulator sees. The abort form
+holds for ideal permutations at the concrete layer (`giSimAttempt_perfectAbort`). It implies
+statistical zero-knowledge with error `2^{-|x|}` (`PerfectZKAbort.statZK`), hence
+zero-knowledge (`PerfectZKAbort.zk`); the source's "perfect" results are stated as `StatZK`
+with negligible error. -/
 def PerfectZKAbort (π : Protocol) (R : List Bool → List Bool → Prop) : Prop :=
   ∀ V' : Strategy, V'.Efficient → ∃ S : NUPPT, S.Uniform ∧ ∀ x y z, R x y →
     uprob (fun r : S.Coins x.length => S.simulate x z r = []) ≤ 1 / 2 ∧
@@ -208,6 +259,344 @@ theorem PerfectZK.zk {π : Protocol} {R : List Bool → List Bool → Prop} (h :
     ZK π R :=
   StatZK.zk negligible_const_zero h
 
+/-- Non-vacuity (gate 03e, note 10): the protocol with no messages is perfectly
+zero-knowledge for every relation.
+
+**Proof sketch.** The view of any `V'` is `⟨x, z, r, []⟩` (no moves, `exec_zero`), and the
+simulator `NUPPT.ofPolyTimeUniform` of the layout map `w ↦ ⟨inArg w, ⟨inCoins w, []⟩⟩` with
+`V'`'s coin polynomial outputs `⟨⟨x, z⟩, ⟨r, []⟩⟩` on its own tape `r`; the prover's tape does
+not enter the view (`uprob_fst` after `Equiv.prodComm`), so the two laws coincide. -/
+theorem perfectZK_zeroRounds (P V : Strategy) (b : Bool) (R : List Bool → List Bool → Prop) :
+    PerfectZK ⟨P, V, .const 0, b⟩ R := by
+  intro V' _
+  have hF : PolyTimeComputable fun w =>
+      pairEncode (NUPPT.inArg w) (pairEncode (NUPPT.inCoins w) []) :=
+    NUPPT.polyTimeComputable_inArg.pairEncode
+      (NUPPT.polyTimeComputable_inCoins.pairEncode (polyTimeComputable_const []))
+  refine ⟨NUPPT.ofPolyTimeUniform hF V'.coins, NUPPT.ofPolyTimeUniform_uniform hF _,
+    fun x y z _ T => ?_⟩
+  have h1 : uprob (fun r : (Protocol.withV ⟨P, V, .const 0, b⟩ V').ExecCoins P x =>
+      T ((Protocol.withV ⟨P, V, .const 0, b⟩ V').viewV x y z r).encode) =
+      uprob (fun ρ : V'.Coins x.length =>
+        T (pairEncode (pairEncode x z) (pairEncode (List.ofFn ρ) []))) := by
+    rw [← uprob_comp_equiv (Equiv.prodComm _ _)]
+    exact uprob_fst (fun ρ : V'.Coins x.length =>
+      T (pairEncode (pairEncode x z) (pairEncode (List.ofFn ρ) [])))
+  have h2 : uprob (fun ρ : (NUPPT.ofPolyTimeUniform hF V'.coins).Coins x.length =>
+      T ((NUPPT.ofPolyTimeUniform hF V'.coins).simulate x z ρ)) =
+      uprob (fun ρ : V'.Coins x.length =>
+        T (pairEncode (pairEncode x z) (pairEncode (List.ofFn ρ) []))) := by
+    refine OneWay.uprob_congr fun ρ => ?_
+    rw [NUPPT.simulate_eq, NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform]
+    simp [NUPPT.inArg, NUPPT.inCoins, NUPPT.advInput]
+  simp only [h2]
+  rw [abs_nonpos_iff, sub_eq_zero]
+  exact h1
+
+/-! ### Retrying an aborting simulator -/
+
+namespace AbortRetry
+
+open EncodingMachines Finset Complexity.StateLoop
+
+/-- One attempt of the retrying simulator on its machine layout
+`w = ⟨⟨⟨1^n, y⟩, α⟩, r⟩` at the index `t`: the simulator `S` at parameter `n = |1^n|` on the
+argument `y`, with empty advice and the `t`-th block of `S.coinLen n` coins of `r`. -/
+def attempt (S : NUPPT) (w : List Bool) (t : ℕ) : List Bool :=
+  S.output (NUPPT.layout (NUPPT.inParam w) (NUPPT.inArg w) []
+    (((NUPPT.inCoins w).drop (t * S.coinLen (NUPPT.inParam w).length)).take
+      (S.coinLen (NUPPT.inParam w).length)))
+
+/-- The retrying simulator on its machine layout `w = ⟨⟨⟨1^n, y⟩, α⟩, r⟩`
+(for the abort form of [Gol01, Definition 4.3.1], amplified by repetition): the
+first of the `n` attempts that does not output `⊥ = []` (the first accepted index,
+`EncodingMachines.firstIdx`), or `⊥` if every attempt aborts. -/
+noncomputable def retry (S : NUPPT) (w : List Bool) : List Bool :=
+  if firstIdx (fun t => decide (attempt S w t ≠ [])) (NUPPT.inParam w).length <
+      (NUPPT.inParam w).length then
+    attempt S w (firstIdx (fun t => decide (attempt S w t ≠ [])) (NUPPT.inParam w).length)
+  else []
+
+/-- One attempt is polynomial-time on the indexed layout `⟨1^t, w⟩`.
+
+**Proof sketch.** The block `(r.drop (t · c)).take c` with `c = S.coinLen n` in unary
+(`unaryPoly_comp`, `unaryMul_poly`, `polyTimeComputable_pairDropPoly`, `truncate_poly`), the
+layout (`NUPPT.polyTimeComputable_layout`) and the machine of `S`
+(`NUPPT.polyTimeComputable_output`). -/
+theorem attempt_poly (S : NUPPT) :
+    PolyTimeComputable fun u => attempt S (pairSndD u) (pairFstD u).length := by
+  have congr : ∀ {f g : List Bool → List Bool}, PolyTimeComputable f → (∀ w, g w = f w) →
+      PolyTimeComputable g := fun hf h => by rw [show _ = _ from funext h]; exact hf
+  have hpar : PolyTimeComputable fun u => NUPPT.inParam (pairSndD u) :=
+    NUPPT.polyTimeComputable_inParam.comp polyTimeComputable_pairSndD
+  have hr : PolyTimeComputable fun u => NUPPT.inCoins (pairSndD u) :=
+    NUPPT.polyTimeComputable_inCoins.comp polyTimeComputable_pairSndD
+  have hc : PolyTimeComputable fun u =>
+      List.replicate (S.coinLen (NUPPT.inParam (pairSndD u)).length) true :=
+    unaryPoly_comp S.coins hpar
+  have ht : PolyTimeComputable fun u => List.replicate (pairFstD u).length true :=
+    unaryLength_poly polyTimeComputable_pairFstD
+  have hdrop : PolyTimeComputable fun u => (NUPPT.inCoins (pairSndD u)).drop
+      ((pairFstD u).length * S.coinLen (NUPPT.inParam (pairSndD u)).length) :=
+    congr ((polyTimeComputable_pairDropPoly .var).comp ((unaryMul_poly ht hc).pairEncode hr))
+      fun u => by simp
+  have hblk := truncate_poly hdrop hc
+  have hlay := NUPPT.polyTimeComputable_layout hpar
+    (NUPPT.polyTimeComputable_inArg.comp polyTimeComputable_pairSndD)
+    (polyTimeComputable_const []) hblk
+  exact congr (S.polyTimeComputable_output.comp hlay) fun u => rfl
+
+/-- **The retrying simulator is polynomial-time** as a function of its layout: the first
+non-aborting index is `EncodingMachines.polyTimeComputable_firstIdx` (an instance of the
+repetition lemma `Complexity.polyTimeComputable_iterateFind`) with the test of
+`attempt_poly`, and the output is that attempt (`attempt_poly` at the found index) or `[]`
+(`polyTimeComputable_ite`). -/
+theorem retry_poly (S : NUPPT) : PolyTimeComputable (retry S) := by
+  have congr : ∀ {f g : List Bool → List Bool}, PolyTimeComputable f → (∀ w, g w = f w) →
+      PolyTimeComputable g := fun hf h => by rw [show _ = _ from funext h]; exact hf
+  have hatt := attempt_poly S
+  have hp : PolyTimeComputable fun u =>
+      [decide (attempt S (pairSndD u) (pairFstD u).length ≠ [])] :=
+    congr (ltTest_poly (unaryConst_poly 0) (unaryLength_poly hatt)) fun u => by
+      simp [List.length_pos_iff]
+  have hN : PolyTimeComputable fun w => List.replicate (NUPPT.inParam w).length true :=
+    unaryLength_poly NUPPT.polyTimeComputable_inParam
+  have hidx := polyTimeComputable_firstIdx (p := fun w t => decide (attempt S w t ≠ [])) hp hN
+  have hsel : PolyTimeComputable fun w => attempt S w
+      (firstIdx (fun t => decide (attempt S w t ≠ [])) (NUPPT.inParam w).length) :=
+    congr (hatt.comp (hidx.pairEncode polyTimeComputable_id)) fun w => by simp
+  refine congr (polyTimeComputable_ite (ltTest_poly hidx hN) hsel (polyTimeComputable_const []))
+    fun w => ?_
+  simp only [retry, decide_eq_true_eq]
+
+/-- **The retrying simulator is a uniform PPT**: `NUPPT.ofPolyTimeUniform` of `retry_poly`
+with `|x|` blocks of `S.coinLen |x|` coins; on `(x, z)` it computes `retry S` on the layout
+`⟨⟨⟨1^{|x|}, ⟨x, z⟩⟩, []⟩, r⟩` (`NUPPT.runAtL_ofPolyTimeUniform`). -/
+theorem exists_retrySimulator (S : NUPPT) :
+    ∃ S' : NUPPT, S'.Uniform ∧ S'.coins = .mul .var S.coins ∧
+      ∀ x z (r : S'.Coins x.length), S'.simulate x z r =
+        retry S (NUPPT.layout (List.replicate x.length true) (pairEncode x z) [] (List.ofFn r)) :=
+  ⟨NUPPT.ofPolyTimeUniform (retry_poly S) (.mul .var S.coins),
+    NUPPT.ofPolyTimeUniform_uniform _ _, rfl, fun x z r => by
+      rw [NUPPT.simulate_eq, NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform]
+      rfl⟩
+
+/-- The first hit of `K` draws read through `EncodingMachines.firstIdx`: if `a t` is `g` of
+the `t`-th draw and `q t` tests `E` on it (for `t < K`), then the first hit mapped by `g` and
+defaulted to `d` is `a` at the first index accepted by `q`, or `d` if there is none.
+
+**Proof sketch.** If `i := firstIdx q K < K`, the draw `i` is in `E` (`q_firstIdx`) and no
+earlier draw is (`firstIdx_min`); splitting `List.finRange K` at `i`
+(`List.drop_eq_getElem_cons`, `List.take_append_drop`, `List.getElem_finRange`) gives
+`firstHit E xs = some (xs i)` by `List.findSome?_eq_some_iff`. Otherwise no draw is in `E`
+(`firstIdx_eq_iff`) and `firstHit E xs = none` (`firstHit_eq_none_iff`). -/
+theorem firstHit_map_getD_eq {α β : Type*} (E : α → Prop) [DecidablePred E] {K : ℕ}
+    (xs : Fin K → α) (g : α → β) (d : β) (a : ℕ → β) (q : ℕ → Bool)
+    (ha : ∀ t (ht : t < K), a t = g (xs ⟨t, ht⟩))
+    (hq : ∀ t (ht : t < K), q t = decide (E (xs ⟨t, ht⟩))) :
+    ((firstHit E xs).map g).getD d = if firstIdx q K < K then a (firstIdx q K) else d := by
+  split_ifs with h
+  · set i := firstIdx q K with hi_def
+    have hEi : E (xs ⟨i, h⟩) := by
+      have := q_firstIdx h
+      rw [hq i h] at this
+      exact of_decide_eq_true this
+    have hmin : ∀ j (hj : j < i), ¬ E (xs ⟨j, hj.trans h⟩) := fun j hj hE => by
+      have := firstIdx_min hj
+      rw [hq j (hj.trans h)] at this
+      exact absurd (decide_eq_true hE) (by rw [this]; decide)
+    have hsome : firstHit E xs = some (xs ⟨i, h⟩) := by
+      unfold firstHit
+      rw [List.findSome?_eq_some_iff]
+      refine ⟨(List.finRange K).take i, ⟨i, h⟩, (List.finRange K).drop (i + 1), ?_, ?_, ?_⟩
+      · have hlen : i < (List.finRange K).length := by simpa using h
+        have hsplit : List.finRange K = (List.finRange K).take i ++
+            (List.finRange K)[i] :: (List.finRange K).drop (i + 1) := by
+          rw [← List.drop_eq_getElem_cons hlen, List.take_append_drop]
+        rw [List.getElem_finRange] at hsplit
+        exact hsplit
+      · simp [hEi]
+      · intro j hj
+        obtain ⟨k, hk, rfl⟩ := List.mem_take_iff_getElem.1 hj
+        have hki : k < i := lt_of_lt_of_le hk (min_le_left _ _)
+        simp [hmin k hki]
+    rw [hsome, ha i h]
+    rfl
+  · have hall := firstIdx_eq_iff.1 (le_antisymm firstIdx_le (not_lt.1 h))
+    have hnone : firstHit E xs = none := (firstHit_eq_none_iff E xs).2 fun t hE => by
+      have := hall t t.isLt
+      rw [hq t t.isLt] at this
+      exact absurd (decide_eq_true hE) (by rw [this]; decide)
+    rw [hnone]
+    rfl
+
+/-- **Retrying an aborting sampler** (amplification by repetition): let `g` be a
+sampler on a finite uniform space `Ω`, `E` the event "`g` does not abort", with
+`Pr[¬ E] ≤ 1/2`, and suppose the output of `g` conditioned on `E` has the law of the sampler
+`Y`. Then the output of `g` on the first of `K` independent draws in `E` (the default `d₀` if
+there is none) is within `2^{-K}` of `Y`.
+
+**Proof sketch.** Let `p := Pr[E] ≥ 1/2` and `f := (1 - p)^K`, the probability that no draw
+is in `E` (`uprob_firstHit_none`). Each `a ∈ E` is the first hit with the same probability
+`q₀` (`firstHit_uniform_of_some`), so for a test set `T`, splitting over the fibres of
+`firstHit` (`uprob_comp_eq_sum_fiber`, `Fintype.sum_option`),
+`Pr[T(retry)] = [T d₀] · f + q₀ · #{a ∈ E : T (g a)}`, and with `T := ⊤`,
+`1 = f + q₀ · #E`. The conditional-law hypothesis times `|Ω|` is
+`Pr[T(Y)] · #E = #{a ∈ E : T (g a)}`, so `Pr[T(retry)] = [T d₀] · f + (1 - f) · Pr[T(Y)]`
+(`linear_combination`) and `|Pr[T(Y)] - Pr[T(retry)]| = f · |Pr[T(Y)] - [T d₀]| ≤ f ≤ 2^{-K}`. -/
+theorem statClose_retry {Ω τ : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω] [Fintype τ]
+    (E : Ω → Prop) [DecidablePred E] (g : Ω → List Bool) (Y : τ → List Bool) (d₀ : List Bool)
+    (habort : uprob (fun ω => ¬ E ω) ≤ 1 / 2)
+    (hcond : ∀ T : List Bool → Prop,
+      uprob (fun t => T (Y t)) * uprob E = uprob (fun ω => E ω ∧ T (g ω)))
+    (K : ℕ) :
+    StatClose Y (fun ws : Fin K → Ω => ((firstHit E ws).map g).getD d₀) ((2 : ℝ)⁻¹ ^ K) := by
+  classical
+  intro T
+  have hpE : uprob E = 1 - uprob (fun ω => ¬ E ω) := by rw [uprob_not]; ring
+  obtain ⟨d, hd⟩ : ∃ d, E d := by
+    by_contra hne
+    push_neg at hne
+    have h0 : uprob E = 0 := by
+      rw [← uprob_false (α := Ω)]
+      exact OneWay.uprob_congr fun ω => ⟨fun h => hne ω h, False.elim⟩
+    linarith
+  have hsome : ∀ a, E a → uprob (fun xs : Fin K → Ω => firstHit E xs = some a) =
+      uprob (fun xs : Fin K → Ω => firstHit E xs = some d) :=
+    fun a ha => firstHit_uniform_of_some E K ha hd
+  have hnot : ∀ a, ¬ E a → uprob (fun xs : Fin K → Ω => firstHit E xs = some a) = 0 := by
+    intro a ha
+    rw [← uprob_false (α := Fin K → Ω)]
+    exact OneWay.uprob_congr fun xs => ⟨fun h => ha (firstHit_eq_some_imp E h), False.elim⟩
+  have hdec : ∀ S' : Option Ω → Prop, uprob (fun xs : Fin K → Ω => S' (firstHit E xs)) =
+      (if S' none then (1 - uprob E) ^ K else 0) +
+        uprob (fun xs : Fin K → Ω => firstHit E xs = some d) *
+          (univ.filter fun a => E a ∧ S' (some a)).card := by
+    intro S'
+    rw [uprob_comp_eq_sum_fiber (firstHit E) S', sum_filter, Fintype.sum_option,
+      uprob_firstHit_none E K]
+    congr 1
+    rw [mul_comm, ← nsmul_eq_mul, ← sum_const, sum_filter]
+    refine sum_congr rfl fun a _ => ?_
+    by_cases hSa : S' (some a)
+    · by_cases hEa : E a
+      · simp [hSa, hEa, hsome a hEa]
+      · simp [hSa, hEa, hnot a hEa]
+    · simp [hSa]
+  have hsim := hdec fun o => T ((o.map g).getD d₀)
+  have htot := hdec fun _ => True
+  rw [uprob_true] at htot
+  simp only [Option.map_none, Option.getD_none, Option.map_some, Option.getD_some, if_true,
+    and_true] at hsim htot
+  -- the conditional law in counting form
+  have hcard : (Fintype.card Ω : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
+  have hc := hcond T
+  rw [uprob_eq_card_filter E, uprob_eq_card_filter (fun ω => E ω ∧ T (g ω)), mul_div_assoc',
+    div_left_inj' hcard] at hc
+  generalize uprob (fun xs : Fin K → Ω => firstHit E xs = some d) = q₀ at hsim htot
+  generalize hf : (1 - uprob E) ^ K = f at hsim htot
+  have hY0 := uprob_nonneg (fun t => T (Y t))
+  have hY1 := uprob_le_one (fun t => T (Y t))
+  have hsimeq : uprob (fun xs : Fin K → Ω => T (((firstHit E xs).map g).getD d₀)) =
+      (if T d₀ then f else 0) + (1 - f) * uprob (fun t => T (Y t)) := by
+    rw [hsim]
+    linear_combination (-q₀) * hc + (-uprob (fun t => T (Y t))) * htot
+  have hf0 : 0 ≤ f := hf ▸ pow_nonneg (by linarith [uprob_le_one E]) K
+  have hfK : f ≤ (2 : ℝ)⁻¹ ^ K :=
+    hf ▸ pow_le_pow_left₀ (by linarith [uprob_le_one E]) (by linarith) K
+  show |uprob (fun t => T (Y t)) -
+    uprob (fun xs : Fin K → Ω => T (((firstHit E xs).map g).getD d₀))| ≤ (2 : ℝ)⁻¹ ^ K
+  rw [hsimeq, abs_le]
+  split_ifs <;> constructor <;> nlinarith
+
+/-- The probability that the retrying simulator's attempt aborts is the complement of its
+success probability (a restatement of `PerfectZKAbort`'s first clause for
+`AbortRetry.statClose_retry`). -/
+theorem uprob_not_ne_nil_le {Ω : Type*} [Fintype Ω] (g : Ω → List Bool)
+    (h : uprob (fun ω => g ω = []) ≤ 1 / 2) : uprob (fun ω => ¬ g ω ≠ []) ≤ 1 / 2 := by
+  simpa using h
+
+end AbortRetry
+
+open AbortRetry in
+/-- **Perfect zero-knowledge with abort implies statistical zero-knowledge with error
+`2^{-|x|}`** (the abort form of [Gol01, Definition 4.3.1], amplified by repetition)
+(ruling G3-4 of gate 03): retry the aborting simulator on `|x|` disjoint coin blocks and
+output the first non-`⊥` result.
+
+**Proof sketch.** For an efficient `V'` take the aborting simulator `S` of `h`; the
+retrying simulator `S'` of `AbortRetry.exists_retrySimulator` is a uniform PPT with `|x|`
+blocks of `S.coinLen |x|` coins. Read its tape as `|x|` independent blocks (the bijection
+`e` built from `finCongr`, `finProdFinEquiv` and `Equiv.curry`, through
+`StatClose.comp_equiv_right`): the `t`-th slice of the tape is `List.ofFn` of block `t`, so
+attempt `t` is `S` on block `t` (`S` is uniform, so its advice is `[]`), and the retrying
+simulator is the first non-`⊥` attempt (`AbortRetry.firstHit_map_getD_eq`). The two clauses
+of `h` are the hypotheses of `AbortRetry.statClose_retry` with `K = |x|`. -/
+theorem PerfectZKAbort.statZK {π : Protocol} {R : List Bool → List Bool → Prop}
+    (h : PerfectZKAbort π R) : StatZK π R (fun n => (2 : ℝ)⁻¹ ^ n) := by
+  intro V' hV'
+  obtain ⟨S, hSu, hS⟩ := h V' hV'
+  obtain ⟨S', hS'u, hS'c, hS'⟩ := exists_retrySimulator S
+  refine ⟨S', hS'u, fun x y z hxy => ?_⟩
+  obtain ⟨habort, hcond⟩ := hS x y z hxy
+  have hlen : S'.coinLen x.length = x.length * S.coinLen x.length := by
+    simp only [NUPPT.coinLen, hS'c, PolyExpr.eval_mul, PolyExpr.eval_var]
+  -- the tape of `S'` as `|x|` blocks of `S.coinLen |x|` coins
+  let e : S'.Coins x.length ≃ (Fin x.length → S.Coins x.length) :=
+    ((Equiv.arrowCongr (finCongr hlen) (Equiv.refl Bool)).trans
+      (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl Bool))).trans (Equiv.curry _ _ _)
+  have hblock : ∀ (r : S'.Coins x.length) (t : ℕ) (ht : t < x.length),
+      ((List.ofFn r).drop (t * S.coinLen x.length)).take (S.coinLen x.length) =
+        List.ofFn (e r ⟨t, ht⟩) := by
+    intro r t ht
+    have hle : t * S.coinLen x.length + S.coinLen x.length ≤ x.length * S.coinLen x.length := by
+      rw [← Nat.succ_mul]
+      exact Nat.mul_le_mul_right _ ht
+    refine List.ext_getElem ?_ fun j h₁ h₂ => ?_
+    · simp only [List.length_take, List.length_drop, List.length_ofFn, hlen]
+      omega
+    · simp only [List.getElem_take, List.getElem_drop, List.getElem_ofFn]
+      simp only [e, Equiv.trans_apply, Equiv.arrowCongr_apply, Equiv.coe_refl,
+        Function.comp_apply, Equiv.symm_symm, Equiv.curry_apply, Function.curry_apply]
+      congr 1
+      ext
+      simp [finProdFinEquiv]
+      ring
+  have hatt : ∀ (r : S'.Coins x.length) (t : ℕ) (ht : t < x.length),
+      attempt S (NUPPT.layout (List.replicate x.length true) (pairEncode x z) [] (List.ofFn r)) t =
+        S.simulate x z (e r ⟨t, ht⟩) := by
+    intro r t ht
+    simp only [attempt, NUPPT.inParam_layout, NUPPT.inArg_layout, NUPPT.inCoins_layout,
+      List.length_replicate]
+    rw [hblock r t ht, NUPPT.simulate_eq, NUPPT.runAt_eq, NUPPT.runAtL_eq_output_layout, hSu]
+  have heq : ∀ r : S'.Coins x.length, S'.simulate x z r =
+      ((firstHit (fun ω => S.simulate x z ω ≠ []) (e r)).map (S.simulate x z)).getD [] := by
+    intro r
+    rw [hS' x z r, firstHit_map_getD_eq (fun ω => S.simulate x z ω ≠ []) (e r)
+      (S.simulate x z) []
+      (attempt S (NUPPT.layout (List.replicate x.length true) (pairEncode x z) [] (List.ofFn r)))
+      (fun t => decide (attempt S
+        (NUPPT.layout (List.replicate x.length true) (pairEncode x z) [] (List.ofFn r)) t ≠ []))
+      (hatt r) (fun t ht => by simp only [hatt r t ht])]
+    simp only [retry, NUPPT.inParam_layout, List.length_replicate]
+  have key := (statClose_retry (fun ω => S.simulate x z ω ≠ []) (S.simulate x z)
+    (fun r : (π.withV V').ExecCoins π.P x => ((π.withV V').viewV x y z r).encode) []
+    (uprob_not_ne_nil_le _ habort) hcond x.length).comp_equiv_right e
+  intro T
+  have hu : uprob (fun t : S'.Coins x.length => T (S'.simulate x z t)) =
+      uprob (fun t : S'.Coins x.length => T (((firstHit (fun ω => S.simulate x z ω ≠ []) (e t)).map
+        (S.simulate x z)).getD [])) :=
+    OneWay.uprob_congr fun t => by rw [heq t]
+  rw [hu]
+  exact key T
+
+/-- **Perfect zero-knowledge with abort implies zero-knowledge** (ruling G3-4 of gate 03):
+`PerfectZKAbort.statZK` and `StatZK.zk` with the negligible error `2^{-n}`
+(`negligible_two_pow_neg`). -/
+theorem PerfectZKAbort.zk {π : Protocol} {R : List Bool → List Bool → Prop}
+    (h : PerfectZKAbort π R) : ZK π R :=
+  h.statZK.zk negligible_two_pow_neg
+
 /-! ### Negligibility in the instance length (Inf-4.4) -/
 
 /-- For `a > 1` and `C > 0` the function `N ↦ a^{-√(N / C)}` (with `Nat.sqrt` and natural
diff --git a/TCSlib/Cryptography/ZeroKnowledge/Interaction.lean b/TCSlib/Cryptography/ZeroKnowledge/Interaction.lean
index 8fdeb8bf..23519614 100644
--- a/TCSlib/Cryptography/ZeroKnowledge/Interaction.lean
+++ b/TCSlib/Cryptography/ZeroKnowledge/Interaction.lean
@@ -36,15 +36,24 @@ activation has exactly the arguments of the activation that produced its last me
 last message *is* its verdict (`Protocol.outV_eq_getLast_of_moverIsV`); the chapter's protocols
 are stated with the prover moving last, and the `n`-fold protocols read the verifier's last
 message as the verdict.
+Repetition convention (gate 03e, note 8): an iteration with an odd number of messages (prover,
+verifier, prover) is repeated under strict alternation by appending one dummy empty verifier
+message to each iteration, so that every iteration starts with the prover; the fourth move of
+`giProtocolRep` and of `colProtocolRep`, and the filler moves of the sequential repetition of
+[PS10, §7.2.1] in ch. 7, follow this convention.
 `Strategy.Efficient` ([PS10, §4.4], time complexity of an interactive machine) is one
 activation of a uniform `Complexity.NUPPT` at parameter `|x|` on `⟨⟨x, z⟩, messages⟩` with the
 whole random tape; the time is polynomial in the total input length rather than in `|x|`
-alone (the text's `t(|x|)` "regardless of messages" would leave the simulator's call to `V*`
-on long auxiliary inputs ill-defined; see D8). Consequently `Efficient` alone does not bound a
-party's work in `|x|` against a counterparty that sends long messages; the message-prefix cap
-`Strategy.ReadsPrefix m` — the strategy depends only on the first `m(|x|)` bits of each received
-message, as a time-`t(|x|)` machine of the text necessarily does — restores the text's bound,
-and the class `IP` (`InteractiveProofs.lean`) requires it of the verifier (run-3 audit P9-1).
+alone (the text's bound `t(|x|)`, which holds whatever the messages received, would leave the
+simulator's call to `V*` on long auxiliary inputs ill-defined; see D8). Consequently
+`Efficient` alone bounds neither a party's work in `|x|` against a counterparty that sends long
+messages nor the length of its own messages. The proof systems (`InteractiveProofs.lean`)
+therefore add the bound on the honest prover's messages, `Protocol.ProverBounded` (ruling G3-3
+of gate 03, the convention of ch. 6: `Efficient` plus polynomially bounded honest messages);
+the message-prefix cap `Strategy.ReadsPrefix m` — the strategy depends only on the first
+`m(|x|)` bits of each received message, as a time-`t(|x|)` machine of the text necessarily
+does — is the text's bound on the reading side, and the class `IP` (`InteractiveProofs.lean`)
+requires it of the verifier (run-3 audit P9-1).
 
 ## Main definitions
 
@@ -59,6 +68,9 @@ and the class `IP` (`InteractiveProofs.lean`) requires it of the verifier (run-3
   (Def-114.b); `Protocol.transcriptWith`, `Protocol.transcript` (Def-115.c), `Protocol.outV`,
   `Protocol.outP`, `Strategy.out` (Def-115.d), `Protocol.viewV`, `Protocol.viewP`,
   `Protocol.execution` (Def-115.a/b), `Protocol.withV`.
+* `TCSlib.Cryptography.Protocol.ProverBounded` — the honest prover's messages have at most
+  `B(|x|)` bits on instances with a witness (Def-116.b, the writing half of the text's bound
+  in `|x|`; ruling G3-3).
 
 ## Main results
 
@@ -140,17 +152,21 @@ theorem ofNUPPT_next (A : NUPPT) (x z r : List Bool) (hist : List (List Bool)) :
     (ofNUPPT A).next x z r hist =
       A.runAtL x.length (pairEncode (pairEncode x z) (encodeMsgs hist)) r := rfl
 
-/-- A PPT strategy [PS10, §4.4, time complexity of an interactive machine] (Def-116.b): the
-next-message function is computed by a uniform `NUPPT` with the same coin polynomial, one
-activation per message at parameter `|x|` on `⟨⟨x, z⟩, messages⟩` with the whole random tape.
+/-- An efficient strategy, the formal counterpart of the text's PPT interactive machine
+[PS10, §4.4, time complexity of an interactive machine] (Def-116.b): the next-message function
+is computed by a uniform `NUPPT` with the same coin polynomial, one activation per message at
+parameter `|x|` on `⟨⟨x, z⟩, messages⟩` with the whole random tape.
 
 **Deviation (D8):** per-activation time polynomial in the total input length `|x| + |z| +
-|messages|` instead of the text's `t(|x|)` "regardless of the messages". The number of
-activations is bounded by the protocol's `rounds`, but the messages of an unbounded
-counterparty may be arbitrarily long, so `Efficient` alone does not bound a party's work in
-`|x|` (run-3 audit P9-1). The text's bound is recovered by adding the message-prefix cap
-`ReadsPrefix m`: an efficient strategy that reads only `m(|x|)` bits of each message runs in
-time polynomial in `|x| + |z|`, and the class `IP` requires the cap of the verifier. -/
+|messages|` instead of the text's `t(|x|)`, which bounds the running time whatever the
+messages received. The number of activations is bounded by the protocol's `rounds`, but the
+messages of an unbounded counterparty may be arbitrarily long, so `Efficient` alone does not
+bound a party's work in `|x|` (run-3 audit P9-1), nor the length of the messages it writes.
+The text's bound is recovered on the reading side by the message-prefix cap `ReadsPrefix m`
+(an efficient strategy that reads only `m(|x|)` bits of each message runs in time polynomial
+in `|x| + |z|`; the class `IP` requires it of the verifier) and on the writing side, for the
+honest prover, by `Protocol.ProverBounded` (its messages have at most `B(|x|)` bits; the proof
+systems require it, ruling G3-3 of gate 03). -/
 def Efficient (S : Strategy) : Prop :=
   ∃ A : NUPPT, A.Uniform ∧ S.coins = A.coins ∧
     ∀ x z r hist, S.next x z r hist = (ofNUPPT A).next x z r hist
@@ -299,6 +315,27 @@ prover's and the verifier's random tapes at parameter `|x|` [PS10, §4.4, random
 abbrev ExecCoins (π : Protocol) (P' : Strategy) (x : List Bool) : Type :=
   P'.Coins x.length × π.V.Coins x.length
 
+/-- **The honest prover's messages are short** with respect to the witness relation `R` and
+the polynomial `B` [PS10, §4.4, time complexity: a machine of time complexity `t(|x|)` halts
+within `t(|x|)` steps whatever it receives, so each of its messages has at most `t(|x|)` bits]:
+on every instance `x` with a witness `y` (`R x y`), whatever its random tape and whatever it
+has received, the honest prover's message has at most `B(|x|)` bits.
+
+**Deviation (D8; ruling G3-3 of gate 03, the convention of ch. 6):** `Strategy.Efficient`
+bounds a party's work, hence its messages, only in the total length of its input, which
+contains the messages it has received; the bound in `|x|` is this separate condition, a field
+of `EfficientProverProof` (and, for the completeness witness, part of the completeness clause
+of `InteractiveProof`). Without it an honest prover that echoes the verifier's messages —
+zero-knowledge for one run — lets a cheating verifier that doubles its messages build a view
+of length `2^{rounds}`, which the composition theorems of ch. 7 cannot simulate. -/
+def ProverBounded (π : Protocol) (R : List Bool → List Bool → Prop) (B : PolyExpr) : Prop :=
+  ∀ x y r hist, R x y → (π.P.next x y r hist).length ≤ B.eval x.length
+
+/-- A message bound `B` implies every pointwise larger bound `B'`. -/
+theorem ProverBounded.mono {π : Protocol} {R : List Bool → List Bool → Prop} {B B' : PolyExpr}
+    (h : π.ProverBounded R B) (hle : ∀ n, B.eval n ≤ B'.eval n) : π.ProverBounded R B' :=
+  fun x y r hist hxy => (h x y r hist hxy).trans (hle _)
+
 /-- The protocol with the verifier replaced by `V'` (the cheating verifier `V*` of the
 zero-knowledge definitions), same prover, round count and first mover. -/
 def withV (π : Protocol) (V' : Strategy) : Protocol := { π with V := V' }
diff --git a/TCSlib/Cryptography/ZeroKnowledge/InteractiveProofs.lean b/TCSlib/Cryptography/ZeroKnowledge/InteractiveProofs.lean
index 2886aa2a..6b774497 100644
--- a/TCSlib/Cryptography/ZeroKnowledge/InteractiveProofs.lean
+++ b/TCSlib/Cryptography/ZeroKnowledge/InteractiveProofs.lean
@@ -33,10 +33,21 @@ read as the output string `[false]`, the negligible `ε` quantified before the i
 cheating prover and its auxiliary input; cheating provers are arbitrary strategies with a
 polynomial random tape (unbounded computation; polynomial coin tapes lose nothing by
 averaging, `Protocol.exists_proverCoins_le`). Completeness is `uprob = 1`, i.e. acceptance on
-every pair of random tapes. The verifier's efficiency is `Strategy.Efficient`, polynomial time
-in `|x| + |z| + |messages|` (D8), so `InteractiveProof` alone does not bound the verifier's
-work in `|x|` against an unbounded prover sending long messages; the class `IP` adds the
-message-prefix cap `Strategy.ReadsPrefix` (run-3 audit P9-1).
+every pair of random tapes. The parties' efficiency (the text's "p.p.t.") is
+`Strategy.Efficient`, polynomial time in `|x| + |z| + |messages|` (D8), together with a
+polynomial bound `B(|x|)` on the honest prover's messages (ruling G3-3 of gate 03, the
+convention of ch. 6): in the completeness clause of `InteractiveProof` and
+`InteractiveProofErr` for the completeness witness, and as the field `boundedP`
+(`Protocol.ProverBounded`) of `EfficientProverProof` and `EfficientProverProofErr` for every
+witness. The residual deviation is that against a cheating prover the verifier's work is
+polynomial in the length of the messages it receives, not in `|x|`. Since the honest messages
+are short, the verifier can always be capped: `V` reading only the first `B(|x|)` bits of each
+message is still complete (the honest messages are untouched) and sound (against `P*` it acts
+as `V` against `P*` with truncated messages, another prover strategy). So the proof systems
+hold only for languages of the text's class IP — undecidable languages such as the halting
+problem, whose computation histories are not polynomially bounded, are excluded — while
+`IP` itself is stated with the message-prefix cap `Strategy.ReadsPrefix` of the verifier
+(run-3 audit P9-1). The capping argument is not formalized as a lemma.
 
 ## Main definitions
 
@@ -58,13 +69,18 @@ message-prefix cap `Strategy.ReadsPrefix` (run-3 audit P9-1).
 * `TCSlib.Cryptography.InteractiveProofErr.interactiveProof`,
   `TCSlib.Cryptography.InteractiveProof.exists_err` — a negligible soundness error gives an
   interactive proof and conversely.
+* `TCSlib.Cryptography.InteractiveProof.exists_accept`,
+  `TCSlib.Cryptography.Protocol.ProverBounded.exists_complete` — completeness without the
+  message bound, and completeness with the bound from bounded messages and completeness for
+  every witness.
 * `TCSlib.Cryptography.InteractiveProof.exists_uprob_accept_lt` — the acceptance form of
   soundness, `Pr[out_V = [true]] < ε(|x|)`.
 * `TCSlib.Cryptography.WitnessRelation.mem_NP`,
   `TCSlib.Cryptography.exists_witnessRelation_of_mem_NP` — witness relations characterize
   `Complexity.NP` (the bridge to the certificate definition of `ClassNP/NP.lean`).
 * `TCSlib.Cryptography.npProtocol_interactiveProof` — non-vacuity: sending a witness is an
-  interactive proof with efficient prover; `TCSlib.Cryptography.npProtocol_readsPrefix`,
+  interactive proof with efficient prover (`TCSlib.Cryptography.npProtocol_proverBounded`: its
+  prover's message is the witness); `TCSlib.Cryptography.npProtocol_readsPrefix`,
   `TCSlib.Cryptography.WitnessRelation.mem_IP`, `TCSlib.Cryptography.NP_subset_IP` — its
   verifier reads a polynomial prefix, hence `NP ⊆ IP` (Claim-117.c).
 
@@ -83,25 +99,33 @@ open Complexity Turing
 /-! ### Interactive proofs -/
 
 /-- An interactive proof system for `L` [PS10, Definition 116.1] (Def-116.1): the verifier is
-efficient; completeness — for every `x ∈ L` there is an auxiliary input `y` such that for every
+efficient; completeness — for a polynomial `B` and every `x ∈ L` there is an auxiliary input
+`y` on which the honest prover's messages have at most `B(|x|)` bits and such that for every
 `z` the honest execution `P(x, y) ↔ V(x, z)` makes `V` output `1` with probability one;
 soundness — there is a negligible `ε` such that for every `x ∉ L`, every (unbounded) prover
 strategy `P'` and every `z`, `V` outputs `0` in `P'(x) ↔ V(x, z)` with probability greater than
 `1 - ε(|x|)`.
 
-**Deviation (D8):** `out_V = 0` is the literal output string `[false]` on the complete
-history of the fixed-alternation execution; `P'` ranges over strategies with polynomial
-random tapes and receives no auxiliary input (the text's `P*(x)`); completeness is `uprob = 1`
-(every pair of random tapes). The verifier is `Strategy.Efficient`, i.e. polynomial-time in
-`|x| + |z| + |messages|` (D8), so this predicate alone does not bound the verifier's work in
-`|x|` against an unbounded prover sending long messages; the class `IP` adds the
-message-prefix cap `Strategy.ReadsPrefix` (run-3 audit P9-1). -/
+**Deviation (D8; ruling G3-3 of gate 03):** `out_V = 0` is the literal output string `[false]`
+on the complete history of the fixed-alternation execution; `P'` ranges over strategies with
+polynomial random tapes and receives no auxiliary input (the text's `P*(x)`); completeness is
+`uprob = 1` (every pair of random tapes). The verifier's "p.p.t." is `Strategy.Efficient`,
+polynomial-time in `|x| + |z| + |messages|` (D8), and the honest messages on the completeness
+witness are bounded by `B(|x|)` (the text's p.p.t. prover writes at most `t(|x|)` bits; the
+convention of ch. 6). Against a cheating prover the verifier's work is polynomial in the
+length of the messages it receives, not in `|x|`; because the honest messages are short the
+verifier can be capped to their length without losing completeness or soundness (module
+docstring), so the predicate holds only for languages of the text's class IP. The class `IP`
+is stated with the message-prefix cap `Strategy.ReadsPrefix` (run-3 audit P9-1). -/
 structure InteractiveProof (π : Protocol) (L : Language Bool) : Prop where
-  /-- The verifier is a PPT strategy. -/
+  /-- The verifier is efficient (`Strategy.Efficient`, D8). -/
   efficientV : π.V.Efficient
-  /-- Completeness: some auxiliary input makes the honest verifier accept with probability one. -/
-  complete : ∀ x ∈ L, ∃ y : List Bool, ∀ z : List Bool,
-    uprob (fun r : π.ExecCoins π.P x => π.outV π.P x y z r = [true]) = 1
+  /-- Completeness: for a polynomial `B`, every `x ∈ L` has an auxiliary input on which the
+  honest prover's messages have at most `B(|x|)` bits and the honest verifier accepts with
+  probability one. -/
+  complete : ∃ B : PolyExpr, ∀ x ∈ L, ∃ y : List Bool,
+    (∀ r hist, (π.P.next x y r hist).length ≤ B.eval x.length) ∧
+    ∀ z : List Bool, uprob (fun r : π.ExecCoins π.P x => π.outV π.P x y z r = [true]) = 1
   /-- Soundness: against every prover strategy the verifier rejects with probability
   `> 1 - ε(|x|)` for a negligible `ε`. -/
   sound : ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ x ∉ L, ∀ (P' : Strategy) (z : List Bool),
@@ -112,15 +136,19 @@ structure InteractiveProof (π : Protocol) (L : Language Bool) : Prop where
 function `s` (for instance the constant `1/2` of the single-iteration graph-isomorphism
 protocol).
 
-**Deviation (D8):** as for `InteractiveProof` (literal `[false]`, provers with polynomial
-tapes, `uprob = 1` completeness; verifier time in the total input length — the message-prefix
-cap is added in `IP`, run-3 audit P9-1). -/
+**Deviation (D8; ruling G3-3 of gate 03):** as for `InteractiveProof` (literal `[false]`,
+provers with polynomial tapes, `uprob = 1` completeness with honest messages of at most
+`B(|x|)` bits; verifier time in the total input length — the message-prefix cap is added in
+`IP`, run-3 audit P9-1). -/
 structure InteractiveProofErr (π : Protocol) (L : Language Bool) (s : ℕ → ℝ) : Prop where
-  /-- The verifier is a PPT strategy. -/
+  /-- The verifier is efficient (`Strategy.Efficient`, D8). -/
   efficientV : π.V.Efficient
-  /-- Completeness: some auxiliary input makes the honest verifier accept with probability one. -/
-  complete : ∀ x ∈ L, ∃ y : List Bool, ∀ z : List Bool,
-    uprob (fun r : π.ExecCoins π.P x => π.outV π.P x y z r = [true]) = 1
+  /-- Completeness: for a polynomial `B`, every `x ∈ L` has an auxiliary input on which the
+  honest prover's messages have at most `B(|x|)` bits and the honest verifier accepts with
+  probability one. -/
+  complete : ∃ B : PolyExpr, ∀ x ∈ L, ∃ y : List Bool,
+    (∀ r hist, (π.P.next x y r hist).length ≤ B.eval x.length) ∧
+    ∀ z : List Bool, uprob (fun r : π.ExecCoins π.P x => π.outV π.P x y z r = [true]) = 1
   /-- Soundness error `s`: the verifier rejects with probability at least `1 - s(|x|)`. -/
   sound : ∀ x ∉ L, ∀ (P' : Strategy) (z : List Bool),
     1 - s x.length ≤ uprob (fun r : π.ExecCoins P' x => π.outV P' x [] z r = [false])
@@ -172,6 +200,40 @@ theorem InteractiveProof.exists_uprob_accept_lt {π : Protocol} {L : Language Bo
   rw [uprob_not] at h2
   linarith
 
+/-- Completeness without the message bound (the form in which consumers use it): every
+`x ∈ L` has an auxiliary input on which the honest verifier accepts with probability one. -/
+theorem InteractiveProof.exists_accept {π : Protocol} {L : Language Bool}
+    (h : InteractiveProof π L) : ∀ x ∈ L, ∃ y : List Bool, ∀ z : List Bool,
+      uprob (fun r : π.ExecCoins π.P x => π.outV π.P x y z r = [true]) = 1 := fun x hx =>
+  let ⟨_, hB⟩ := h.complete
+  let ⟨y, _, hy⟩ := hB x hx
+  ⟨y, hy⟩
+
+/-- Completeness without the message bound, for an interactive proof with soundness error. -/
+theorem InteractiveProofErr.exists_accept {π : Protocol} {L : Language Bool} {s : ℕ → ℝ}
+    (h : InteractiveProofErr π L s) : ∀ x ∈ L, ∃ y : List Bool, ∀ z : List Bool,
+      uprob (fun r : π.ExecCoins π.P x => π.outV π.P x y z r = [true]) = 1 := fun x hx =>
+  let ⟨_, hB⟩ := h.complete
+  let ⟨y, _, hy⟩ := hB x hx
+  ⟨y, hy⟩
+
+/-- The completeness clause of `InteractiveProof` from bounded honest messages: if the honest
+prover's messages have at most `B(|x|)` bits on instances with an `R`-witness
+(`Protocol.ProverBounded`), every witness makes the honest verifier accept with probability
+one, and every `x ∈ L` has a witness, then the clause holds with the bound `B` and the
+witnesses as auxiliary inputs. -/
+theorem Protocol.ProverBounded.exists_complete {π : Protocol} {L : Language Bool}
+    {R : List Bool → List Bool → Prop} {B : PolyExpr} (hB : π.ProverBounded R B)
+    (hLR : ∀ x ∈ L, ∃ y, R x y)
+    (hc : ∀ x y, R x y → ∀ z : List Bool,
+      uprob (fun r : π.ExecCoins π.P x => π.outV π.P x y z r = [true]) = 1) :
+    ∃ B : PolyExpr, ∀ x ∈ L, ∃ y : List Bool,
+      (∀ r hist, (π.P.next x y r hist).length ≤ B.eval x.length) ∧
+      ∀ z : List Bool, uprob (fun r : π.ExecCoins π.P x => π.outV π.P x y z r = [true]) = 1 :=
+  ⟨B, fun x hx =>
+    let ⟨y, hy⟩ := hLR x hx
+    ⟨y, fun r hist => hB x y r hist hy, hc x y hy⟩⟩
+
 /-! ### Witness relations -/
 
 /-- A witness relation for `L` [PS10, Appendix B, Definition 191.11] (Def-191.11): `x ∈ L` iff
@@ -180,7 +242,11 @@ decidable in polynomial time on the pair `⟨x, y⟩`.
 
 **Deviation:** the text's `R_L(x) = {y : (x, y) ∈ L}` is a typo for `∈ R_L`; the witness-length
 bound is an explicit `PolyExpr` and the decider a polynomial-time string function
-(`PolyTimeComputable`). -/
+(`PolyTimeComputable`). The bound is on the relation itself (every `y` with `R x y` is short),
+whereas Definition 191.11 bounds only the witnesses that count (`∃ y, |y| ≤ p(|x|) ∧
+(x, y) ∈ R_L`); the two agree on languages (intersect `R_L` with the bound), and the bounded
+form suits Definition 119.5's "for every `y ∈ R_L(x)`", since a time-`t(|x|)` prover cannot
+read a longer `y` (gate 03e, note 11). -/
 structure WitnessRelation (L : Language Bool) (R : List Bool → List Bool → Prop) : Prop where
   /-- `x ∈ L` iff `x` has a witness. -/
   mem_iff : ∀ x, x ∈ L ↔ ∃ y, R x y
@@ -263,23 +329,36 @@ theorem exists_witnessRelation_of_mem_NP {L : Language Bool} (h : L ∈ NP) :
 /-! ### Efficient provers -/
 
 /-- An interactive proof for `L` with efficient prover with respect to the witness relation
-`R` [PS10, Definition 119.5] (Def-119.5): an interactive proof whose prover is a PPT strategy
-(the witness is its auxiliary input) and which is complete for **every** witness `y` of `x`
-(Definition 116.1 only asks for some auxiliary input). -/
+`R` [PS10, Definition 119.5] (Def-119.5): an interactive proof whose prover is efficient (the
+witness is its auxiliary input) and which is complete for **every** witness `y` of `x`
+(Definition 116.1 only asks for some auxiliary input).
+
+**Deviation (D8; ruling G3-3 of gate 03):** the text's "P is p.p.t." is `Strategy.Efficient`
+(time polynomial in the total input length, D8) together with a polynomial bound `B(|x|)` on
+the prover's messages on every instance with a witness (`Protocol.ProverBounded`: the text's
+p.p.t. machine writes at most `t(|x|)` bits per message, the convention of ch. 6); the
+verifier is as in `InteractiveProof`. -/
 structure EfficientProverProof (π : Protocol) (L : Language Bool)
     (R : List Bool → List Bool → Prop) : Prop extends InteractiveProof π L where
-  /-- The prover is a PPT strategy. -/
+  /-- The prover is efficient (`Strategy.Efficient`, D8). -/
   efficientP : π.P.Efficient
+  /-- The prover's messages have at most `B(|x|)` bits on instances with a witness. -/
+  boundedP : ∃ B : PolyExpr, π.ProverBounded R B
   /-- Completeness for every witness. -/
   completeWitness : ∀ x y, R x y → ∀ z : List Bool,
     uprob (fun r : π.ExecCoins π.P x => π.outV π.P x y z r = [true]) = 1
 
 /-- An interactive proof with soundness error `s` and efficient prover with respect to `R`
-[PS10, Definition 119.5 with the soundness error of §4.5] (Def-119.5, Def-117.a). -/
+[PS10, Definition 119.5 with the soundness error of §4.5] (Def-119.5, Def-117.a).
+
+**Deviation (D8; ruling G3-3 of gate 03):** as for `EfficientProverProof` (`Efficient` prover
+with messages of at most `B(|x|)` bits on instances with a witness). -/
 structure EfficientProverProofErr (π : Protocol) (L : Language Bool)
     (R : List Bool → List Bool → Prop) (s : ℕ → ℝ) : Prop extends InteractiveProofErr π L s where
-  /-- The prover is a PPT strategy. -/
+  /-- The prover is efficient (`Strategy.Efficient`, D8). -/
   efficientP : π.P.Efficient
+  /-- The prover's messages have at most `B(|x|)` bits on instances with a witness. -/
+  boundedP : ∃ B : PolyExpr, π.ProverBounded R B
   /-- Completeness for every witness. -/
   completeWitness : ∀ x y, R x y → ∀ z : List Bool,
     uprob (fun r : π.ExecCoins π.P x => π.outV π.P x y z r = [true]) = 1
@@ -290,6 +369,7 @@ theorem EfficientProverProofErr.efficientProverProof {π : Protocol} {L : Langua
     (h : EfficientProverProofErr π L R s) : EfficientProverProof π L R where
   toInteractiveProof := h.toInteractiveProofErr.interactiveProof hs
   efficientP := h.efficientP
+  boundedP := h.boundedP
   completeWitness := h.completeWitness
 
 /-- An interactive proof with efficient prover has a negligible soundness error. -/
@@ -297,7 +377,7 @@ theorem EfficientProverProof.exists_err {π : Protocol} {L : Language Bool}
     {R : List Bool → List Bool → Prop} (h : EfficientProverProof π L R) :
     ∃ ε : ℕ → ℝ, Negligible ε ∧ EfficientProverProofErr π L R ε := by
   obtain ⟨ε, hε, herr⟩ := h.toInteractiveProof.exists_err
-  exact ⟨ε, hε, herr, h.efficientP, h.completeWitness⟩
+  exact ⟨ε, hε, herr, h.efficientP, h.boundedP, h.completeWitness⟩
 
 /-! ### The trivial NP protocol -/
 
@@ -381,6 +461,13 @@ theorem npProtocol_efficientP (T : List Bool → Bool) (p : PolyExpr) :
     fun x z r hist => ?_⟩
   simp [npProtocol, Strategy.ofNUPPT_next, NUPPT.runAtL_ofPolyTimeUniform, NUPPT.advInput]
 
+/-- The prover of `npProtocol T p` sends its auxiliary input, so on witnesses of length at most
+`p(|x|)` its message has at most `p(|x|)` bits (ruling G3-3 of gate 03). -/
+theorem npProtocol_proverBounded (T : List Bool → Bool) (p : PolyExpr)
+    {R : List Bool → List Bool → Prop} (hp : ∀ x y, R x y → y.length ≤ p.eval x.length) :
+    (npProtocol T p).ProverBounded R p :=
+  fun x y _ _ hxy => hp x y hxy
+
 /-- Non-vacuity of Definitions 116.1 and 119.5 [PS10, §4.5, "`NP ⊆ IP`"]: for a witness relation
 `R` of `L` decided by the polynomial-time predicate `T`, with witnesses of length at most
 `p(|x|)`, the one-message protocol in which the prover sends a witness is an interactive proof
@@ -392,9 +479,11 @@ probability one).
 
 **Proof sketch.** The verifier's output is `[T ⟨x, m.take (p(|x|))⟩]` for the message `m` sent
 (`npProtocol_outV`); the honest prover sends `y`, which the truncation leaves unchanged since
-`|y| ≤ p(|x|)` (`hp`, `List.take_of_length_le`). Completeness: for `x ∈ L` take a witness `y`
-(`hR.mem_iff`); then `T ⟨x, y⟩ = true` (`hTR`) on every coin pair, so the probability is one
-(`HardcoreBit.uprob_eq_one_of_forall`). Soundness with `ε n := 2⁻¹ ^ n`
+`|y| ≤ p(|x|)` (`hp`, `List.take_of_length_le`). Completeness for every witness `y`:
+`T ⟨x, y⟩ = true` (`hTR`) on every coin pair, so the probability is one
+(`HardcoreBit.uprob_eq_one_of_forall`); the prover's message `y` has at most `p(|x|)` bits
+(`npProtocol_proverBounded`), and completeness follows for `x ∈ L` with a witness from
+`hR.mem_iff` (`Protocol.ProverBounded.exists_complete`). Soundness with `ε n := 2⁻¹ ^ n`
 (`negligible_two_pow_neg`; the literal clause is strict, so `ε = 0` is not admissible): for
 `x ∉ L` no string — in particular no truncated message — is a witness, so `T ⟨x, ·⟩ = false`
 and the verifier outputs `[false]` on every coin pair, with probability `1 > 1 - ε(|x|)`.
@@ -404,35 +493,36 @@ theorem npProtocol_interactiveProof {L : Language Bool} {R : List Bool → List
     (hT : PolyTimeComputable fun z => [T z])
     (hTR : ∀ x y, T (pairEncode x y) = true ↔ R x y)
     (hp : ∀ x y, R x y → y.length ≤ p.eval x.length) :
-    EfficientProverProof (npProtocol T p) L R where
-  efficientV := npProtocol_efficientV T p hT
-  complete := by
-    intro x hx
-    obtain ⟨y, hy⟩ := (hR.mem_iff x).1 hx
-    refine ⟨y, fun z => HardcoreBit.uprob_eq_one_of_forall fun r => ?_⟩
-    rw [npProtocol_outV]
-    simp [npProtocol, List.take_of_length_le (hp x y hy), (hTR x y).2 hy]
-  sound := by
-    refine ⟨fun n => (2 : ℝ)⁻¹ ^ n, negligible_two_pow_neg, fun x hx P' z => ?_⟩
-    have hall : ∀ r : (npProtocol T p).ExecCoins P' x,
-        (npProtocol T p).outV P' x [] z r = [false] := by
-      intro r
-      rw [npProtocol_outV]
-      have hno : ¬ R x ((P'.next x [] (List.ofFn r.1) []).take (p.eval x.length)) :=
-        fun hw => hx ((hR.mem_iff x).2 ⟨_, hw⟩)
-      have hfalse :
-          T (pairEncode x ((P'.next x [] (List.ofFn r.1) []).take (p.eval x.length))) = false := by
-        rw [← Bool.not_eq_true, hTR]
-        exact hno
-      rw [hfalse]
-    rw [HardcoreBit.uprob_eq_one_of_forall hall]
-    exact sub_lt_self _ (by positivity)
-  efficientP := npProtocol_efficientP T p
-  completeWitness := by
+    EfficientProverProof (npProtocol T p) L R := by
+  have hcw : ∀ x y, R x y → ∀ z : List Bool,
+      uprob (fun r : (npProtocol T p).ExecCoins (npProtocol T p).P x =>
+        (npProtocol T p).outV (npProtocol T p).P x y z r = [true]) = 1 := by
     intro x y hy z
     refine HardcoreBit.uprob_eq_one_of_forall fun r => ?_
     rw [npProtocol_outV]
     simp [npProtocol, List.take_of_length_le (hp x y hy), (hTR x y).2 hy]
+  refine
+    { efficientV := npProtocol_efficientV T p hT
+      complete := (npProtocol_proverBounded T p hp).exists_complete
+        (fun x hx => (hR.mem_iff x).1 hx) hcw
+      sound := ?_
+      efficientP := npProtocol_efficientP T p
+      boundedP := ⟨p, npProtocol_proverBounded T p hp⟩
+      completeWitness := hcw }
+  refine ⟨fun n => (2 : ℝ)⁻¹ ^ n, negligible_two_pow_neg, fun x hx P' z => ?_⟩
+  have hall : ∀ r : (npProtocol T p).ExecCoins P' x,
+      (npProtocol T p).outV P' x [] z r = [false] := by
+    intro r
+    rw [npProtocol_outV]
+    have hno : ¬ R x ((P'.next x [] (List.ofFn r.1) []).take (p.eval x.length)) :=
+      fun hw => hx ((hR.mem_iff x).2 ⟨_, hw⟩)
+    have hfalse :
+        T (pairEncode x ((P'.next x [] (List.ofFn r.1) []).take (p.eval x.length))) = false := by
+      rw [← Bool.not_eq_true, hTR]
+      exact hno
+    rw [hfalse]
+  rw [HardcoreBit.uprob_eq_one_of_forall hall]
+  exact sub_lt_self _ (by positivity)
 
 /-- Every language with a witness relation is in `IP` [PS10, §4.5, "`NP ⊆ IP`"] (Claim-117.c):
 the one-message protocol `npProtocol T p`, with the relation's decider `T` and witness-length
diff --git a/TCSlib/Cryptography/ZeroKnowledge/NP.lean b/TCSlib/Cryptography/ZeroKnowledge/NP.lean
index eab0b408..8ad8b9c0 100644
--- a/TCSlib/Cryptography/ZeroKnowledge/NP.lean
+++ b/TCSlib/Cryptography/ZeroKnowledge/NP.lean
@@ -32,9 +32,11 @@ deferred).
 
 **Deviations:**
 * a Levin reduction is taken *length-regular* with `|f x| = p(|x|)` for a `PolyExpr p ≥ id`
-  (every Levin reduction to `3COL` can be padded to this form by adding isolated vertices),
-  which makes the coin and round polynomials of the pulled-back protocol `subst p` of the
-  original ones and the error bounds `ε(p(|x|))`, negligible in `|x|` (`Negligible.comp_of_le`);
+  (assumed: padding a Levin reduction to `3COL` with isolated vertices should give this form
+  with `p = q²` for a polynomial `q`, the lengths of `encGraph` being perfect squares, but the
+  padding is not formalized; gate 03e, note 14), which makes the coin and round polynomials
+  of the pulled-back protocol `subst p` of the original ones and the error bounds
+  `ε(p(|x|))`, negligible in `|x|` (`Negligible.comp_of_le`);
 * the text's "execute protocol `(P, V)` on `x'`" is read as `(P', V')`; the hypothesis of a
   hard-core predicate for the one-way permutation is made explicit (as in Theorem 126.4).
 
@@ -47,6 +49,22 @@ the machines `exists_liftSimulator`/`exists_liftDistinguisher`, and the strict m
 a length polynomial `p ≥ id` (`polyExpr_strictMono_of_le`, which gives the left inverse of
 `p.eval` along which the distinguisher is re-parametrized).
 
+**Bounded prover messages (ruling G3-3 of gate 03):** the bound on the honest prover's
+messages transfers along a Levin reduction with bound `B.subst p`
+(`Protocol.ProverBounded.pullback`).
+
+**Scope of Theorem 124.1 (DQ5; gate 03e, minor 3).** The text's Theorem 124.1 asserts one
+zero-knowledge proof with negligible soundness error. Here the zero-knowledge protocol is one
+iteration of the 3-colouring protocol, with soundness error `1 - 1/p(|x|) + 2^{-p(|x|)}`, and
+the interactive proof with negligible error is its `n|E|`-fold repetition; that the repetition
+is also zero-knowledge, with negligible soundness error, is sequential repetition
+[PS10, §7.2.1], which ch. 7 supplies (ruling G3-7(d)), and is not stated here. In the
+existential forms the conjunct `∃ π, EfficientProverProof π L R` says nothing about the
+zero-knowledge protocol (`npProtocol` already witnesses it, `npProtocol_interactiveProof`);
+the tied forms `exists_commitment_zk_proof_of_owp_levinReduction`,
+`zk_proof_of_witnessRelation` and `zk_proof_of_witnessRelation_of_owp` state both protocols for
+one commitment scheme and one Levin reduction, as `zk_proof_of_levinReduction` does.
+
 **Run-3 repairs (audit P11-1, P11-2):** the transfer lemmas and both forms of Theorem 124.1
 take the hypothesis `hLR : ∀ x ∈ L, ∃ y, R x y` (`L ⊆ witnessLanguage R`): no field of
 `LevinReduction` relates `L` to `R` (with `R = ∅` the `witness` field is vacuous), and without
@@ -71,14 +89,22 @@ length polynomial `p ≥ id` (the run-2 `∃ s, EfficientProverProofErr π L R s
 * `TCSlib.Cryptography.LevinReduction.efficientProverProof`,
   `TCSlib.Cryptography.LevinReduction.efficientProverProofErr`,
   `TCSlib.Cryptography.LevinReduction.zk` — interactive proofs with efficient prover and
-  zero-knowledge transfer along Levin reductions (Claim-124.d).
+  zero-knowledge transfer along Levin reductions (Claim-124.d);
+  `TCSlib.Cryptography.Protocol.ProverBounded.pullback` — so does the bound on the prover's
+  messages.
 * `TCSlib.Cryptography.zk_proof_of_levinReduction` — **[PS10, Theorem 124.1], form (A)**:
-  a commitment scheme and a Levin reduction to `3COL` give a zero-knowledge proof for `L`;
-  `TCSlib.Cryptography.zk_proof_of_owp_levinReduction` — the same from a one-way permutation
-  with a hard-core predicate (Thm-124.1).
-* `TCSlib.Cryptography.zk_proof_of_mem_NP`, `TCSlib.Cryptography.zk_proof_of_mem_NP_of_owp` —
-  the "every language in NP" form under `LevinNPHard L3COL R3COL`, with the explicit soundness
-  error of the Levin reduction's length polynomial
+  a commitment scheme and a Levin reduction to `3COL` give a zero-knowledge protocol for `L`
+  with soundness error `1 - 1/p(|x|) + 2^{-p(|x|)}` whose `n|E|`-fold repetition is an
+  interactive proof; `TCSlib.Cryptography.zk_proof_of_owp_levinReduction`,
+  `TCSlib.Cryptography.exists_commitment_zk_proof_of_owp_levinReduction` — the same from a
+  one-way permutation with a hard-core predicate, untied and tied (Thm-124.1).
+* `TCSlib.Cryptography.zk_proof_of_witnessRelation`,
+  `TCSlib.Cryptography.zk_proof_of_witnessRelation_of_owp` — the "every language in NP" form
+  for every witness relation, under `LevinNPHard L3COL R3COL` (the second from a one-way
+  permutation, the text's hypothesis); `TCSlib.Cryptography.zk_proof_of_mem_NP`,
+  `TCSlib.Cryptography.zk_proof_of_mem_NP_of_owp` — the corollaries for `L ∈ NP` with the
+  witness relation of `exists_witnessRelation_of_mem_NP`, with the explicit soundness error of
+  the Levin reduction's length polynomial
   (`TCSlib.Cryptography.one_sub_inv_add_half_pow_lt_one`: the error is below `1`).
 
 ## References
@@ -86,7 +112,7 @@ length polynomial `p ≥ id` (the run-2 `∃ s, EfficientProverProofErr π L R s
 * [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
   (§4.7: Theorem 124.1; Appendix B, Definition 191.11.)
 * [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge
-  University Press, 2009. (Definition 2.7, Karp reductions; §2.3.3, Levin reductions.)
+  University Press, 2009. (Definition 2.7, Karp reductions; §2.3, Levin reductions.)
 -/
 
 namespace TCSlib.Cryptography
@@ -102,8 +128,9 @@ polynomial-time Karp reduction (`x ∈ L ↔ f x ∈ L'`), `w` is polynomial-tim
 length-regular: `|f x| = p(|x|)` for the polynomial `p ≥ id`.
 
 **Deviation:** the text never defines Levin reductions; length-regularity with `p ≥ id` is
-assumed (achievable by padding) so that the pulled-back protocol's polynomials are `subst p`
-of the original ones and its error bounds `ε(p(|x|))` are negligible in `|x|`. -/
+assumed (padding with isolated vertices should achieve it for `3COL`, with `p = q²`; not
+formalized) so that the pulled-back protocol's polynomials are `subst p` of the original ones
+and its error bounds `ε(p(|x|))` are negligible in `|x|`. -/
 structure LevinReduction (L L' : Language Bool) (R R' : List Bool → List Bool → Prop)
     (f : List Bool → List Bool) (w : List Bool → List Bool → List Bool) (p : PolyExpr) : Prop where
   /-- The instance map is polynomial-time. -/
@@ -239,6 +266,19 @@ theorem Strategy.pullback_efficient {S : Strategy} (hS : S.Efficient) {f : List
     rw [hnext, Strategy.ofNUPPT_next, ← hx x]
     simp only [id, pairFstD_pairEncode, pairSndD_pairEncode]
 
+/-- **Bounded prover messages transfer along a Levin reduction** with bound `B.subst p`
+(ruling G3-3 of gate 03): the pulled-back prover runs `π.P` on `(f x, w x y)`, `R x y` gives
+`R' (f x) (w x y)` (`LevinReduction.witness`), and `|f x| = p(|x|)`
+(`LevinReduction.length_eq`, `PolyExpr.eval_subst`). -/
+theorem Protocol.ProverBounded.pullback {L L' : Language Bool}
+    {R R' : List Bool → List Bool → Prop} {f : List Bool → List Bool}
+    {w : List Bool → List Bool → List Bool} {p : PolyExpr} (h : LevinReduction L L' R R' f w p)
+    {π : Protocol} {B : PolyExpr} (hB : π.ProverBounded R' B) :
+    (π.pullback f w p).ProverBounded R (B.subst p) := by
+  intro x y r hist hxy
+  rw [PolyExpr.eval_subst, ← h.length_eq x]
+  exact hB (f x) (w x y) r hist (h.witness x y hxy)
+
 /-! ### Negligibility along polynomial reparametrization -/
 
 /-- A negligible function composed with a map `φ ≥ id` is negligible: for `N ≥ max n₀ 1`,
@@ -354,11 +394,14 @@ execution of the pulled-back protocol on `(x, y, z)` with coins `r` is the execu
 functions are those of `π` on `(f x, w x y)` and `(f x, z)` by definition — with the move
 count `π.rounds.eval (p |x|) = π.rounds.eval |f x|` by `h.length_eq`); the cast is a uniform
 projection (`LevinTransfer.unifProj_coinTrunc`, `UnifProj.uprob_comp`), so
-`hπ.completeWitness` gives probability one. Completeness:
-`complete x hx := let ⟨y, hy⟩ := hLR x hx; ⟨y, completeWitness x y hy⟩`. Soundness: for
-`x ∉ L`, `f x ∉ L'` (`h.mem_iff`); a prover `P'` for the pulled-back protocol on `x` is the
-prover `P* := ⟨fun _ _ r hist => P'.next x [] r hist, .const (P'.coinLen |x|)⟩` for `π` on
-`f x` with the same coins (`outV_pullback_cheat`, `P*.coinLen |f x| = P'.coinLen |x|`), and
+`hπ.completeWitness` gives probability one. Bounded prover messages:
+`Protocol.ProverBounded.pullback` with the bound `B.subst p` of `hπ.boundedP`. Completeness:
+for `x ∈ L` take `y` with `R x y` (`hLR`); the honest messages have at most `B(p(|x|))` bits
+and the verifier accepts with probability one (`Protocol.ProverBounded.exists_complete`).
+Soundness: for `x ∉ L`, `f x ∉ L'` (`h.mem_iff`); a prover `P'` for the pulled-back protocol
+on `x` is the prover `P* := ⟨fun _ _ r hist => P'.next x [] r hist, .const (P'.coinLen |x|)⟩`
+for `π` on `f x` with the same coins (`outV_pullback_cheat`,
+`P*.coinLen |f x| = P'.coinLen |x|`), and
 `hπ.sound (f x) _ P* z` gives `1 - s |f x| ≤ Pr[out = [false]]`, i.e. `1 - s (p |x|)` by
 `h.length_eq`. -/
 theorem LevinReduction.efficientProverProofErr {L L' : Language Bool}
@@ -380,11 +423,11 @@ theorem LevinReduction.efficientProverProofErr {L L' : Language Bool}
     congr 1
     funext r
     rw [outV_pullback_honest π f w hx]
+  obtain ⟨B, hB⟩ := hπ.boundedP
   refine ⟨⟨Strategy.pullback_efficient hπ.efficientV h.f_poly polyTimeComputable_pairSndD
-    h.length_eq, fun x hx => ?_, fun x hx P' z => ?_⟩,
-    Strategy.pullback_efficient hπ.efficientP h.f_poly h.w_poly h.length_eq, hcompl⟩
-  · obtain ⟨y, hy⟩ := hLR x hx
-    exact ⟨y, hcompl x y hy⟩
+    h.length_eq, (hB.pullback h).exists_complete hLR hcompl, fun x hx P' z => ?_⟩,
+    Strategy.pullback_efficient hπ.efficientP h.f_poly h.w_poly h.length_eq,
+    ⟨B.subst p, hB.pullback h⟩, hcompl⟩
   · have hlen := h.length_eq x
     have hfx : f x ∉ L' := fun hfx => hx ((h.mem_iff x).2 hfx)
     have hU : UnifProj (Prod.map (coinTrunc le_rfl)
@@ -518,8 +561,10 @@ theorem LevinReduction.zk {L L' : Language Bool} {R R' : List Bool → List Bool
 /-! ### Theorem 124.1 -/
 
 /-- **[PS10, Theorem 124.1], form (A): a commitment scheme and a Levin reduction to `3COL`
-give a zero-knowledge proof for `L`** (Thm-124.1): for a commitment scheme `(Com, ℓ)` and a
-Levin reduction `(f, w)` of `(L, R)` to `(3COL, R_3COL)` with `L ⊆ witnessLanguage R` (`hLR`),
+give a zero-knowledge protocol for `L` with soundness error `1 - 1/p(|x|) + 2^{-p(|x|)}` whose
+`n|E|`-fold repetition is an interactive proof** (Thm-124.1): for a commitment scheme
+`(Com, ℓ)` and a Levin reduction `(f, w)` of `(L, R)` to `(3COL, R_3COL)` with
+`L ⊆ witnessLanguage R` (`hLR`),
 the pulled-back `n|E|`-fold 3-colouring protocol is an interactive proof for `L` with
 efficient prover w.r.t. `R`, and the pulled-back one-iteration protocol is zero-knowledge for
 `R` and an interactive proof with efficient prover and soundness error
@@ -527,8 +572,9 @@ efficient prover w.r.t. `R`, and the pulled-back one-iteration protocol is zero-
 
 **Deviation (DQ5):** the proof and the zero-knowledge statements are for the repeated and
 the single-iteration protocols respectively (sequential composition, [PS10, §7.2.1], is out
-of scope); the reduction is an explicit hypothesis (the text's "Cook's reduction applied to
-the witness" is a Levin reduction, never defined there).
+of scope; the text's single zero-knowledge proof with negligible soundness error is debt that
+ch. 7 discharges, ruling G3-7(d)); the reduction is an explicit hypothesis (the text's
+"Cook's reduction applied to the witness" is a Levin reduction, never defined there).
 
 **Repair (run-3 audit P11-1):** hypothesis `hLR : ∀ x ∈ L, ∃ y, R x y` added — the first and
 third conjuncts are instances of `LevinReduction.efficientProverProofErr`, and without it
@@ -547,15 +593,19 @@ theorem zk_proof_of_levinReduction {Com : List Bool → List Bool} {ℓ : PolyEx
     h.efficientProverProofErr hLR (col_efficientProverProofErr hC)⟩
 
 /-- **[PS10, Theorem 124.1]: if one-way permutations (with a hard-core predicate) exist, every
-language with a Levin reduction to `3COL` has a zero-knowledge proof** (Thm-124.1, headline):
-for `L ⊆ witnessLanguage R` (`hLR`) there is a protocol that is an interactive proof for `L`
-with efficient prover w.r.t. `R`, and a protocol that is zero-knowledge for `R` and an
-interactive proof with efficient prover and soundness error `1 - 1/p(|x|) + (1/2)^{p(|x|)}` —
-the commitment scheme of [PS10, Theorem 126.4] (`exists_commitment_of_owp_hardCore`) plugged
-into `zk_proof_of_levinReduction`.
+language with a Levin reduction to `3COL` has a zero-knowledge protocol with soundness error
+`1 - 1/p(|x|) + 2^{-p(|x|)}`** (Thm-124.1, untied existential form): for `L ⊆ witnessLanguage R`
+(`hLR`) there is a protocol that is an interactive proof for `L` with efficient prover w.r.t.
+`R`, and a protocol that is zero-knowledge for `R` and an interactive proof with efficient
+prover and soundness error `1 - 1/p(|x|) + (1/2)^{p(|x|)}` — the commitment scheme of
+[PS10, Theorem 126.4] (`exists_commitment_of_owp_hardCore`) plugged into
+`zk_proof_of_levinReduction`.
 
 **Deviation:** hard-core predicate explicit (source error 47); single OWP rather than a
-collection; see `zk_proof_of_levinReduction` for the two-protocol form (DQ5).
+collection; see `zk_proof_of_levinReduction` for the two-protocol form (DQ5). The first
+conjunct alone says nothing about the zero-knowledge protocol (gate 03e, minor 3:
+`npProtocol` pulled back along `(f, w)` already witnesses it); the tied form, both protocols
+from one commitment scheme, is `exists_commitment_zk_proof_of_owp_levinReduction`.
 
 **Repair (run-3 audit P11-1):** hypothesis `hLR : ∀ x ∈ L, ∃ y, R x y` added (see
 `zk_proof_of_levinReduction`). -/
@@ -572,6 +622,28 @@ theorem zk_proof_of_owp_levinReduction
   obtain ⟨h1, h2, h3⟩ := zk_proof_of_levinReduction hC h hLR
   exact ⟨⟨_, h1⟩, _, h2, h3⟩
 
+/-- **[PS10, Theorem 124.1], tied form: if one-way permutations exist, every language with a
+Levin reduction to `3COL` has a zero-knowledge protocol with soundness error
+`1 - 1/p(|x|) + 2^{-p(|x|)}` whose `n|E|`-fold repetition is an interactive proof**
+(Thm-124.1; gate 03e, minor 3): from the text's hypothesis, a single one-way permutation, there
+is a commitment scheme `(Com, ℓ)` (`exists_commitment_of_owp`, [PS10, Theorem 126.4] with the
+hard-core predicate of Goldreich–Levin) for which the conclusion of
+`zk_proof_of_levinReduction` holds: both protocols are built from `Com` and the reduction.
+
+**Deviation (DQ5):** as for `zk_proof_of_levinReduction`. -/
+theorem exists_commitment_zk_proof_of_owp_levinReduction
+    (how : ∃ P : PermFamily, OneWayPermutation P)
+    {L : Language Bool} {R : List Bool → List Bool → Prop} {f : List Bool → List Bool}
+    {w : List Bool → List Bool → List Bool} {p : PolyExpr}
+    (h : LevinReduction L L3COL R R3COL f w p) (hLR : ∀ x ∈ L, ∃ y, R x y) :
+    ∃ (Com : List Bool → List Bool) (ℓ : PolyExpr), Commitment Com ℓ ∧
+      EfficientProverProof ((colProtocolRep Com ℓ).pullback f w p) L R ∧
+      ZK ((colProtocol Com ℓ).pullback f w p) R ∧
+      EfficientProverProofErr ((colProtocol Com ℓ).pullback f w p) L R
+        (fun N => 1 - 1 / (p.eval N : ℝ) + (1 / 2 : ℝ) ^ p.eval N) := by
+  obtain ⟨Com, ℓ, hC⟩ := exists_commitment_of_owp how
+  exact ⟨Com, ℓ, hC, zk_proof_of_levinReduction hC h hLR⟩
+
 /-- Sanity (run-3 audit P11-2): the soundness error `1 - 1/k + (1/2)^k` of the one-iteration
 protocols is strictly below `1` for `k ≥ 1`, since `k < 2^k` (`Nat.lt_two_pow_self`). Hence
 `EfficientProverProofErr π L R (fun N => 1 - 1/(p N) + (1/2)^{p N})` with `p N ≥ N ≥ 1`
@@ -595,13 +667,59 @@ def LevinNPHard (L' : Language Bool) (R' : List Bool → List Bool → Prop) : P
     ∃ (f : List Bool → List Bool) (w : List Bool → List Bool → List Bool) (p : PolyExpr),
       LevinReduction L L' R R' f w p
 
-/-- **[PS10, Theorem 124.1], "every language in NP"**, under NP-hardness of `3COL` with Levin
-reductions: for a commitment scheme and every `L ∈ NP` there is a witness relation `R` for
+/-- **[PS10, Theorem 124.1], "every language in NP", for every witness relation** (Thm-124.1;
+gate 03e, minors 3 and 4): under NP-hardness of `3COL` with Levin reductions, for a commitment
+scheme `(Com, ℓ)` and every witness relation `R` of `L` there is a Levin reduction `(f, w)` of
+`(L, R)` to `(3COL, R_3COL)` with length polynomial `p ≥ id` for which the pulled-back
+one-iteration 3-colouring protocol is zero-knowledge for `R` with soundness error
+`1 - 1/p(|x|) + 2^{-p(|x|)}`, and its `n|E|`-fold repetition is an interactive proof with
+efficient prover (`zk_proof_of_levinReduction`, with `hLR` from `WitnessRelation.mem_iff`).
+
+**Deviation (DQ5):** as for `zk_proof_of_levinReduction`. -/
+theorem zk_proof_of_witnessRelation (h3 : LevinNPHard L3COL R3COL)
+    {Com : List Bool → List Bool} {ℓ : PolyExpr} (hC : Commitment Com ℓ) {L : Language Bool}
+    {R : List Bool → List Bool → Prop} (hR : WitnessRelation L R) :
+    ∃ (f : List Bool → List Bool) (w : List Bool → List Bool → List Bool) (p : PolyExpr),
+      (∀ N, N ≤ p.eval N) ∧
+      EfficientProverProof ((colProtocolRep Com ℓ).pullback f w p) L R ∧
+      ZK ((colProtocol Com ℓ).pullback f w p) R ∧
+      EfficientProverProofErr ((colProtocol Com ℓ).pullback f w p) L R
+        (fun N => 1 - 1 / (p.eval N : ℝ) + (1 / 2 : ℝ) ^ p.eval N) := by
+  obtain ⟨f, w, p, h⟩ := h3 L R hR
+  exact ⟨f, w, p, h.le_eval, zk_proof_of_levinReduction hC h fun x hx => (hR.mem_iff x).1 hx⟩
+
+/-- **[PS10, Theorem 124.1], "if one-way permutations exist then every language in NP has a
+zero-knowledge proof", for every witness relation** (Thm-124.1; gate 03e, minors 3 and 4):
+from the text's hypothesis, a one-way permutation, there is a commitment scheme
+(`exists_commitment_of_owp`) for which the conclusion of `zk_proof_of_witnessRelation` holds,
+under NP-hardness of `3COL` with Levin reductions.
+
+**Deviation (DQ5):** as for `zk_proof_of_levinReduction`. -/
+theorem zk_proof_of_witnessRelation_of_owp (h3 : LevinNPHard L3COL R3COL)
+    (how : ∃ P : PermFamily, OneWayPermutation P) {L : Language Bool}
+    {R : List Bool → List Bool → Prop} (hR : WitnessRelation L R) :
+    ∃ (Com : List Bool → List Bool) (ℓ : PolyExpr), Commitment Com ℓ ∧
+      ∃ (f : List Bool → List Bool) (w : List Bool → List Bool → List Bool) (p : PolyExpr),
+        (∀ N, N ≤ p.eval N) ∧
+        EfficientProverProof ((colProtocolRep Com ℓ).pullback f w p) L R ∧
+        ZK ((colProtocol Com ℓ).pullback f w p) R ∧
+        EfficientProverProofErr ((colProtocol Com ℓ).pullback f w p) L R
+          (fun N => 1 - 1 / (p.eval N : ℝ) + (1 / 2 : ℝ) ^ p.eval N) := by
+  obtain ⟨Com, ℓ, hC⟩ := exists_commitment_of_owp how
+  exact ⟨Com, ℓ, hC, zk_proof_of_witnessRelation h3 hC hR⟩
+
+/-- **[PS10, Theorem 124.1], "every language in NP", one-iteration form: a zero-knowledge
+protocol with soundness error `1 - 1/p(|x|) + 2^{-p(|x|)}`**, under NP-hardness of `3COL` with
+Levin reductions: for a commitment scheme and every `L ∈ NP` there is a witness relation `R` for
 `L` with an interactive proof with efficient prover, and a protocol that is zero-knowledge
 for `R` and an interactive proof with efficient prover and soundness error
 `1 - 1/p(|x|) + (1/2)^{p(|x|)}`, where `p ≥ id` is the length polynomial of the Levin
 reduction (the two protocols of `zk_proof_of_levinReduction`; the witness relation from
-`exists_witnessRelation_of_mem_NP`, [PS10, Definition 191.11], supplies `hLR`).
+`exists_witnessRelation_of_mem_NP`, [PS10, Definition 191.11], supplies `hLR`). This is the
+corollary of `zk_proof_of_witnessRelation`, which holds for every witness relation (gate 03e,
+minor 4) and ties the two protocols together; here the conjunct
+`∃ π, EfficientProverProof π L R` alone says nothing about the zero-knowledge protocol
+(`npProtocol` witnesses it, minor 3).
 
 **Repair (run-3 audit P11-2):** the run-2 conclusion `∃ s, EfficientProverProofErr π L R s`
 asserted no soundness (`s := 1` turns the clause into `0 ≤ uprob …`, so it followed from the
@@ -616,18 +734,20 @@ theorem zk_proof_of_mem_NP (h3 : LevinNPHard L3COL R3COL) {Com : List Bool → L
         EfficientProverProofErr π L R
           (fun N => 1 - 1 / (p.eval N : ℝ) + (1 / 2 : ℝ) ^ p.eval N) := by
   obtain ⟨R, hR⟩ := exists_witnessRelation_of_mem_NP hL
-  obtain ⟨f, w, p, h⟩ := h3 L R hR
-  obtain ⟨h1, h2, h3'⟩ := zk_proof_of_levinReduction hC h fun x hx => (hR.mem_iff x).1 hx
-  exact ⟨R, hR, ⟨_, h1⟩, _, p, h.le_eval, h2, h3'⟩
+  obtain ⟨_, _, p, hp, h1, h2, h3'⟩ := zk_proof_of_witnessRelation h3 hC hR
+  exact ⟨R, hR, ⟨_, h1⟩, _, p, hp, h2, h3'⟩
 
 /-- **[PS10, Theorem 124.1], "if one-way permutations exist then every language in NP has a
-zero-knowledge proof"**, under NP-hardness of `3COL` with Levin reductions and with the
+zero-knowledge proof", one-iteration form: a zero-knowledge protocol with soundness error
+`1 - 1/p(|x|) + 2^{-p(|x|)}`**, under NP-hardness of `3COL` with Levin reductions and with the
 hard-core predicate explicit (`exists_commitment_of_owp_hardCore`, `zk_proof_of_mem_NP`):
 the zero-knowledge protocol has the explicit soundness error `1 - 1/p(|x|) + (1/2)^{p(|x|)}`
 of the Levin reduction's length polynomial `p ≥ id`.
 
 **Repair (run-3 audit P11-2):** explicit soundness error instead of the vacuous
-`∃ s, EfficientProverProofErr π L R s` (see `zk_proof_of_mem_NP`). -/
+`∃ s, EfficientProverProofErr π L R s` (see `zk_proof_of_mem_NP`). The form for every witness
+relation, from the text's hypothesis (a one-way permutation) and with the two protocols tied,
+is `zk_proof_of_witnessRelation_of_owp` (gate 03e, minors 3 and 4). -/
 theorem zk_proof_of_mem_NP_of_owp (h3 : LevinNPHard L3COL R3COL)
     (how : ∃ (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool),
       OneWayPermutation P ∧ HardCore P.toFunFamily h)

### --- B: the 03e repair commit 30f90d36ab23d8f6b9ac99e4608c38174f3bfcb1 (on a3c5fa8b72e50939822f22364647dc844a3914a0; in #199), outside this pack's files ---
diff --git a/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean b/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean
index ea63a690..9869c680 100644
--- a/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean
+++ b/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean
@@ -127,7 +127,9 @@ malformed `x ∉ L` could decode to a pair of isomorphic graphs and soundness wo
   `TCSlib.Cryptography.uprob_gi_rep_cheat_le` (Lem-120.d, proved from Lem-119.c).
 * `TCSlib.Cryptography.gni_interactiveProofErr`, `TCSlib.Cryptography.gni_interactiveProof`
   — [PS10, Proposition 118.4]; `TCSlib.Cryptography.gi_efficientProverProofErr`,
-  `TCSlib.Cryptography.gi_rep_efficientProverProof` — [PS10, Proposition 120.7].
+  `TCSlib.Cryptography.gi_rep_efficientProverProof` — [PS10, Proposition 120.7];
+  `TCSlib.Cryptography.giProtocol_proverBounded`, `TCSlib.Cryptography.gniProtocol_proverBounded`
+  (and the `Rep` forms) — the honest messages are bounded (ruling G3-3).
 * `TCSlib.Cryptography.Riso_witnessRelation` — `Riso` is a witness relation for `Liso`.
 
 ## References
@@ -826,7 +828,7 @@ theorem gni_honest_reply {n : ℕ} {G₀ G₁ : Graph n} (h : ¬ Isomorphic G₀
 
 /-! ### Efficiency of the honest parties (Inf-4.2) -/
 
-/-- The honest prover of the graph isomorphism protocol is a PPT strategy
+/-- The honest prover of the graph isomorphism protocol is efficient (D8)
 [PS10, Proposition 120.7, efficient prover] (Inf-4.2).
 
 **Proof sketch.** `Strategy.Efficient` with `NUPPT.ofPolyTimeUniform` of the string function
@@ -839,7 +841,7 @@ the case split on `msgs = []` by `polyTimeComputable_lenEq`; the equation with `
 by `NUPPT.runAtL_ofPolyTimeUniform`, `Strategy.pairFstD_encodeMsgs`, `decPerm_encPerm`. -/
 theorem giProver_efficient : giProver.Efficient := GI.giProver_efficient
 
-/-- The verifier of the graph isomorphism protocol is a PPT strategy [PS10, Definition 116.1
+/-- The verifier of the graph isomorphism protocol is efficient (D8) [PS10, Definition 116.1
 for Proposition 120.7] (Inf-4.2).
 
 **Proof sketch.** As `giProver_efficient`: the challenge is the first coin
@@ -849,24 +851,24 @@ conjoined (`polyTimeComputable_and`) with the well-formedness test (`polyTimeCom
 against the squared vertex count in unary and `computesFunInTime_pairValid`). -/
 theorem giVerifier_efficient : giVerifier.Efficient := GI.giVerifier_efficient
 
-/-- The verifier of one iteration of the graph non-isomorphism protocol is a PPT strategy
+/-- The verifier of one iteration of the graph non-isomorphism protocol is efficient (D8)
 [PS10, Proposition 118.4] (Inf-4.2): as `giVerifier_efficient`, with the first message
 `polyTimeComputable_encPermGraph` on `⟨G_b, encPerm σ⟩` for `σ` from
 `polyTimeComputable_encSamplePerm` and the verdict a one-bit comparison. -/
 theorem gniVerifier_efficient : gniVerifier.Efficient := GI.gniVerifier_efficient
 
-/-- The verifier of the `|x|`-fold graph non-isomorphism protocol is a PPT strategy
+/-- The verifier of the `|x|`-fold graph non-isomorphism protocol is efficient (D8)
 (Inf-4.2): the coin block of iteration `hist.length` is cut by `pairTakePoly`/`pairDropPoly`
 with the unary block length, the message as in `gniVerifier_efficient`, and the verdict is a
 loop over the `|x|` replies (`polyTimeComputable_iterate` with an accumulated conjunction). -/
 theorem gniVerifierRep_efficient : gniVerifierRep.Efficient := GI.gniVerifierRep_efficient
 
-/-- The prover of the `|x|`-fold graph isomorphism protocol is a PPT strategy (Inf-4.2): as
+/-- The prover of the `|x|`-fold graph isomorphism protocol is efficient (D8) (Inf-4.2): as
 `giProver_efficient` with the coin block of iteration `hist.length / 2` cut by
 `pairTakePoly`/`pairDropPoly` and the parity test of the history length. -/
 theorem giProverRep_efficient : giProverRep.Efficient := GI.giProverRep_efficient
 
-/-- The verifier of the `|x|`-fold graph isomorphism protocol is a PPT strategy (Inf-4.2):
+/-- The verifier of the `|x|`-fold graph isomorphism protocol is efficient (D8) (Inf-4.2):
 the challenge is coin `hist.length / 2`, and the verdict is a loop over the `|x|` pairs
 `(H_j, γ_j)` of the history (`polyTimeComputable_iterate` over `polyTimeComputable_encPermGraph`
 and `polyTimeComputable_pairEq`). -/
@@ -918,6 +920,23 @@ Efficiency: `gniVerifierRep_efficient`. -/
 theorem gni_interactiveProof : InteractiveProof gniProtocolRep Lniso :=
   GI.gni_interactiveProof gniVerifierRep_efficient
 
+/-- The honest provers of the graph-isomorphism protocols send `n²`-bit words with
+`n² ≤ |x|`, so at most `|x|` bits per message, on every instance (ruling G3-3 of gate 03;
+`GI.giProver_length_le`). -/
+theorem giProtocol_proverBounded (R : List Bool → List Bool → Prop) :
+    giProtocol.ProverBounded R .var := fun x y r hist _ => GI.giProver_length_le x y r hist
+
+/-- The `|x|`-fold form of `giProtocol_proverBounded` (`GI.giProverRep_length_le`). -/
+theorem giProtocolRep_proverBounded (R : List Bool → List Bool → Prop) :
+    giProtocolRep.ProverBounded R .var := fun x y r hist _ => GI.giProverRep_length_le x y r hist
+
+/-- The honest graph non-isomorphism prover sends one bit per message (ruling G3-3 of gate 03;
+`GI.gniProver_length_le`), in one iteration and in the `|x|`-fold protocol. -/
+theorem gniProtocol_proverBounded (R : List Bool → List Bool → Prop) :
+    gniProtocol.ProverBounded R (.const 1) ∧ gniProtocolRep.ProverBounded R (.const 1) :=
+  ⟨fun x y r hist _ => GI.gniProver_length_le x y r hist,
+    fun x y r hist _ => GI.gniProver_length_le x y r hist⟩
+
 /-- One iteration of the graph isomorphism protocol is an interactive proof for `L_iso`
 with soundness error `1/2` and efficient prover with respect to `R_iso`
 [PS10, Proposition 120.7, corrected: for `L_iso`, not `L_niso`] (Prop-120.7).
diff --git a/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Efficiency.lean b/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Efficiency.lean
index 55508abf..e7048422 100644
--- a/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Efficiency.lean
+++ b/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Efficiency.lean
@@ -51,7 +51,7 @@ malformed inputs).
   count is polynomial-time.
 * `TCSlib.Cryptography.GI.Riso_decidable` — the decider clause of `Riso_witnessRelation`.
 * `TCSlib.Cryptography.GI.giProver_efficient`, `GI.giVerifier_efficient`,
-  `GI.gniVerifier_efficient` — the single-iteration parties are PPT strategies.
+  `GI.gniVerifier_efficient` — the single-iteration parties are efficient (D8).
 
 ## References
 
@@ -469,7 +469,7 @@ theorem Riso_decidable : ∃ T : List Bool → Bool, PolyTimeComputable (fun z =
 
 /-! ### Efficiency of the single-iteration parties -/
 
-/-- The honest prover of the graph isomorphism protocol is a PPT strategy
+/-- The honest prover of the graph isomorphism protocol is efficient (D8)
 [PS10, Proposition 120.7] (Inf-4.2).
 
 **Proof sketch.** `efficient_of_polyTime` with the layout function: message `1` is
@@ -505,7 +505,7 @@ theorem giProver_efficient : giProver.Efficient := by
     rw [sampleStr, mulInvStr_encPerm]
     split_ifs <;> rfl
 
-/-- The verifier of the graph isomorphism protocol is a PPT strategy [PS10, Definition 116.1
+/-- The verifier of the graph isomorphism protocol is efficient (D8) [PS10, Definition 116.1
 for Proposition 120.7] (Inf-4.2).
 
 **Proof sketch.** `efficient_of_polyTime`: the challenge is the first coin (`coinBit_poly`),
@@ -555,7 +555,7 @@ theorem giVerifier_efficient : giVerifier.Efficient := by
     simp only [argM_ilayout, Strategy.encodeMsgs_cons, Turing.pairEncode_ne_nil, decide_false,
       Bool.false_eq_true, if_false, pairSndD_pairEncode]
 
-/-- The verifier of one iteration of the graph non-isomorphism protocol is a PPT strategy
+/-- The verifier of one iteration of the graph non-isomorphism protocol is efficient (D8)
 [PS10, Proposition 118.4] (Inf-4.2).
 
 **Proof sketch.** `efficient_of_polyTime`: the first message is `relabel_poly` of `G_b` by
diff --git a/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/EfficiencyRep.lean b/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/EfficiencyRep.lean
index cdac6fc5..56bfb24b 100644
--- a/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/EfficiencyRep.lean
+++ b/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/EfficiencyRep.lean
@@ -39,7 +39,7 @@ and one **unary-count loop** (`iterUnary_poly`: iterate a step `|u|` times for a
 * `TCSlib.Cryptography.GI.unaryMul_poly`, `GI.coinSlice_poly` — unary multiplication and the
   coin block of a given iteration.
 * `TCSlib.Cryptography.GI.gniVerifierRep_efficient` — the `|x|`-fold graph non-isomorphism
-  verifier is a PPT strategy.
+  verifier is efficient (D8).
 
 ## References
 
@@ -584,7 +584,7 @@ theorem gni_verdict_iff (hist : List (List Bool)) (r : List Bool) (N c : ℕ) (h
   rw [iterate_pairSndD_encodeMsgs, Strategy.pairFstD_encodeMsgs, coinSlice, headD_take hc, Fin.val_mk,
     getD_eq_headD_drop]
 
-/-- The verifier of the `|x|`-fold graph non-isomorphism protocol is a PPT strategy (Inf-4.2).
+/-- The verifier of the `|x|`-fold graph non-isomorphism protocol is efficient (D8) (Inf-4.2).
 
 **Proof sketch.** `efficient_of_polyTime`: the message count `1^{|hist|}` (`cnt_poly`), the
 test `|hist| < |x|` (`ltLen_poly`), the coin block of the current iteration (`gniSlice_poly`)
diff --git a/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/EfficiencyRepGI.lean b/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/EfficiencyRepGI.lean
index aaee9471..143e3bbf 100644
--- a/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/EfficiencyRepGI.lean
+++ b/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/EfficiencyRepGI.lean
@@ -28,7 +28,7 @@ current iteration (`coinSlice_poly`), and the verdict scan over the `|x|` iterat
 ## Main results
 
 * `TCSlib.Cryptography.GI.giProverRep_efficient`, `GI.giVerifierRep_efficient` — the parties of
-  the `|x|`-fold graph isomorphism protocol are PPT strategies.
+  the `|x|`-fold graph isomorphism protocol are efficient (D8).
 
 ## References
 
@@ -98,7 +98,7 @@ theorem lastBit_poly : PolyTimeComputable fun w =>
     [(pairFstD (pairSndD^[lastSteps (argM w)] (argM w))).headD false] :=
   headBit_poly.comp (lastMsg_poly.comp argM_poly)
 
-/-- The prover of the `|x|`-fold graph isomorphism protocol is a PPT strategy (Inf-4.2).
+/-- The prover of the `|x|`-fold graph isomorphism protocol is efficient (D8) (Inf-4.2).
 
 **Proof sketch.** `efficient_of_polyTime`: the half count `|hist| / 2` and the parity by the
 half loop (`halfLoop_poly`), the coin block of the current iteration (`giSlice_poly`), the
@@ -304,7 +304,7 @@ theorem gi_verdict_iff (x : List Bool) (hist : List (List Bool)) (r : List Bool)
     ← getD_eq_headD_drop, ← getD_eq_headD_drop]
   cases r.getD j false <;> exact Iff.rfl
 
-/-- The verifier of the `|x|`-fold graph isomorphism protocol is a PPT strategy (Inf-4.2).
+/-- The verifier of the `|x|`-fold graph isomorphism protocol is efficient (D8) (Inf-4.2).
 
 **Proof sketch.** `efficient_of_polyTime`: the parity of the message count (`odd_poly`), the
 challenge `r_{|hist|/2}` (`challenge_poly`), the test `|hist| < 2|x|` (`ltLen2_poly`), and the
diff --git a/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs.lean b/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs.lean
index 77ad5854..154c9cd0 100644
--- a/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs.lean
+++ b/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs.lean
@@ -53,6 +53,9 @@ need (Lem-119.a, Lem-120.b–c, the honest replies).
   two graphs.
 * `TCSlib.Cryptography.GI.efficient_of_polyTime` — a strategy whose next-message function is a
   polynomial-time function of the machine layout is efficient.
+* `TCSlib.Cryptography.GI.giProver_length_le`, `GI.giProverRep_length_le`,
+  `GI.gniProver_length_le` — the honest provers' messages have at most `|x|` bits (one bit for
+  graph non-isomorphism), whatever the tape and history (ruling G3-3).
 * `TCSlib.Cryptography.GI.gniProtocol_outV`, `GI.giProtocol_outV` and the `*_next_*` lemmas —
   the verdicts of the single-iteration protocols on encoded instances.
 * `TCSlib.Cryptography.GI.pushesUniform_castLE`, `GI.statClose_samplePerm_long` — a prefix of a
@@ -237,6 +240,36 @@ noncomputable def giProtocolRep : Protocol where
   rounds := .mul (.const 4) .var
   verifierFirst := false
 
+/-! ### Bounded prover messages (ruling G3-3 of gate 03) -/
+
+/-- The honest prover of one graph-isomorphism iteration sends `n²`-bit words (`encGraph`,
+`encPerm`) with `n = Nat.sqrt` of the length of the first component of `x`, hence at most
+`|x|` bits, whatever its auxiliary input, tape and history (`Nat.sqrt_le`,
+`length_pairFstD_le`). -/
+theorem giProver_length_le (x y r : List Bool) (hist : List (List Bool)) :
+    (giProver.next x y r hist).length ≤ x.length := by
+  have h : (giProver.next x y r hist).length =
+      Nat.sqrt (pairFstD x).length * Nat.sqrt (pairFstD x).length := by
+    cases hist <;> simp [giProver, decGraph]
+  rw [h]
+  exact (Nat.sqrt_le _).trans (length_pairFstD_le x)
+
+/-- The honest prover of the `|x|`-fold graph-isomorphism protocol sends at most `|x|` bits per
+message, as in one iteration (`giProver_length_le`). -/
+theorem giProverRep_length_le (x y r : List Bool) (hist : List (List Bool)) :
+    (giProverRep.next x y r hist).length ≤ x.length := by
+  have h : (giProverRep.next x y r hist).length =
+      Nat.sqrt (pairFstD x).length * Nat.sqrt (pairFstD x).length := by
+    simp only [giProverRep]
+    split_ifs <;> simp [instanceVertexCount]
+  rw [h]
+  exact (Nat.sqrt_le _).trans (length_pairFstD_le x)
+
+/-- The honest prover of the graph non-isomorphism protocol sends one bit per message. -/
+theorem gniProver_length_le (x y r : List Bool) (hist : List (List Bool)) :
+    (gniProver.next x y r hist).length ≤ 1 := by
+  simp [gniProver]
+
 /-! ### Isomorphism algebra (shadow copies of the main file's lemmas) -/
 
 /-- Every graph is isomorphic to itself. -/
diff --git a/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Soundness.lean b/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Soundness.lean
index f05c284f..a8918e97 100644
--- a/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Soundness.lean
+++ b/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Soundness.lean
@@ -173,8 +173,9 @@ theorem gni_interactiveProofErr (hV : gniVerifier.Efficient) :
     InteractiveProofErr gniProtocol Lniso (fun N => 1 / 2 + permFailBound (instanceVertices N)) where
   efficientV := hV
   complete := by
+    refine ⟨.const 1, ?_⟩
     rintro x ⟨n, G₀, G₁, rfl, hni⟩
-    exact ⟨[], fun z => gni_complete hni [] z⟩
+    exact ⟨[], gniProver_length_le _ [], fun z => gni_complete hni [] z⟩
   sound := by
     intro x hx P' z
     by_cases hwf : wellFormedInstance x = true
@@ -293,8 +294,9 @@ theorem gi_efficientProverProofErr (hP : giProver.Efficient) (hV : giVerifier.Ef
     EfficientProverProofErr giProtocol Liso Riso (fun _ => 1 / 2) where
   efficientV := hV
   complete := by
+    refine ⟨.var, ?_⟩
     rintro x ⟨n, G₀, G₁, σ, rfl, hσ⟩
-    exact ⟨encPerm σ, fun z => gi_complete hσ z⟩
+    exact ⟨encPerm σ, giProver_length_le _ _, fun z => gi_complete hσ z⟩
   sound := by
     intro x hx P' z
     by_cases hwf : wellFormedInstance x = true
@@ -316,6 +318,7 @@ theorem gi_efficientProverProofErr (hP : giProver.Efficient) (hV : giVerifier.Ef
       rw [HardcoreBit.uprob_eq_one_of_forall hall]
       norm_num
   efficientP := hP
+  boundedP := ⟨.var, fun x y r hist _ => giProver_length_le x y r hist⟩
   completeWitness := by
     rintro x y ⟨n, G₀, G₁, σ, rfl, rfl, hσ⟩ z
     exact gi_complete hσ z
diff --git a/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRep.lean b/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRep.lean
index 4647fec0..b5affdac 100644
--- a/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRep.lean
+++ b/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRep.lean
@@ -413,8 +413,9 @@ theorem gni_interactiveProofErrRep (hV : gniVerifierRep.Efficient) :
       (fun N => (2 : ℝ)⁻¹ ^ N + N * permFailBound (instanceVertices N)) where
   efficientV := hV
   complete := by
+    refine ⟨.const 1, ?_⟩
     rintro x ⟨n, G₀, G₁, rfl, hni⟩
-    exact ⟨[], fun z => gniRep_complete hni [] z⟩
+    exact ⟨[], gniProver_length_le _ [], fun z => gniRep_complete hni [] z⟩
   sound := by
     intro x hx P' z
     by_cases hwf : wellFormedInstance x = true
diff --git a/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRepGI.lean b/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRepGI.lean
index 28202b3a..4aeed143 100644
--- a/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRepGI.lean
+++ b/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRepGI.lean
@@ -446,8 +446,9 @@ theorem gi_rep_efficientProverProofErr (hP : giProverRep.Efficient) (hV : giVeri
     EfficientProverProofErr giProtocolRep Liso Riso (fun N => (2 : ℝ)⁻¹ ^ N) where
   efficientV := hV
   complete := by
+    refine ⟨.var, ?_⟩
     rintro x ⟨n, G₀, G₁, σ, rfl, hσ⟩
-    exact ⟨encPerm σ, fun z => giRep_complete hσ z⟩
+    exact ⟨encPerm σ, giProverRep_length_le _ _, fun z => giRep_complete hσ z⟩
   sound := by
     intro x hx P' z
     by_cases hwf : wellFormedInstance x = true
@@ -473,6 +474,7 @@ theorem gi_rep_efficientProverProofErr (hP : giProverRep.Efficient) (hV : giVeri
       have : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ x.length := by positivity
       linarith
   efficientP := hP
+  boundedP := ⟨.var, fun x y r hist _ => giProverRep_length_le x y r hist⟩
   completeWitness := by
     rintro x y ⟨n, G₀, G₁, σ, rfl, rfl, hσ⟩ z
     exact giRep_complete hσ z
diff --git a/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphismZK.lean b/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphismZK.lean
index 575ba2ae..ff43a6b3 100644
--- a/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphismZK.lean
+++ b/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphismZK.lean
@@ -40,7 +40,12 @@ perfect zero-knowledge with an expected polynomial-time simulator); only one ite
 treated (the text defers the `n`-fold protocol to its §7.2.1); the Goldreich abort form
 `PerfectZKAbort` holds for the one-attempt simulator at the concrete layer
 (`giSimAttempt_perfectAbort`) but is not claimed for `giProtocol` itself, whose honest
-prover's rejection-sampled `π` is not exactly uniform.
+prover's rejection-sampled `π` is not exactly uniform. No honest prover drawing its
+permutation from polynomially many fair coins could do better (`n! ∤ 2^c` for `n ≥ 3`), so
+neither `PerfectZK` nor `PerfectZKAbort` has a source instance under D8 and D10 (ruling G3-4
+of gate 03; see their docstrings in `ZeroKnowledge/Defs.lean`); `gi_statZK` is the form in
+which [PS10, Theorem 122.3] is stated, and `PerfectZKAbort.statZK` relates the abort form to
+it.
 
 ## Contents
 
@@ -79,8 +84,8 @@ prover's rejection-sampled `π` is not exactly uniform.
   (§4.6 Zero-knowledge proofs, pp. 122–124.)
 * [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
   draft of 22 January 2026 (the concrete probability layer).
-* O. Goldreich, *Foundations of Cryptography, Volume I: Basic Tools*, Cambridge University
-  Press, 2001, Definition 4.3.1 (perfect zero-knowledge with abort).
+* [Gol01] O. Goldreich, *Foundations of Cryptography, Volume I: Basic Tools*, Cambridge
+  University Press, 2001, Definition 4.3.1 (perfect zero-knowledge with abort).
 -/
 
 namespace TCSlib.Cryptography
@@ -281,7 +286,7 @@ theorem uprob_giSimAttempt_some {n : ℕ} {ρ : Type*} [Fintype ρ] {G₀ G₁ :
   linarith
 
 /-- The abort form of perfect zero-knowledge for one attempt of the simulator
-[Goldreich, Definition 4.3.1; PS10, Algorithm 123.4] (Claim-123.b, `PerfectZKAbort` shape at
+[Gol01, Definition 4.3.1; PS10, Algorithm 123.4] (Claim-123.b, `PerfectZKAbort` shape at
 the concrete layer): the attempt aborts with probability at most `1/2`, and for every test
 set `T`, `Pr[T(view)] · Pr[attempt ≠ ⊥] = Pr[attempt ≠ ⊥ ∧ T(attempt)]`. -/
 theorem giSimAttempt_perfectAbort {n : ℕ} {ρ : Type*} [Fintype ρ] [Nonempty ρ] {G₀ G₁ : Graph n}
diff --git a/TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean b/TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean
index 94818e32..e8cb2fe1 100644
--- a/TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean
+++ b/TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean
@@ -78,6 +78,8 @@ the commitment.
 * `TCSlib.Cryptography.col_efficientProverProofErr`,
   `TCSlib.Cryptography.colRep_efficientProverProof` — **[PS10, Proposition 127.6]**, the
   interactive-proof half (Prop-127.6).
+* `TCSlib.Cryptography.colProver_length_le`, `TCSlib.Cryptography.colProtocol_proverBounded`
+  — the honest provers' messages are polynomially bounded in `|x|` (ruling G3-3).
 * `TCSlib.Cryptography.R3COL_witnessRelation` — `R_3COL` is a witness relation for `3COL`.
 
 ## References
@@ -503,7 +505,7 @@ noncomputable def colProtocolRep (Com : List Bool → List Bool) (ℓ : PolyExpr
 
 /-! ### Efficiency of the honest parties (Inf-4.2) -/
 
-/-- The honest prover of one iteration is a PPT strategy when `Com` is polynomial-time
+/-- The honest prover of one iteration is efficient (D8) when `Com` is polynomial-time
 [PS10, Proposition 127.6, efficient prover] (Inf-4.2).
 
 **Proof sketch.** `Strategy.Efficient` with `NUPPT.ofPolyTimeUniform` of the string function
@@ -522,7 +524,7 @@ theorem colProver_efficient {Com : List Bool → List Bool} (hCom : PolyTimeComp
     (ℓ : PolyExpr) : (colProver Com ℓ).Efficient :=
   ColProofs.colProver_efficient hCom ℓ
 
-/-- The verifier of one iteration is a PPT strategy when `Com` is polynomial-time
+/-- The verifier of one iteration is efficient (D8) when `Com` is polynomial-time
 [PS10, Definition 116.1 for Proposition 127.6] (Inf-4.2).
 
 **Proof sketch.** As `colProver_efficient`: the edge index by `polyTimeComputable_iterateFind`
@@ -537,14 +539,14 @@ theorem colVerifier_efficient {Com : List Bool → List Bool} (hCom : PolyTimeCo
     (ℓ : PolyExpr) : (colVerifier Com ℓ).Efficient :=
   ColProofs.colVerifier_efficient hCom ℓ
 
-/-- The prover of the `n|E|`-fold protocol is a PPT strategy (Inf-4.2): `colProver_efficient`
+/-- The prover of the `n|E|`-fold protocol is efficient (D8) (Inf-4.2): `colProver_efficient`
 on the coin block `hist.length / 2` cut by `pairTakePoly`/`pairDropPoly`, with the parity and
 iteration tests by `polyTimeComputable_lenLe` on unary counters. -/
 theorem colProverRep_efficient {Com : List Bool → List Bool} (hCom : PolyTimeComputable Com)
     (ℓ : PolyExpr) : (colProverRep Com ℓ).Efficient :=
   ColProofs.colProverRep_efficient hCom ℓ
 
-/-- The verifier of the `n|E|`-fold protocol is a PPT strategy (Inf-4.2): the challenge as in
+/-- The verifier of the `n|E|`-fold protocol is efficient (D8) (Inf-4.2): the challenge as in
 `colVerifier_efficient` on the block `hist.length / 2`, and the verdict a loop over the
 `n|E|` pairs of the history (`polyTimeComputable_iterate` with an accumulated conjunction of
 `colVerify` checks). -/
@@ -552,6 +554,64 @@ theorem colVerifierRep_efficient {Com : List Bool → List Bool} (hCom : PolyTim
     (ℓ : PolyExpr) : (colVerifierRep Com ℓ).Efficient :=
   ColProofs.colVerifierRep_efficient hCom ℓ
 
+/-! ### Bounded prover messages (ruling G3-3 of gate 03) -/
+
+/-- A vector of `q` commitments to `n`-bit values with `m`-bit randomness has at most
+`q (2 C (2n + 3 + m)^c + 2)` bits when `C (|w| + 1)^c` bounds `|Com w|`
+(`CommitmentLemmas.length_encodeMsgs_le`, `length_pairEncode`). -/
+theorem length_multiCom_le {Com : List Bool → List Bool} {C c : ℕ}
+    (hC : ∀ w, (Com w).length ≤ C * (w.length + 1) ^ c) {q n m : ℕ} (v : Fin q → Fin n → Bool)
+    (r : Fin q → Fin m → Bool) :
+    (multiCom Com v r).length ≤ q * (2 * (C * (2 * n + 3 + m) ^ c) + 2) := by
+  unfold multiCom
+  refine (CommitmentLemmas.length_encodeMsgs_le _ (C * (2 * n + 3 + m) ^ c)
+    fun msg hmsg => ?_).trans (by simp)
+  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hmsg
+  refine (hC _).trans (le_of_eq ?_)
+  rw [length_pairEncode, List.length_ofFn, List.length_ofFn]
+  ring_nf
+
+/-- **The honest prover of one iteration sends polynomially bounded messages** (ruling G3-3 of
+gate 03): for `C (|w| + 1)^c` bounding `|Com w|` and `n = (decGraph x).1 ≤ |x|`, the
+commitment message has at most `n (2 C (2n + 3 + ℓ(n))^c + 2)` bits (`length_multiCom_le`),
+the opening `3 ℓ(n) + 20` (`length_pairEncode`, `length_encColoring`) and the empty reply none;
+`ℓ` is monotone (`PolyExpr.eval_mono`). The bound holds for every tape and history, since
+`colCommit` and `colOpen` have a fixed shape. -/
+theorem colProver_length_le {Com : List Bool → List Bool} (hCom : PolyTimeComputable Com)
+    (ℓ : PolyExpr) : ∃ B : PolyExpr, ∀ x y r hist,
+      ((colProver Com ℓ).next x y r hist).length ≤ B.eval x.length := by
+  obtain ⟨C, c, hC⟩ := hCom.output_length_le
+  refine ⟨.add (.mul .var (.add (.mul (.const 2) (.mul (.const C)
+    (.pow (.add (.add (.mul (.const 2) .var) (.const 3)) ℓ) c))) (.const 2)))
+    (.add (.mul (.const 3) ℓ) (.const 20)), fun x y r hist => ?_⟩
+  have hn : (decGraph x).1 ≤ x.length := Nat.sqrt_le_self _
+  have hℓ : ℓ.eval (decGraph x).1 ≤ ℓ.eval x.length := ℓ.eval_mono hn
+  have hcom : (decGraph x).1 * (2 * (C * (2 * (decGraph x).1 + 3 + ℓ.eval (decGraph x).1) ^ c) + 2)
+      ≤ x.length * (2 * (C * (2 * x.length + 3 + ℓ.eval x.length) ^ c) + 2) := by
+    gcongr
+  simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_pow,
+    PolyExpr.eval_var, colProver]
+  split
+  · exact (length_multiCom_le hC _ _).trans (hcom.trans (Nat.le_add_right _ _))
+  · split
+    · simp only [colOpen, length_pairEncode, List.length_ofFn, encColor, length_encColoring]
+      omega
+    · simp
+
+/-- **The honest provers of [PS10, Protocol 127.5] send polynomially bounded messages**, one
+iteration and `n|E|`-fold, on every instance (ruling G3-3 of gate 03): the bound of
+`colProver_length_le` from the commitment's polynomial-time evaluator; the repeated prover
+runs `colProver` on a coin block or sends `[]`. -/
+theorem colProtocol_proverBounded {Com : List Bool → List Bool} {ℓ : PolyExpr}
+    (hC : Commitment Com ℓ) (R : List Bool → List Bool → Prop) :
+    ∃ B : PolyExpr, (colProtocol Com ℓ).ProverBounded R B ∧
+      (colProtocolRep Com ℓ).ProverBounded R B := by
+  obtain ⟨B, hB⟩ := colProver_length_le hC.easy ℓ
+  refine ⟨B, fun x y r hist _ => hB x y r hist, fun x y r hist _ => ?_⟩
+  show ((colProverRep Com ℓ).next x y r hist).length ≤ B.eval x.length
+  simp only [colProverRep]
+  split_ifs <;> first | exact hB _ _ _ _ | exact Nat.zero_le _
+
 /-! ### Proposition 127.6, interactive-proof half -/
 
 section OneIteration
@@ -815,12 +875,14 @@ theorem col_efficientProverProofErr {Com : List Bool → List Bool} {ℓ : PolyE
       (fun N => 1 - 1 / (N : ℝ) + (1 / 2 : ℝ) ^ N) where
   efficientV := colVerifier_efficient hC.easy ℓ
   complete := by
-    intro x hx
+    obtain ⟨B, hB, -⟩ := colProtocol_proverBounded hC R3COL
+    refine ⟨B, fun x hx => ?_⟩
     obtain ⟨y, n, G, c, rfl, rfl, hc⟩ := (mem_L3COL_iff x).1 hx
-    exact ⟨encColoring c, fun z => HardcoreBit.uprob_eq_one_of_forall fun r =>
-      colProtocol_outV_honest hc z r⟩
+    exact ⟨encColoring c, fun r hist => hB _ _ r hist ⟨n, G, c, rfl, rfl, hc⟩,
+      fun z => HardcoreBit.uprob_eq_one_of_forall fun r => colProtocol_outV_honest hc z r⟩
   sound := fun x hx P' z => colProtocol_sound hC x hx P' z
   efficientP := colProver_efficient hC.easy ℓ
+  boundedP := (colProtocol_proverBounded hC R3COL).imp fun _ h => h.1
   completeWitness := by
     rintro x y ⟨n, G, c, rfl, rfl, hc⟩ z
     exact HardcoreBit.uprob_eq_one_of_forall fun r => colProtocol_outV_honest hc z r
@@ -847,7 +909,8 @@ probability is at most `(1 - 1/|E|)^{n|E|} ≤ e^{-n}` (`one_sub_inv_pow_mul_le_
 `n = Nat.sqrt |x|` (`length_encGraph`, `Nat.sqrt_eq`). Negligibility:
 `negligible_exp_neg_sqrt_div` with `C = 1`, `Negligible.mul_pow negligible_two_pow_neg 2`,
 `negligible_two_pow_neg`, `Negligible.add`. Efficiency: `colProverRep_efficient`,
-`colVerifierRep_efficient`. -/
+`colVerifierRep_efficient`. Bounded prover messages (and the bound in the completeness
+clause): `colProtocol_proverBounded`. -/
 theorem colRep_efficientProverProof {Com : List Bool → List Bool} {ℓ : PolyExpr}
     (hC : Commitment Com ℓ) : EfficientProverProof (colProtocolRep Com ℓ) L3COL R3COL := by
   sorry
diff --git a/TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/ProtocolProofs.lean b/TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/ProtocolProofs.lean
index 49577820..ab4796e9 100644
--- a/TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/ProtocolProofs.lean
+++ b/TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/ProtocolProofs.lean
@@ -33,7 +33,7 @@ main file makes the main file fail to type-check, so it cannot go unnoticed.
   when the graph has an edge.
 * `TCSlib.Cryptography.ColProofs.colProver_efficient`, `ColProofs.colVerifier_efficient`,
   `ColProofs.colProverRep_efficient`, `ColProofs.colVerifierRep_efficient` — the (shadow)
-  parties are PPT strategies (Inf-4.2).
+  parties are efficient (D8) (Inf-4.2).
 * `TCSlib.Cryptography.ColProofs.pushesUniform_castLE`, `ColProofs.sampleEdgeIdx_ofFn_castLE`,
   `ColProofs.finOneEquiv`, `ColProofs.two_le_of_edge` — helpers of the soundness proof of
   Proposition 127.6.
@@ -316,22 +316,22 @@ theorem colVerifierRep_next_eq (Com : List Bool → List Bool) (ℓ : PolyExpr)
 
 /-! ### Efficiency of the (shadow) parties -/
 
-/-- The honest prover of one iteration is a PPT strategy when `Com` is (shadow form). -/
+/-- The honest prover of one iteration is efficient (D8) when `Com` is (shadow form). -/
 theorem colProver_efficient {Com : List Bool → List Bool} (hCom : PolyTimeComputable Com)
     (ℓ : PolyExpr) : (colProver Com ℓ).Efficient :=
   efficient_of_polyTime _ (proverStr_poly Com ℓ hCom) (colProver_next_eq Com ℓ)
 
-/-- The verifier of one iteration is a PPT strategy when `Com` is (shadow form). -/
+/-- The verifier of one iteration is efficient (D8) when `Com` is (shadow form). -/
 theorem colVerifier_efficient {Com : List Bool → List Bool} (hCom : PolyTimeComputable Com)
     (ℓ : PolyExpr) : (colVerifier Com ℓ).Efficient :=
   efficient_of_polyTime _ (verifierStr_poly Com ℓ hCom) (colVerifier_next_eq Com ℓ)
 
-/-- The prover of the `n|E|`-fold protocol is a PPT strategy when `Com` is (shadow form). -/
+/-- The prover of the `n|E|`-fold protocol is efficient (D8) when `Com` is (shadow form). -/
 theorem colProverRep_efficient {Com : List Bool → List Bool} (hCom : PolyTimeComputable Com)
     (ℓ : PolyExpr) : (colProverRep Com ℓ).Efficient :=
   efficient_of_polyTime _ (proverRepStr_poly Com ℓ hCom) (colProverRep_next_eq Com ℓ)
 
-/-- The verifier of the `n|E|`-fold protocol is a PPT strategy when `Com` is (shadow form). -/
+/-- The verifier of the `n|E|`-fold protocol is efficient (D8) when `Com` is (shadow form). -/
 theorem colVerifierRep_efficient {Com : List Bool → List Bool} (hCom : PolyTimeComputable Com)
     (ℓ : PolyExpr) : (colVerifierRep Com ℓ).Efficient :=
   efficient_of_polyTime _ (verifierRepStr_poly Com ℓ hCom) (colVerifierRep_next_eq Com ℓ)
diff --git a/audits/pass-shelat/Checks.lean b/audits/pass-shelat/Checks.lean
index 8eb0368d..ed7c52c4 100644
--- a/audits/pass-shelat/Checks.lean
+++ b/audits/pass-shelat/Checks.lean
@@ -300,6 +300,10 @@ results must print exactly `[propext, Classical.choice, Quot.sound]`.
 #print axioms TCSlib.Cryptography.col_zk
 #print axioms TCSlib.Cryptography.col_hvzk
 #print axioms TCSlib.Cryptography.col_zeroKnowledgeProof
+-- The four Theorem 124.1 forms below print `sorryAx`. Gate 03e, minor 5(a): the sorried
+-- declarations they reach are exactly `colRep_efficientProverProof` and `col_zk` (the 3-colouring
+-- stubs of pack 03g); the transfer lemmas `LevinReduction.zk`, `.efficientProverProof(Err)`
+-- print clean (gate 03e section below).
 #print axioms TCSlib.Cryptography.zk_proof_of_levinReduction
 #print axioms TCSlib.Cryptography.zk_proof_of_owp_levinReduction
 #print axioms TCSlib.Cryptography.zk_proof_of_mem_NP
@@ -378,3 +382,39 @@ results must print exactly `[propext, Classical.choice, Quot.sound]`.
 #print axioms TCSlib.Cryptography.Candidates.statClose_sampleBelowL
 -- P9-1 (zk-model): the prefix-reading verifier of the sanity protocol (proved).
 #print axioms TCSlib.Cryptography.npProtocol_readsPrefix
+
+-- ## Gate 03e (ch. 2–4 interaction, proof systems, ZK definitions, commitments, NP layer)
+-- Minor 5(b): the pack's headlines that had no print.
+#print axioms TCSlib.Cryptography.LevinReduction.zk
+#print axioms TCSlib.Cryptography.LevinReduction.efficientProverProof
+#print axioms TCSlib.Cryptography.LevinReduction.efficientProverProofErr
+#print axioms TCSlib.Cryptography.Strategy.pullback_efficient
+#print axioms TCSlib.Cryptography.Commitment.multiHiding
+-- Ruling G3-3: bounded honest prover messages in the proof systems.
+#print axioms TCSlib.Cryptography.Protocol.ProverBounded.mono
+#print axioms TCSlib.Cryptography.Protocol.ProverBounded.exists_complete
+#print axioms TCSlib.Cryptography.Protocol.ProverBounded.pullback
+#print axioms TCSlib.Cryptography.InteractiveProof.exists_accept
+#print axioms TCSlib.Cryptography.InteractiveProofErr.exists_accept
+#print axioms TCSlib.Cryptography.npProtocol_proverBounded
+#print axioms TCSlib.Cryptography.npProtocol_interactiveProof
+#print axioms TCSlib.Cryptography.giProtocol_proverBounded
+#print axioms TCSlib.Cryptography.giProtocolRep_proverBounded
+#print axioms TCSlib.Cryptography.gniProtocol_proverBounded
+#print axioms TCSlib.Cryptography.gni_interactiveProofErr
+#print axioms TCSlib.Cryptography.gi_efficientProverProofErr
+#print axioms TCSlib.Cryptography.colProver_length_le
+#print axioms TCSlib.Cryptography.colProtocol_proverBounded
+-- Ruling G3-4: perfect zero-knowledge with abort implies statistical ZK (error 2^{-|x|}).
+#print axioms TCSlib.Cryptography.AbortRetry.statClose_retry
+#print axioms TCSlib.Cryptography.AbortRetry.exists_retrySimulator
+#print axioms TCSlib.Cryptography.PerfectZKAbort.statZK
+#print axioms TCSlib.Cryptography.PerfectZKAbort.zk
+#print axioms TCSlib.Cryptography.perfectZK_zeroRounds
+-- Minors 3 and 4, note 13: the text's Theorem 126.4, and Theorem 124.1 for every witness
+-- relation with the two protocols tied (the last three print `sorryAx`, reaching exactly
+-- `colRep_efficientProverProof` and `col_zk`, like the four forms above).
+#print axioms TCSlib.Cryptography.exists_commitment_of_owp
+#print axioms TCSlib.Cryptography.exists_commitment_zk_proof_of_owp_levinReduction
+#print axioms TCSlib.Cryptography.zk_proof_of_witnessRelation
+#print axioms TCSlib.Cryptography.zk_proof_of_witnessRelation_of_owp

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence/e2/replay.log =====

# closure of pack 03e2's files at e79397eaf68b156b9db091f464741f6eb75b9c28: 126 modules, extracted from replay-combined.log
TCSlib/Complexity/CircuitComplexity/Advice rc=0 4s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/Basic rc=0 8s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/DAGCircuit rc=0 3s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/DAGFanin rc=0 5s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/DAGTransform rc=0 2s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/LayeredCircuit rc=0 6s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/LayeredDAG rc=0 6s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/LayeredPPoly rc=0 1s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/PPoly rc=0 2s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/SizeClasses rc=0 2s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/TreeDAG rc=0 5s errors=0 sorry=0
TCSlib/Complexity/ClassNP/CoNP rc=0 1s errors=0 sorry=0
TCSlib/Complexity/ClassNP/CounterProgPolyTime rc=0 2s errors=0 sorry=0
TCSlib/Complexity/ClassNP/EXP rc=0 21s errors=0 sorry=0
TCSlib/Complexity/ClassNP/NP rc=0 3s errors=0 sorry=0
TCSlib/Complexity/ClassNP/PClosure rc=0 2s errors=0 sorry=0
TCSlib/Complexity/ClassNP/PolyTime rc=0 1s errors=0 sorry=0
TCSlib/Complexity/ClassNP/PolyTimeBlockLoop rc=0 3s errors=0 sorry=0
TCSlib/Complexity/ClassNP/PolyTimeBlockMajority rc=0 2s errors=0 sorry=0
TCSlib/Complexity/ClassNP/PolyTimeBlockTests rc=0 3s errors=0 sorry=0
TCSlib/Complexity/ClassNP/PolyTimePairing rc=0 2s errors=0 sorry=0
TCSlib/Complexity/ClassNP/PolyTimePrefix rc=0 3s errors=0 sorry=0
TCSlib/Complexity/ClassNP/Reductions rc=0 3s errors=0 sorry=0
TCSlib/Complexity/ClassP/DTIME rc=0 1s errors=0 sorry=0
TCSlib/Complexity/ClassP/P rc=0 2s errors=0 sorry=0
TCSlib/Complexity/ClassP/TimeConstructible rc=0 2s errors=0 sorry=2
TCSlib/Complexity/PolyHierarchy/Padding rc=0 2s errors=0 sorry=0
TCSlib/Complexity/Randomized/Build/IterateFind rc=0 5s errors=0 sorry=0
TCSlib/Complexity/Randomized/Build/IterateFindHost rc=0 4s errors=0 sorry=0
TCSlib/Complexity/Randomized/Build/PairSplit rc=0 4s errors=0 sorry=0
TCSlib/Complexity/Randomized/Build/StateLoop rc=0 1s errors=0 sorry=0
TCSlib/Complexity/Randomized/Build/StringLoops rc=0 3s errors=0 sorry=0
TCSlib/Complexity/Randomized/Build/UnaryMul rc=0 4s errors=0 sorry=0
TCSlib/Complexity/Randomized/Closure rc=0 2s errors=0 sorry=0
TCSlib/Complexity/Randomized/NonUniform rc=0 2s errors=0 sorry=1
TCSlib/Complexity/Randomized/PPT rc=0 1s errors=0 sorry=0
TCSlib/Complexity/Randomized/PolyExpr rc=0 2s errors=0 sorry=0
TCSlib/Complexity/Randomized/Primitives rc=0 1s errors=0 sorry=0
TCSlib/Complexity/Randomized/Repetition rc=0 2s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Build/Convention rc=0 2s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Build/Embed rc=0 3s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Build/EmitIterBody rc=0 13s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Build/EmitIterEmbed rc=0 2s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Build/Loop rc=0 50s errors=0 sorry=5
TCSlib/Complexity/TuringMachine/Build/Primitives rc=0 54s errors=0 sorry=3
TCSlib/Complexity/TuringMachine/Build/Wrappers rc=0 4s errors=0 sorry=2
TCSlib/Complexity/TuringMachine/Composition rc=0 3s errors=0 sorry=3
TCSlib/Complexity/TuringMachine/Configuration rc=0 2s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/CounterProg rc=0 5s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/CounterProgInput rc=0 2s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/CounterProgRun rc=0 4s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Deterministic rc=0 2s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Encoding rc=0 3s errors=0 sorry=1
TCSlib/Complexity/TuringMachine/Finite rc=0 2s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction rc=0 5s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Robustness/SingleTape rc=0 11s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Simulation rc=0 6s errors=0 sorry=1
TCSlib/Complexity/TuringMachine/StateRenaming rc=0 2s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Sweep rc=0 2s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/UnaryTape rc=0 2s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Universal rc=0 28s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/UniversalBlock rc=0 8s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/UniversalInterpreter rc=0 9s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/UniversalStartup rc=0 3s errors=0 sorry=0
TCSlib/Complexity/Uncomputability/Computable rc=0 2s errors=0 sorry=0
TCSlib/Complexity/Uncomputability/Diagonalization rc=0 1s errors=0 sorry=0
TCSlib/Complexity/Uncomputability/Halting rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/Adversary rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/Collections rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/CollectionsHelpers rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/CollectionsLemmas rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/Ensembles rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/EnsemblesLemmas rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/GoldreichLevinDomain rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCore rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreClaims rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreCollection rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreGL rc=0 8s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreGLColl rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreGLFamily rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreLemmas rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreLoops rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCorePermutation rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/NextBit rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/OneWay rc=0 8s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/OneWayLemmas rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/OneWayYao rc=0 60s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/Permutations rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/Pseudorandom rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/Sampling rc=0 6s errors=0 sorry=0
TCSlib/Cryptography/Foundations/Experiments rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/Foundations/Negligible rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Foundations/Probability rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/HardcoreBit/Basic rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/HardcoreBit/GoldreichLevin rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/HardcoreBit/InnerProduct rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/HardcoreBit/PairwiseIndependence rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/HardcoreBit/ThreeQuarters rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/OneWayFunctions/Amplification rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/OneWayFunctions/Basic rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/OneWayFunctions/OutputLength rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/Pseudorandom/GeneratorFromPermutation rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Pseudorandom/Generators rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/Pseudorandom/Indistinguishability rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/Commitment rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/CommitmentLemmas rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/Defs rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/Encoding rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/EncodingMachines rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/EncodingPermutations rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/Interaction rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/InteractiveProofs rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/NP rc=0 9s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/NPLemmas rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Machines rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Parties rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol rc=0 5s errors=0 sorry=2
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/ProtocolProofs rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator rc=0 4s errors=0 sorry=1
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorLemmas rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorMachine rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorNumeric rc=0 4s errors=0 sorry=0
TCSlib/InformationTheory/FinDist rc=0 3s errors=0 sorry=0
TCSlib/InformationTheory/StatisticalDistance rc=0 2s errors=0 sorry=0

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence/e2/axioms.log =====

# axiom prints of every public theorem and lemma for declarations in pack 03e2's files, at e79397eaf68b156b9db091f464741f6eb75b9c28
TCSlib.Cryptography.Strategy.encodeMsgs_nil: none
TCSlib.Cryptography.Strategy.encodeMsgs_cons: none
TCSlib.Cryptography.Strategy.pairFstD_encodeMsgs: propext, Quot.sound
TCSlib.Cryptography.Strategy.ofNUPPT_next: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Strategy.ofNUPPT_efficient: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Strategy.Efficient.exists_uniform: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Strategy.ReadsPrefix.next_congr: propext
TCSlib.Cryptography.Strategy.ReadsPrefix.mono: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.moverIsV_true: none
TCSlib.Cryptography.moverIsV_false: none
TCSlib.Cryptography.exec_zero: none
TCSlib.Cryptography.exec_succ: none
TCSlib.Cryptography.exec_length: propext, Quot.sound
TCSlib.Cryptography.Protocol.ProverBounded.mono: propext
TCSlib.Cryptography.Protocol.withV_V: none
TCSlib.Cryptography.Protocol.withV_P: none
TCSlib.Cryptography.Protocol.withV_rounds: none
TCSlib.Cryptography.Protocol.withV_verifierFirst: none
TCSlib.Cryptography.Protocol.withV_self: none
TCSlib.Cryptography.Protocol.outV_eq_out: propext
TCSlib.Cryptography.Protocol.outP_eq_out: propext
TCSlib.Cryptography.Protocol.transcript_eq: propext
TCSlib.Cryptography.Protocol.outV_withV: propext
TCSlib.Cryptography.Protocol.outV_eq_getLast_of_moverIsV: propext
TCSlib.Cryptography.Protocol.uprob_outV_eq_uexp: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Protocol.exists_proverCoins_le: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.InteractiveProofErr.interactiveProof: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.InteractiveProof.exists_err: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.InteractiveProof.exists_uprob_accept_lt: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.InteractiveProof.exists_accept: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.InteractiveProofErr.exists_accept: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Protocol.ProverBounded.exists_complete: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.mem_witnessLanguage: none
TCSlib.Cryptography.mem_witnessSet: none
TCSlib.Cryptography.WitnessRelation.eq_witnessLanguage: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.WitnessRelation.mem_NP: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.exists_witnessRelation_of_mem_NP: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.EfficientProverProofErr.efficientProverProof: propext,  Classical.choice,  Quot.sound
TCSlib.Cryptography.EfficientProverProof.exists_err: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.npProtocol_outV: propext, Quot.sound
TCSlib.Cryptography.npProtocol_readsPrefix: propext, Quot.sound
TCSlib.Cryptography.npProtocol_efficientV: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.npProtocol_efficientP: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.npProtocol_proverBounded: propext
TCSlib.Cryptography.npProtocol_interactiveProof: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.WitnessRelation.mem_IP: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.NP_subset_IP: propext, Classical.choice, Quot.sound
Complexity.NUPPT.simulate_eq: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.StatZK.zk: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.StatZK.hvzk: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.ZK.hvzk: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.StatZK.mono: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.negligible_const_zero: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.PerfectZK.statZK: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.PerfectZK.zk: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.perfectZK_zeroRounds: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.AbortRetry.attempt_poly: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.AbortRetry.retry_poly: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.AbortRetry.exists_retrySimulator: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.AbortRetry.firstHit_map_getD_eq: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.AbortRetry.statClose_retry: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.AbortRetry.uprob_not_ne_nil_le: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.PerfectZKAbort.statZK: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.PerfectZKAbort.zk: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.negligible_inv_pow_sqrt_div: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.negligible_two_pow_neg_sqrt_div: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.negligible_exp_neg_sqrt_div: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.negligible_of_le_inv_pow_sqrt_div: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.inv_pow_le_inv_pow_sqrt_div: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Commitment.binding_ofFn: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.acceptProb_pairHybrid_zero: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.acceptProb_pairHybrid_self: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.acceptProb_pairRed_left: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.acceptProb_pairRed_right: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.exists_pairRed_ge: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Commitment.multiHiding: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.bitCom_castSucc: propext, Quot.sound
TCSlib.Cryptography.bitCom_last: propext, Quot.sound
TCSlib.Cryptography.bitCom_false: propext, Quot.sound
TCSlib.Cryptography.bitCom_true: propext, Quot.sound
TCSlib.Cryptography.bitCom_false_eq_owpGenPRG: propext, Quot.sound
TCSlib.Cryptography.bitCom_inj: propext, Quot.sound
TCSlib.Cryptography.owpCom_eq_pairTuple: Quot.sound
TCSlib.Cryptography.owpCom_inj: propext, Quot.sound
TCSlib.Cryptography.owpComLen_eval: propext
TCSlib.Cryptography.owpComStr_pairEncode: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.owpComAt_ofFn: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.owpComStr_ofFn: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.owpComAt_inj: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.owpComStr_binding: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.exists_bitComPredictor: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.HardCore.bitHiding: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.BitHiding.owpComStr_hides: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.owpComStr_polyTimeComputable: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.owp_commitment: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.exists_commitment_of_owp_hardCore: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.exists_commitment_of_owp: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.LevinReduction.polyTimeReducible: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.LevinReduction.refl: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.LevinReduction.trans: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Strategy.coinLen_pullback: propext
TCSlib.Cryptography.Protocol.pullback_outV: propext
TCSlib.Cryptography.Strategy.pullback_efficient: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Protocol.ProverBounded.pullback: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Negligible.comp_of_le: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.LevinReduction.efficientProverProofErr: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.LevinReduction.efficientProverProof: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.LevinReduction.zk: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.zk_proof_of_levinReduction: propext, sorryAx, Classical.choice, Quot.sound
TCSlib.Cryptography.zk_proof_of_owp_levinReduction: propext, sorryAx, Classical.choice, Quot.sound
TCSlib.Cryptography.exists_commitment_zk_proof_of_owp_levinReduction: propext,  sorryAx,  Classical.choice,  Quot.sound
TCSlib.Cryptography.one_sub_inv_add_half_pow_lt_one: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.zk_proof_of_witnessRelation: propext, sorryAx, Classical.choice, Quot.sound
TCSlib.Cryptography.zk_proof_of_witnessRelation_of_owp: propext,  sorryAx,  Classical.choice,  Quot.sound
TCSlib.Cryptography.zk_proof_of_mem_NP: propext, sorryAx, Classical.choice, Quot.sound
TCSlib.Cryptography.zk_proof_of_mem_NP_of_owp: propext, sorryAx, Classical.choice, Quot.sound

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence/e2/admissions.txt =====

# declarations with `sorry` in pack 03e2's files, at e79397eaf68b156b9db091f464741f6eb75b9c28

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence/e2/lint.log =====

# scripts/style_lint.py on pack 03e2's files, at e79397eaf68b156b9db091f464741f6eb75b9c28






0 findings in 5 files

## ===== TCSlib/Cryptography/ZeroKnowledge/Interaction.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.Randomized.PPT
import TCSlib.Complexity.ClassNP.PolyTimePairing
import TCSlib.Cryptography.Foundations.Probability

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Interactive protocols: strategies, executions, views

The interaction model of [PS10, §4.4] in the form frozen by the campaign's foundation
decision D8 (`briefs/pass-shelat/DESIGN.md` §2.15). An interactive machine is a *next-message
strategy* `next x z r received`: given the common input `x`, the auxiliary input `z`, the
random tape `r` and the messages received so far, it returns the next message to send; its
value on the complete history is the party's output. A protocol is a pair of strategies with
an explicit polynomial number of messages (`rounds : PolyExpr`) and a first mover. The
execution `A_{r₁}(x, z₁) ↔ B_{r₂}(x, z₂)` is the fixed alternation of `rounds.eval |x|` moves
(`exec`), and the four derived objects of the text — the view of each party, the transcript,
and the outputs — are projections of it.

**Deviation (D8, recorded once here for the whole chapter):** no tapes, states or idle
transitions are modelled; "entering the idle state" is returning from `next`; the number of
messages is fixed by the protocol (a party that would halt is modelled as sending `[]`), and the
verifier's verdict is `V.next` on the complete history, so it is always defined. The text's
"a round ends when the active machine halts — in which case the protocol ends" makes the
literal `Pr[out_V = 0]` of [PS10, Definition 116.1] unsatisfiable against a prover that halts
at once; the fixed-alternation reading is the one under which that clause is satisfiable.
Verdict convention (run-3 audit P9-3): when the verifier is the last mover, the verdict
activation has exactly the arguments of the activation that produced its last message, so its
last message *is* its verdict (`Protocol.outV_eq_getLast_of_moverIsV`); the chapter's protocols
are stated with the prover moving last, and the `n`-fold protocols read the verifier's last
message as the verdict.
Repetition convention (gate 03e, note 8): an iteration with an odd number of messages (prover,
verifier, prover) is repeated under strict alternation by appending one dummy empty verifier
message to each iteration, so that every iteration starts with the prover; the fourth move of
`giProtocolRep` and of `colProtocolRep`, and the filler moves of the sequential repetition of
[PS10, §7.2.1] in ch. 7, follow this convention.
`Strategy.Efficient` ([PS10, §4.4], time complexity of an interactive machine) is one
activation of a uniform `Complexity.NUPPT` at parameter `|x|` on `⟨⟨x, z⟩, messages⟩` with the
whole random tape; the time is polynomial in the total input length rather than in `|x|`
alone (the text's bound `t(|x|)`, which holds whatever the messages received, would leave the
simulator's call to `V*` on long auxiliary inputs ill-defined; see D8). Consequently
`Efficient` alone bounds neither a party's work in `|x|` against a counterparty that sends long
messages nor the length of its own messages. The proof systems (`InteractiveProofs.lean`)
therefore add the bound on the honest prover's messages, `Protocol.ProverBounded` (ruling G3-3
of gate 03, the convention of ch. 6: `Efficient` plus polynomially bounded honest messages);
the message-prefix cap `Strategy.ReadsPrefix m` — the strategy depends only on the first
`m(|x|)` bits of each received message, as a time-`t(|x|)` machine of the text necessarily
does — is the text's bound on the reading side, and the class `IP` (`InteractiveProofs.lean`)
requires it of the verifier (run-3 audit P9-1).

## Main definitions

* `TCSlib.Cryptography.Strategy` — a next-message strategy with an explicit coin polynomial
  [PS10, §4.4] (Def-114.a); `Strategy.ofNUPPT`, `Strategy.Efficient` (Def-116.b, the machine
  half), `Strategy.ReadsPrefix` (Def-116.b, the message-prefix cap of the text's bound in `|x|`).
* `TCSlib.Cryptography.exec` — the messages received by each party after `k` moves
  [PS10, §4.4] (Def-115.a).
* `TCSlib.Cryptography.View`, `TCSlib.Cryptography.View.encode` — a party's view
  `(x, z, r, received)` and its string encoding (Def-115.b).
* `TCSlib.Cryptography.Protocol` — two strategies, the number of messages and the first mover
  (Def-114.b); `Protocol.transcriptWith`, `Protocol.transcript` (Def-115.c), `Protocol.outV`,
  `Protocol.outP`, `Strategy.out` (Def-115.d), `Protocol.viewV`, `Protocol.viewP`,
  `Protocol.execution` (Def-115.a/b), `Protocol.withV`.
* `TCSlib.Cryptography.Protocol.ProverBounded` — the honest prover's messages have at most
  `B(|x|)` bits on instances with a witness (Def-116.b, the writing half of the text's bound
  in `|x|`; ruling G3-3).

## Main results

* `TCSlib.Cryptography.exec_length` — after `k` moves exactly `k` messages have been sent.
* `TCSlib.Cryptography.Strategy.ofNUPPT_efficient` — every uniform machine is an efficient
  strategy (non-vacuity of Def-116.b).
* `TCSlib.Cryptography.Strategy.ReadsPrefix.mono`,
  `TCSlib.Cryptography.Strategy.ReadsPrefix.next_congr` — the message-prefix cap is monotone
  in the cap and makes the next message a function of the truncated history.
* `TCSlib.Cryptography.Protocol.outV_eq_getLast_of_moverIsV` — when the verifier is the last
  mover, its last message is its verdict (the verdict convention of D8).
* `TCSlib.Cryptography.Protocol.uprob_outV_eq_uexp`,
  `TCSlib.Cryptography.Protocol.exists_proverCoins_le` — random executions are samplers on the
  product of the two coin spaces (Def-116.a), and a prover's coins may be fixed without
  decreasing any event's probability (the "without loss of generality deterministic `P*`"
  remark of the soundness clause).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.4 Interactive protocols, pp. 114–116.)
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge
  University Press, 2009. (Chapter 8, interactive proofs.)
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-! ### Strategies -/

/-- A next-message strategy [PS10, §4.4] (Def-114.a): `next x z r received` is the message a
party sends on common input `x`, auxiliary input `z` and random tape `r` after having
*received* the listed messages; on the complete history its value is the party's output. The
random tape has the explicit polynomial length `coins.eval |x|`.

**Deviation (D8):** no tapes, states or idle transitions; the output function of the text is
the next-message function on the complete history. -/
structure Strategy where
  /-- The next-message function `(x, z, r, received) ↦ message`. -/
  next : List Bool → List Bool → List Bool → List (List Bool) → List Bool
  /-- The length of the random tape as a polynomial in `|x|`. -/
  coins : PolyExpr

namespace Strategy

/-- The number of random bits of a strategy at common-input length `n`. -/
def coinLen (S : Strategy) (n : ℕ) : ℕ := S.coins.eval n

/-- The random tape of a strategy at common-input length `n`: `coinLen n` uniform bits. -/
abbrev Coins (S : Strategy) (n : ℕ) : Type := Fin (S.coinLen n) → Bool

/-- The string encoding of a list of messages: right-nested `pairEncode` pairs ending in `[]`
(the encoding of the received-messages component of a view, Inf-4.1). -/
def encodeMsgs (h : List (List Bool)) : List Bool := h.foldr pairEncode []

/-- The encoding of the empty history is the empty string. -/
@[simp] theorem encodeMsgs_nil : encodeMsgs [] = [] := rfl

/-- The encoding of `m :: h` is the pair `⟨m, encodeMsgs h⟩`. -/
@[simp] theorem encodeMsgs_cons (m : List Bool) (h : List (List Bool)) :
    encodeMsgs (m :: h) = pairEncode m (encodeMsgs h) := rfl

/-- The first projection of an encoded history is its first message (`[]` when empty). -/
theorem pairFstD_encodeMsgs (h : List (List Bool)) : pairFstD (encodeMsgs h) = h.headD [] := by
  cases h with
  | nil => rfl
  | cons m h => simp

/-- The strategy computed by a machine `A`: one activation at parameter `|x|` on
`⟨⟨x, z⟩, messages⟩` with the whole random tape (`A.runAtL`); the coin polynomial is `A.coins`
[PS10, §4.4, the interactive machine as a Turing machine with a random tape]. -/
def ofNUPPT (A : NUPPT) : Strategy where
  next x z r hist := A.runAtL x.length (pairEncode (pairEncode x z) (encodeMsgs hist)) r
  coins := A.coins

/-- The next-message function of `ofNUPPT A` unfolds to one activation of `A`. -/
theorem ofNUPPT_next (A : NUPPT) (x z r : List Bool) (hist : List (List Bool)) :
    (ofNUPPT A).next x z r hist =
      A.runAtL x.length (pairEncode (pairEncode x z) (encodeMsgs hist)) r := rfl

/-- An efficient strategy, the formal counterpart of the text's PPT interactive machine
[PS10, §4.4, time complexity of an interactive machine] (Def-116.b): the next-message function
is computed by a uniform `NUPPT` with the same coin polynomial, one activation per message at
parameter `|x|` on `⟨⟨x, z⟩, messages⟩` with the whole random tape.

**Deviation (D8):** per-activation time polynomial in the total input length `|x| + |z| +
|messages|` instead of the text's `t(|x|)`, which bounds the running time whatever the
messages received. The number of activations is bounded by the protocol's `rounds`, but the
messages of an unbounded counterparty may be arbitrarily long, so `Efficient` alone does not
bound a party's work in `|x|` (run-3 audit P9-1), nor the length of the messages it writes.
The text's bound is recovered on the reading side by the message-prefix cap `ReadsPrefix m`
(an efficient strategy that reads only `m(|x|)` bits of each message runs in time polynomial
in `|x| + |z|`; the class `IP` requires it of the verifier) and on the writing side, for the
honest prover, by `Protocol.ProverBounded` (its messages have at most `B(|x|)` bits; the proof
systems require it, ruling G3-3 of gate 03). -/
def Efficient (S : Strategy) : Prop :=
  ∃ A : NUPPT, A.Uniform ∧ S.coins = A.coins ∧
    ∀ x z r hist, S.next x z r hist = (ofNUPPT A).next x z r hist

/-- Non-vacuity of `Strategy.Efficient`: the strategy of a uniform machine is efficient. -/
theorem ofNUPPT_efficient (A : NUPPT) (hA : A.Uniform) : (ofNUPPT A).Efficient :=
  ⟨A, hA, rfl, fun _ _ _ _ => rfl⟩

/-- An efficient strategy has the coin polynomial of some uniform machine computing it. -/
theorem Efficient.exists_uniform {S : Strategy} (h : S.Efficient) :
    ∃ A : NUPPT, A.Uniform ∧ S.coins = A.coins := by
  obtain ⟨A, hA, hc, -⟩ := h
  exact ⟨A, hA, hc⟩

/-- A strategy reads at most an `m(|x|)`-bit prefix of each received message [PS10, §4.4, time
complexity: an interactive machine of time complexity `t(|x|)` reads at most `t(|x|)` cells of
its communication tape per activation, "independently of the content of the messages it
receives"] (Def-116.b, the message half of the text's bound in `|x|`): the next-message
function is unchanged when every received message is truncated to its first `m.eval |x|` bits.
Together with `Efficient` this is the text's PPT interactive machine — the activation is
computed in time polynomial in `|x| + |z| + rounds · m(|x|)` by truncating the messages first —
whereas `Efficient` alone is polynomial in the total message length (D8).

**Repair (run-3 audit P9-1):** added; the class `IP` requires it of the verifier. -/
def ReadsPrefix (S : Strategy) (m : PolyExpr) : Prop :=
  ∀ x z r hist, S.next x z r hist = S.next x z r (hist.map (List.take (m.eval x.length)))

/-- Under a message-prefix cap the next message depends only on the truncated history. -/
theorem ReadsPrefix.next_congr {S : Strategy} {m : PolyExpr} (h : S.ReadsPrefix m)
    {x z r : List Bool} {hist hist' : List (List Bool)}
    (he : hist.map (List.take (m.eval x.length)) = hist'.map (List.take (m.eval x.length))) :
    S.next x z r hist = S.next x z r hist' := by
  rw [h x z r hist, h x z r hist', he]

/-- The message-prefix cap is monotone: a cap `m` implies every pointwise larger cap `m'`
(`List.take_take`: truncating to `m'(|x|)` and then to `m(|x|) ≤ m'(|x|)` bits is truncating to
`m(|x|)` bits). -/
theorem ReadsPrefix.mono {S : Strategy} {m m' : PolyExpr} (h : S.ReadsPrefix m)
    (hle : ∀ n, m.eval n ≤ m'.eval n) : S.ReadsPrefix m' := by
  intro x z r hist
  refine h.next_congr ?_
  rw [List.map_map]
  refine List.map_congr_left fun msg _ => ?_
  simp only [Function.comp_apply, List.take_take, min_eq_left (hle _)]

end Strategy

/-! ### Executions -/

/-- Which party moves at move `k` (0-indexed): the verifier moves at the even positions when
it moves first, at the odd ones otherwise. -/
def moverIsV (vFirst : Bool) (k : ℕ) : Bool :=
  if vFirst then decide (k % 2 = 0) else decide (k % 2 = 1)

/-- With the verifier first, it moves at the even positions. -/
@[simp] theorem moverIsV_true (k : ℕ) : moverIsV true k = decide (k % 2 = 0) := rfl

/-- With the prover first, the verifier moves at the odd positions. -/
@[simp] theorem moverIsV_false (k : ℕ) : moverIsV false k = decide (k % 2 = 1) := rfl

/-- The messages received by `P` and by `V` after `k` moves of the execution
`P_{rP}(x, zP) ↔ V_{rV}(x, zV)` [PS10, §4.4, the execution `A_{r₁}(x, z₁) ↔ B_{r₂}(x, z₂)`]
(Def-115.a): at move `k` the active party applies its next-message function to the messages
it has received so far and the message is appended to the other party's received list. -/
def exec (P V : Strategy) (vFirst : Bool) (x zP zV rP rV : List Bool) :
    ℕ → List (List Bool) × List (List Bool)
  | 0 => ([], [])
  | k + 1 =>
    let e := exec P V vFirst x zP zV rP rV k
    if moverIsV vFirst k then (e.1 ++ [V.next x zV rV e.2], e.2)
    else (e.1, e.2 ++ [P.next x zP rP e.1])

/-- Before the first move nothing has been received. -/
@[simp] theorem exec_zero (P V : Strategy) (vFirst : Bool) (x zP zV rP rV : List Bool) :
    exec P V vFirst x zP zV rP rV 0 = ([], []) := rfl

/-- One more move: the active party's message is appended to the other party's list. -/
theorem exec_succ (P V : Strategy) (vFirst : Bool) (x zP zV rP rV : List Bool) (k : ℕ) :
    exec P V vFirst x zP zV rP rV (k + 1) =
      (let e := exec P V vFirst x zP zV rP rV k
       if moverIsV vFirst k then (e.1 ++ [V.next x zV rV e.2], e.2)
       else (e.1, e.2 ++ [P.next x zP rP e.1])) := rfl

/-- After `k` moves exactly `k` messages have been sent in total. -/
theorem exec_length (P V : Strategy) (vFirst : Bool) (x zP zV rP rV : List Bool) (k : ℕ) :
    (exec P V vFirst x zP zV rP rV k).1.length + (exec P V vFirst x zP zV rP rV k).2.length = k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [exec_succ]
    split_ifs <;> simp only [List.length_append, List.length_singleton] <;> omega

/-! ### Views -/

/-- A party's view [PS10, §4.4] (Def-115.b): the common input, its auxiliary input, its random
tape and the messages it received. -/
structure View where
  /-- The common input. -/
  x : List Bool
  /-- The party's auxiliary input. -/
  z : List Bool
  /-- The party's random tape. -/
  r : List Bool
  /-- The messages the party received, in order. -/
  received : List (List Bool)

/-- The string encoding of a view, `⟨⟨x, z⟩, ⟨r, messages⟩⟩` (the sample handed to
distinguishers and produced by simulators in the zero-knowledge definitions). -/
def View.encode (v : View) : List Bool :=
  pairEncode (pairEncode v.x v.z) (pairEncode v.r (Strategy.encodeMsgs v.received))

/-- The output of a party on a view [PS10, §4.4, `out(v)`] (Def-115.d): its next-message
function on the complete history. -/
def Strategy.out (S : Strategy) (v : View) : List Bool := S.next v.x v.z v.r v.received

/-! ### Protocols -/

/-- A protocol [PS10, §4.4] (Def-114.b): a prover strategy, a verifier strategy, the number of
messages exchanged (an explicit polynomial in `|x|`) and the first mover (`true` = verifier
first, as in the graph non-isomorphism protocol; `false` = prover first, as in the graph
isomorphism and 3-colouring protocols). The verifier's verdict is its next-message function
on the complete history.

**Deviation (D8):** fixed number of messages `rounds.eval |x|`; a halting party sends `[]`.
If the verifier is the last mover (prover first with an even number of messages, or verifier
first with an odd number), its last message coincides with its verdict — both are `V.next` on
the same history (`outV_eq_getLast_of_moverIsV`) — so a verifier whose final message differs
from its verdict is not expressible; protocols are therefore stated so that the prover moves
last, or the verifier's last message is read as the verdict (the `n`-fold protocols)
(run-3 audit P9-3). -/
structure Protocol where
  /-- The prover's strategy. -/
  P : Strategy
  /-- The verifier's strategy. -/
  V : Strategy
  /-- The number of messages exchanged, as a polynomial in `|x|`. -/
  rounds : PolyExpr
  /-- Whether the verifier sends the first message. -/
  verifierFirst : Bool

namespace Protocol

/-- The joint coin space of an execution of `π` with the prover strategy `P'` on `x`: the
prover's and the verifier's random tapes at parameter `|x|` [PS10, §4.4, random executions]
(Def-116.a). -/
abbrev ExecCoins (π : Protocol) (P' : Strategy) (x : List Bool) : Type :=
  P'.Coins x.length × π.V.Coins x.length

/-- **The honest prover's messages are short** with respect to the witness relation `R` and
the polynomial `B` [PS10, §4.4, time complexity: a machine of time complexity `t(|x|)` halts
within `t(|x|)` steps whatever it receives, so each of its messages has at most `t(|x|)` bits]:
on every instance `x` with a witness `y` (`R x y`), whatever its random tape and whatever it
has received, the honest prover's message has at most `B(|x|)` bits.

**Deviation (D8; ruling G3-3 of gate 03, the convention of ch. 6):** `Strategy.Efficient`
bounds a party's work, hence its messages, only in the total length of its input, which
contains the messages it has received; the bound in `|x|` is this separate condition, a field
of `EfficientProverProof` (and, for the completeness witness, part of the completeness clause
of `InteractiveProof`). Without it an honest prover that echoes the verifier's messages —
zero-knowledge for one run — lets a cheating verifier that doubles its messages build a view
of length `2^{rounds}`, which the composition theorems of ch. 7 cannot simulate. -/
def ProverBounded (π : Protocol) (R : List Bool → List Bool → Prop) (B : PolyExpr) : Prop :=
  ∀ x y r hist, R x y → (π.P.next x y r hist).length ≤ B.eval x.length

/-- A message bound `B` implies every pointwise larger bound `B'`. -/
theorem ProverBounded.mono {π : Protocol} {R : List Bool → List Bool → Prop} {B B' : PolyExpr}
    (h : π.ProverBounded R B) (hle : ∀ n, B.eval n ≤ B'.eval n) : π.ProverBounded R B' :=
  fun x y r hist hxy => (h x y r hist hxy).trans (hle _)

/-- The protocol with the verifier replaced by `V'` (the cheating verifier `V*` of the
zero-knowledge definitions), same prover, round count and first mover. -/
def withV (π : Protocol) (V' : Strategy) : Protocol := { π with V := V' }

/-- The verifier of `π.withV V'` is `V'`. -/
@[simp] theorem withV_V (π : Protocol) (V' : Strategy) : (π.withV V').V = V' := rfl

/-- The prover of `π.withV V'` is the prover of `π`. -/
@[simp] theorem withV_P (π : Protocol) (V' : Strategy) : (π.withV V').P = π.P := rfl

/-- The round count of `π.withV V'` is that of `π`. -/
@[simp] theorem withV_rounds (π : Protocol) (V' : Strategy) : (π.withV V').rounds = π.rounds := rfl

/-- The first mover of `π.withV V'` is that of `π`. -/
@[simp] theorem withV_verifierFirst (π : Protocol) (V' : Strategy) :
    (π.withV V').verifierFirst = π.verifierFirst := rfl

/-- Replacing the verifier by itself changes nothing. -/
@[simp] theorem withV_self (π : Protocol) : π.withV π.V = π := by
  cases π
  rfl

/-- The transcript (messages received by `P'`, messages received by `V`) of the execution
`P'_{r₁}(x, y) ↔ V_{r₂}(x, z)` with all `rounds.eval |x|` moves [PS10, §4.4] (Def-115.c). -/
def transcriptWith (π : Protocol) (P' : Strategy) (x y z : List Bool) (r : π.ExecCoins P' x) :
    List (List Bool) × List (List Bool) :=
  exec P' π.V π.verifierFirst x y z (List.ofFn r.1) (List.ofFn r.2) (π.rounds.eval x.length)

/-- The transcript of the honest execution `P(x, y) ↔ V(x, z)` (Def-115.c). -/
def transcript (π : Protocol) (x y z : List Bool) (r : π.ExecCoins π.P x) :
    List (List Bool) × List (List Bool) :=
  π.transcriptWith π.P x y z r

/-- The verifier's output in `P'_{r₁}(x, y) ↔ V_{r₂}(x, z)` [PS10, §4.4, `out_V`] (Def-115.d):
`V.next` on the complete history.

**Deviation (D8, run-3 audit P9-3):** when the verifier is the last mover this is also the
last message it sent (`outV_eq_getLast_of_moverIsV`); see `Protocol`. -/
def outV (π : Protocol) (P' : Strategy) (x y z : List Bool) (r : π.ExecCoins P' x) : List Bool :=
  π.V.next x z (List.ofFn r.2) (π.transcriptWith P' x y z r).2

/-- The honest prover's output in `P_{r₁}(x, y) ↔ V_{r₂}(x, z)` (Def-115.d). -/
def outP (π : Protocol) (x y z : List Bool) (r : π.ExecCoins π.P x) : List Bool :=
  π.P.next x y (List.ofFn r.1) (π.transcriptWith π.P x y z r).1

/-- The honest verifier's view of `P_{r₁}(x, y) ↔ V_{r₂}(x, z)` [PS10, §4.4, `view_V`]
(Def-115.b). -/
def viewV (π : Protocol) (x y z : List Bool) (r : π.ExecCoins π.P x) : View :=
  ⟨x, z, List.ofFn r.2, (π.transcriptWith π.P x y z r).2⟩

/-- The honest prover's view of `P_{r₁}(x, y) ↔ V_{r₂}(x, z)` [PS10, §4.4, `view_P`]
(Def-115.b). -/
def viewP (π : Protocol) (x y z : List Bool) (r : π.ExecCoins π.P x) : View :=
  ⟨x, y, List.ofFn r.1, (π.transcriptWith π.P x y z r).1⟩

/-- The execution `P_{r₁}(x, y) ↔ V_{r₂}(x, z)` as the pair of views (the joint view)
[PS10, §4.4] (Def-115.a). -/
def execution (π : Protocol) (x y z : List Bool) (r : π.ExecCoins π.P x) : View × View :=
  (π.viewP x y z r, π.viewV x y z r)

/-- The verifier's output is its output function on its view (Def-115.d). -/
theorem outV_eq_out (π : Protocol) (x y z : List Bool) (r : π.ExecCoins π.P x) :
    π.outV π.P x y z r = π.V.out (π.viewV x y z r) := rfl

/-- The prover's output is its output function on its view (Def-115.d). -/
theorem outP_eq_out (π : Protocol) (x y z : List Bool) (r : π.ExecCoins π.P x) :
    π.outP x y z r = π.P.out (π.viewP x y z r) := rfl

/-- The transcript is the pair of received-message components of the two views. -/
theorem transcript_eq (π : Protocol) (x y z : List Bool) (r : π.ExecCoins π.P x) :
    π.transcript x y z r = ((π.viewP x y z r).received, (π.viewV x y z r).received) := rfl

/-- The verifier's output against `P'` only depends on `P'` through the transcript. -/
theorem outV_withV (π : Protocol) (V' P' : Strategy) (x y z : List Bool)
    (r : (π.withV V').ExecCoins P' x) :
    (π.withV V').outV P' x y z r =
      V'.next x z (List.ofFn r.2)
        (exec P' V' π.verifierFirst x y z (List.ofFn r.1) (List.ofFn r.2)
          (π.rounds.eval x.length)).2 := rfl

/-- The verdict convention of D8 made explicit (run-3 audit P9-3): if the verifier makes the
last of the `k + 1` moves (`moverIsV verifierFirst k`), the last message it sent — the last
message `P'` received — is its verdict, because both are `V.next` on the messages `V` received
in the first `k` moves (`exec_succ`, `List.getLast?_concat`). -/
theorem outV_eq_getLast_of_moverIsV (π : Protocol) (P' : Strategy) (x y z : List Bool)
    (r : π.ExecCoins P' x) {k : ℕ} (hk : π.rounds.eval x.length = k + 1)
    (hV : moverIsV π.verifierFirst k = true) :
    (π.transcriptWith P' x y z r).1.getLast? = some (π.outV P' x y z r) := by
  unfold outV transcriptWith
  rw [hk, exec_succ]
  simp [hV]

/-! ### Random executions -/

/-- A random execution is a sampler on the product of the two coin spaces [PS10, §4.4]
(Def-116.a): the probability of any event of the verifier's output is the average over the
prover's coins of its conditional probability over the verifier's coins (`uprob_prod`). -/
theorem uprob_outV_eq_uexp (π : Protocol) (P' : Strategy) (x y z : List Bool)
    (p : List Bool → Prop) :
    uprob (fun r : π.ExecCoins P' x => p (π.outV P' x y z r)) =
      uexp (fun r₁ : P'.Coins x.length =>
        uprob (fun r₂ : π.V.Coins x.length => p (π.outV P' x y z (r₁, r₂)))) :=
  uprob_prod _

/-- A cheating prover may be taken deterministic: for every event of the verifier's output
there is a fixed prover random tape under which the event is at least as likely as on average
(the "without loss of generality `P*` is deterministic" remark behind the soundness clause of
[PS10, Definition 116.1]). -/
theorem exists_proverCoins_le (π : Protocol) (P' : Strategy) (x y z : List Bool)
    (p : List Bool → Prop) :
    ∃ r₁ : P'.Coins x.length,
      uprob (fun r : π.ExecCoins P' x => p (π.outV P' x y z r)) ≤
        uprob (fun r₂ : π.V.Coins x.length => p (π.outV P' x y z (r₁, r₂))) := by
  rw [uprob_outV_eq_uexp]
  set f : P'.Coins x.length → ℝ :=
    fun r₁ => uprob (fun r₂ : π.V.Coins x.length => p (π.outV P' x y z (r₁, r₂)))
  have hcard : (0 : ℝ) < Fintype.card (P'.Coins x.length) := by
    exact_mod_cast Fintype.card_pos
  have hsum : ∑ _a : P'.Coins x.length, uexp f ≤ ∑ a, f a := by
    rw [sum_const, card_univ, nsmul_eq_mul, uexp, mul_div_cancel₀ _ hcard.ne']
  obtain ⟨a, -, ha⟩ := exists_le_of_sum_le univ_nonempty hsum
  exact ⟨a, ha⟩

end Protocol

end TCSlib.Cryptography

## ===== TCSlib/Cryptography/ZeroKnowledge/InteractiveProofs.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.Interaction
import TCSlib.Cryptography.Foundations.Negligible
import TCSlib.Cryptography.HardcoreBit.Basic
import TCSlib.Complexity.ClassNP.NP
import TCSlib.Complexity.ClassNP.PClosure
import TCSlib.Complexity.Randomized.Primitives

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Interactive proof systems

The definitions of [PS10, §4.5] on top of the interaction model of `Interaction.lean`
(foundation decision D8): interactive proofs with negligible soundness error
[PS10, Definition 116.1], proofs with a stated soundness error `s(|x|)` [PS10, §4.5,
constant-error proofs], witness relations [PS10, Appendix B, Definition 191.11], and
interactive proofs with an efficient prover [PS10, Definition 119.5]. The sanity theorem
`npProtocol_interactiveProof` shows the definitions are satisfiable: the one-message protocol
in which the prover sends a witness (read by the verifier up to the relation's witness-length
bound) is an interactive proof with efficient prover for every polynomially decidable witness
relation, and `WitnessRelation.mem_IP`, `NP_subset_IP` place such languages in the class `IP`
([PS10, §4.5, the remark `NP ⊆ IP`]).

**Deviation (D8):** soundness is the literal `1 - ε(|x|) < Pr[out_V = 0]` with `out_V = 0`
read as the output string `[false]`, the negligible `ε` quantified before the instance, the
cheating prover and its auxiliary input; cheating provers are arbitrary strategies with a
polynomial random tape (unbounded computation; polynomial coin tapes lose nothing by
averaging, `Protocol.exists_proverCoins_le`). Completeness is `uprob = 1`, i.e. acceptance on
every pair of random tapes. The parties' efficiency (the text's "p.p.t.") is
`Strategy.Efficient`, polynomial time in `|x| + |z| + |messages|` (D8), together with a
polynomial bound `B(|x|)` on the honest prover's messages (ruling G3-3 of gate 03, the
convention of ch. 6): in the completeness clause of `InteractiveProof` and
`InteractiveProofErr` for the completeness witness, and as the field `boundedP`
(`Protocol.ProverBounded`) of `EfficientProverProof` and `EfficientProverProofErr` for every
witness. The residual deviation is that against a cheating prover the verifier's work is
polynomial in the length of the messages it receives, not in `|x|`. Since the honest messages
are short, the verifier can always be capped: `V` reading only the first `B(|x|)` bits of each
message is still complete (the honest messages are untouched) and sound (against `P*` it acts
as `V` against `P*` with truncated messages, another prover strategy). So the proof systems
hold only for languages of the text's class IP — undecidable languages such as the halting
problem, whose computation histories are not polynomially bounded, are excluded — while
`IP` itself is stated with the message-prefix cap `Strategy.ReadsPrefix` of the verifier
(run-3 audit P9-1). The capping argument is not formalized as a lemma.

## Main definitions

* `TCSlib.Cryptography.InteractiveProof` — interactive proof system [PS10, Definition 116.1]
  (Def-116.1); `TCSlib.Cryptography.InteractiveProofErr` — with soundness error `s` (Def-117.a);
  `TCSlib.Cryptography.IP` — the class of languages with an interactive proof whose verifier
  reads a polynomial prefix of each message (Def-117.b).
* `TCSlib.Cryptography.WitnessRelation` — a witness relation for a language
  [PS10, Definition 191.11] (Def-191.11); `TCSlib.Cryptography.witnessLanguage`,
  `TCSlib.Cryptography.witnessSet` — the language `{x | ∃ y, R x y}` and the set `R_L(x)`.
* `TCSlib.Cryptography.EfficientProverProof`,
  `TCSlib.Cryptography.EfficientProverProofErr` — interactive proofs with efficient prover
  [PS10, Definition 119.5] (Def-119.5).
* `TCSlib.Cryptography.npProtocol` — the one-message protocol in which the prover sends a
  witness, read by the verifier up to a polynomial length bound.

## Main results

* `TCSlib.Cryptography.InteractiveProofErr.interactiveProof`,
  `TCSlib.Cryptography.InteractiveProof.exists_err` — a negligible soundness error gives an
  interactive proof and conversely.
* `TCSlib.Cryptography.InteractiveProof.exists_accept`,
  `TCSlib.Cryptography.Protocol.ProverBounded.exists_complete` — completeness without the
  message bound, and completeness with the bound from bounded messages and completeness for
  every witness.
* `TCSlib.Cryptography.InteractiveProof.exists_uprob_accept_lt` — the acceptance form of
  soundness, `Pr[out_V = [true]] < ε(|x|)`.
* `TCSlib.Cryptography.WitnessRelation.mem_NP`,
  `TCSlib.Cryptography.exists_witnessRelation_of_mem_NP` — witness relations characterize
  `Complexity.NP` (the bridge to the certificate definition of `ClassNP/NP.lean`).
* `TCSlib.Cryptography.npProtocol_interactiveProof` — non-vacuity: sending a witness is an
  interactive proof with efficient prover (`TCSlib.Cryptography.npProtocol_proverBounded`: its
  prover's message is the witness); `TCSlib.Cryptography.npProtocol_readsPrefix`,
  `TCSlib.Cryptography.WitnessRelation.mem_IP`, `TCSlib.Cryptography.NP_subset_IP` — its
  verifier reads a polynomial prefix, hence `NP ⊆ IP` (Claim-117.c).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.5 Interactive proofs, pp. 116–120; Appendix B, Definition 191.11.)
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge
  University Press, 2009. (Definition 2.1, NP via certificates; Chapter 8.)
-/

namespace TCSlib.Cryptography

open Complexity Turing

/-! ### Interactive proofs -/

/-- An interactive proof system for `L` [PS10, Definition 116.1] (Def-116.1): the verifier is
efficient; completeness — for a polynomial `B` and every `x ∈ L` there is an auxiliary input
`y` on which the honest prover's messages have at most `B(|x|)` bits and such that for every
`z` the honest execution `P(x, y) ↔ V(x, z)` makes `V` output `1` with probability one;
soundness — there is a negligible `ε` such that for every `x ∉ L`, every (unbounded) prover
strategy `P'` and every `z`, `V` outputs `0` in `P'(x) ↔ V(x, z)` with probability greater than
`1 - ε(|x|)`.

**Deviation (D8; ruling G3-3 of gate 03):** `out_V = 0` is the literal output string `[false]`
on the complete history of the fixed-alternation execution; `P'` ranges over strategies with
polynomial random tapes and receives no auxiliary input (the text's `P*(x)`); completeness is
`uprob = 1` (every pair of random tapes). The verifier's "p.p.t." is `Strategy.Efficient`,
polynomial-time in `|x| + |z| + |messages|` (D8), and the honest messages on the completeness
witness are bounded by `B(|x|)` (the text's p.p.t. prover writes at most `t(|x|)` bits; the
convention of ch. 6). Against a cheating prover the verifier's work is polynomial in the
length of the messages it receives, not in `|x|`; because the honest messages are short the
verifier can be capped to their length without losing completeness or soundness (module
docstring), so the predicate holds only for languages of the text's class IP. The class `IP`
is stated with the message-prefix cap `Strategy.ReadsPrefix` (run-3 audit P9-1). -/
structure InteractiveProof (π : Protocol) (L : Language Bool) : Prop where
  /-- The verifier is efficient (`Strategy.Efficient`, D8). -/
  efficientV : π.V.Efficient
  /-- Completeness: for a polynomial `B`, every `x ∈ L` has an auxiliary input on which the
  honest prover's messages have at most `B(|x|)` bits and the honest verifier accepts with
  probability one. -/
  complete : ∃ B : PolyExpr, ∀ x ∈ L, ∃ y : List Bool,
    (∀ r hist, (π.P.next x y r hist).length ≤ B.eval x.length) ∧
    ∀ z : List Bool, uprob (fun r : π.ExecCoins π.P x => π.outV π.P x y z r = [true]) = 1
  /-- Soundness: against every prover strategy the verifier rejects with probability
  `> 1 - ε(|x|)` for a negligible `ε`. -/
  sound : ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ x ∉ L, ∀ (P' : Strategy) (z : List Bool),
    1 - ε x.length < uprob (fun r : π.ExecCoins P' x => π.outV P' x [] z r = [false])

/-- An interactive proof system with soundness error `s` [PS10, §4.5, after Definition 116.1]
(Def-117.a): as `InteractiveProof` with `1 - s(|x|) ≤ Pr[out_V = [false]]` for the given
function `s` (for instance the constant `1/2` of the single-iteration graph-isomorphism
protocol).

**Deviation (D8; ruling G3-3 of gate 03):** as for `InteractiveProof` (literal `[false]`,
provers with polynomial tapes, `uprob = 1` completeness with honest messages of at most
`B(|x|)` bits; verifier time in the total input length — the message-prefix cap is added in
`IP`, run-3 audit P9-1). -/
structure InteractiveProofErr (π : Protocol) (L : Language Bool) (s : ℕ → ℝ) : Prop where
  /-- The verifier is efficient (`Strategy.Efficient`, D8). -/
  efficientV : π.V.Efficient
  /-- Completeness: for a polynomial `B`, every `x ∈ L` has an auxiliary input on which the
  honest prover's messages have at most `B(|x|)` bits and the honest verifier accepts with
  probability one. -/
  complete : ∃ B : PolyExpr, ∀ x ∈ L, ∃ y : List Bool,
    (∀ r hist, (π.P.next x y r hist).length ≤ B.eval x.length) ∧
    ∀ z : List Bool, uprob (fun r : π.ExecCoins π.P x => π.outV π.P x y z r = [true]) = 1
  /-- Soundness error `s`: the verifier rejects with probability at least `1 - s(|x|)`. -/
  sound : ∀ x ∉ L, ∀ (P' : Strategy) (z : List Bool),
    1 - s x.length ≤ uprob (fun r : π.ExecCoins P' x => π.outV P' x [] z r = [false])

/-- The class `IP` of languages with an interactive proof system [PS10, §4.5] (Def-117.b):
`L ∈ IP` iff some protocol `π` is an interactive proof for `L` whose verifier reads only a
polynomial prefix `m(|x|)` of each received message (`Strategy.ReadsPrefix`), as a verifier of
time complexity `t(|x|)` in the sense of the text necessarily does.

**Repair (run-3 audit P9-1):** the run-2 definition `∃ π, InteractiveProof π L` contained every
language `{x | ∃ y, T ⟨x, y⟩ = true}` with `T` polynomial-time on the pair and no bound on
`|y|` (all of RE, by computation-history checkers): under D8 the verifier's time is polynomial
in the total input including the messages, so an unbounded prover could hand it an arbitrarily
long certificate. With the cap the verifier's work is polynomial in `|x| + |z|`, as in the
text; `WitnessRelation.mem_IP` recovers `NP ⊆ IP`. -/
def IP : Set (Language Bool) :=
  {L | ∃ (π : Protocol) (m : PolyExpr), π.V.ReadsPrefix m ∧ InteractiveProof π L}

/-- A negligible soundness error gives an interactive proof: the strict clause holds with the
negligible function `ε n := s n + 2⁻¹ ^ n`. -/
theorem InteractiveProofErr.interactiveProof {π : Protocol} {L : Language Bool} {s : ℕ → ℝ}
    (hs : Negligible s) (h : InteractiveProofErr π L s) : InteractiveProof π L where
  efficientV := h.efficientV
  complete := h.complete
  sound := by
    refine ⟨fun n => s n + (2 : ℝ)⁻¹ ^ n, hs.add negligible_two_pow_neg, fun x hx P' z => ?_⟩
    have hpos : (0 : ℝ) < (2 : ℝ)⁻¹ ^ x.length := by positivity
    linarith [h.sound x hx P' z]

/-- An interactive proof has a negligible soundness error. -/
theorem InteractiveProof.exists_err {π : Protocol} {L : Language Bool}
    (h : InteractiveProof π L) : ∃ ε : ℕ → ℝ, Negligible ε ∧ InteractiveProofErr π L ε := by
  obtain ⟨ε, hε, hsound⟩ := h.sound
  exact ⟨ε, hε, h.efficientV, h.complete, fun x hx P' z => (hsound x hx P' z).le⟩

/-- Soundness in the acceptance form: for `x ∉ L` the verifier accepts (outputs `[true]`) with
probability less than `ε(|x|)` (the form the inventory records as equivalent; the event
`out_V = [true]` is contained in `out_V ≠ [false]`). -/
theorem InteractiveProof.exists_uprob_accept_lt {π : Protocol} {L : Language Bool}
    (h : InteractiveProof π L) : ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ x ∉ L, ∀ (P' : Strategy) (z : List Bool),
        uprob (fun r : π.ExecCoins P' x => π.outV P' x [] z r = [true]) < ε x.length := by
  obtain ⟨ε, hε, hsound⟩ := h.sound
  refine ⟨ε, hε, fun x hx P' z => ?_⟩
  have h1 := hsound x hx P' z
  have h2 : uprob (fun r : π.ExecCoins P' x => π.outV P' x [] z r = [true]) ≤
      uprob (fun r : π.ExecCoins P' x => ¬ π.outV P' x [] z r = [false]) :=
    uprob_mono fun r hr => by simp [hr]
  rw [uprob_not] at h2
  linarith

/-- Completeness without the message bound (the form in which consumers use it): every
`x ∈ L` has an auxiliary input on which the honest verifier accepts with probability one. -/
theorem InteractiveProof.exists_accept {π : Protocol} {L : Language Bool}
    (h : InteractiveProof π L) : ∀ x ∈ L, ∃ y : List Bool, ∀ z : List Bool,
      uprob (fun r : π.ExecCoins π.P x => π.outV π.P x y z r = [true]) = 1 := fun x hx =>
  let ⟨_, hB⟩ := h.complete
  let ⟨y, _, hy⟩ := hB x hx
  ⟨y, hy⟩

/-- Completeness without the message bound, for an interactive proof with soundness error. -/
theorem InteractiveProofErr.exists_accept {π : Protocol} {L : Language Bool} {s : ℕ → ℝ}
    (h : InteractiveProofErr π L s) : ∀ x ∈ L, ∃ y : List Bool, ∀ z : List Bool,
      uprob (fun r : π.ExecCoins π.P x => π.outV π.P x y z r = [true]) = 1 := fun x hx =>
  let ⟨_, hB⟩ := h.complete
  let ⟨y, _, hy⟩ := hB x hx
  ⟨y, hy⟩

/-- The completeness clause of `InteractiveProof` from bounded honest messages: if the honest
prover's messages have at most `B(|x|)` bits on instances with an `R`-witness
(`Protocol.ProverBounded`), every witness makes the honest verifier accept with probability
one, and every `x ∈ L` has a witness, then the clause holds with the bound `B` and the
witnesses as auxiliary inputs. -/
theorem Protocol.ProverBounded.exists_complete {π : Protocol} {L : Language Bool}
    {R : List Bool → List Bool → Prop} {B : PolyExpr} (hB : π.ProverBounded R B)
    (hLR : ∀ x ∈ L, ∃ y, R x y)
    (hc : ∀ x y, R x y → ∀ z : List Bool,
      uprob (fun r : π.ExecCoins π.P x => π.outV π.P x y z r = [true]) = 1) :
    ∃ B : PolyExpr, ∀ x ∈ L, ∃ y : List Bool,
      (∀ r hist, (π.P.next x y r hist).length ≤ B.eval x.length) ∧
      ∀ z : List Bool, uprob (fun r : π.ExecCoins π.P x => π.outV π.P x y z r = [true]) = 1 :=
  ⟨B, fun x hx =>
    let ⟨y, hy⟩ := hLR x hx
    ⟨y, fun r hist => hB x y r hist hy, hc x y hy⟩⟩

/-! ### Witness relations -/

/-- A witness relation for `L` [PS10, Appendix B, Definition 191.11] (Def-191.11): `x ∈ L` iff
some `y` satisfies `R x y`; witnesses have polynomially bounded length; and the relation is
decidable in polynomial time on the pair `⟨x, y⟩`.

**Deviation:** the text's `R_L(x) = {y : (x, y) ∈ L}` is a typo for `∈ R_L`; the witness-length
bound is an explicit `PolyExpr` and the decider a polynomial-time string function
(`PolyTimeComputable`). The bound is on the relation itself (every `y` with `R x y` is short),
whereas Definition 191.11 bounds only the witnesses that count (`∃ y, |y| ≤ p(|x|) ∧
(x, y) ∈ R_L`); the two agree on languages (intersect `R_L` with the bound), and the bounded
form suits Definition 119.5's "for every `y ∈ R_L(x)`", since a time-`t(|x|)` prover cannot
read a longer `y` (gate 03e, note 11). -/
structure WitnessRelation (L : Language Bool) (R : List Bool → List Bool → Prop) : Prop where
  /-- `x ∈ L` iff `x` has a witness. -/
  mem_iff : ∀ x, x ∈ L ↔ ∃ y, R x y
  /-- Witnesses have length bounded by a polynomial in `|x|`. -/
  bounded : ∃ p : PolyExpr, ∀ x y, R x y → y.length ≤ p.eval x.length
  /-- The relation is decidable in polynomial time on `⟨x, y⟩`. -/
  decidable : ∃ T : List Bool → Bool, PolyTimeComputable (fun z => [T z]) ∧
    ∀ x y, T (pairEncode x y) = true ↔ R x y

/-- The language of a relation, `{x | ∃ y, R x y}` [PS10, Definition 191.11]. -/
def witnessLanguage (R : List Bool → List Bool → Prop) : Language Bool := {x | ∃ y, R x y}

/-- The witness set `R_L(x) = {y | R x y}` [PS10, Definition 191.11]. -/
def witnessSet (R : List Bool → List Bool → Prop) (x : List Bool) : Set (List Bool) := {y | R x y}

/-- Membership in `witnessLanguage R` unfolds to the existence of a witness. -/
@[simp] theorem mem_witnessLanguage (R : List Bool → List Bool → Prop) (x : List Bool) :
    x ∈ witnessLanguage R ↔ ∃ y, R x y := Iff.rfl

/-- Membership in `witnessSet R x` unfolds to `R x y`. -/
@[simp] theorem mem_witnessSet (R : List Bool → List Bool → Prop) (x y : List Bool) :
    y ∈ witnessSet R x ↔ R x y := Iff.rfl

/-- A witness relation for `L` determines `L` as `witnessLanguage R`. -/
theorem WitnessRelation.eq_witnessLanguage {L : Language Bool} {R : List Bool → List Bool → Prop}
    (h : WitnessRelation L R) : L = witnessLanguage R :=
  Set.ext fun x => h.mem_iff x

/-- A language with a witness relation is in `NP` [PS10, Definition 191.11, the "iff" with
[AB09, Definition 2.1]].

**Proof sketch.** Use `Complexity.mem_NP_iff_exists_length_le` (the `pairEncode x u ∈ V`,
`|u| ≤ C(|x|+1)^c` form). From `h.bounded` take `p` and `C, c` with `p.eval n ≤ C(n+1)^c`
(`PolyExpr.eval_le`). From `h.decidable` take `T`; the verifier language is
`V := {z | T z = true}`, in `P` by `Complexity.mem_P_iff_polyTimeComputable` since
`[MultiTapeTM.indicator V z] = [T z]` (`funext`, `Bool.decide_eq_true`). The equivalence
`x ∈ L ↔ ∃ u, |u| ≤ C(|x|+1)^c ∧ pairEncode x u ∈ V` is `h.mem_iff`, the length bound and
the decider's specification. -/
theorem WitnessRelation.mem_NP {L : Language Bool} {R : List Bool → List Bool → Prop}
    (h : WitnessRelation L R) : L ∈ NP := by
  rw [mem_NP_iff_exists_length_le]
  obtain ⟨p, hp⟩ := h.bounded
  obtain ⟨C, c, hCc⟩ := p.eval_le
  obtain ⟨T, hT, hTR⟩ := h.decidable
  refine ⟨C, c, {z | T z = true}, mem_P_of_test hT, fun x => ?_⟩
  rw [h.mem_iff x]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, (hp x y hy).trans (hCc _), (hTR x y).2 hy⟩
  · rintro ⟨u, -, hu⟩
    exact ⟨u, (hTR x u).1 hu⟩

/-- Every `NP` language has a witness relation [PS10, Definition 191.11, converse direction].

**Proof sketch.** From `Complexity.mem_NP_iff_exists_length_le` take `C, c, V`; set
`R x y := y.length ≤ C * (x.length + 1) ^ c ∧ pairEncode x y ∈ V`. `mem_iff` is the
characterization; `bounded` is `PolyExpr.normal C c` (`PolyExpr.eval_normal`); `decidable`:
`T z := decide ((pairSndD z).length ≤ C * ((pairFstD z).length + 1) ^ c) && indicator V z`,
polynomial-time by `Complexity.polyTimeComputable_and`, `polyTimeComputable_lenLe` composed
with `pairEncode (unaryPoly (normal C c) ∘ pairFstD) pairSndD`, and
`mem_P_iff_polyTimeComputable`; on `pairEncode x y` the projections are `x` and `y`
(`pairFstD_pairEncode`, `pairSndD_pairEncode`). -/
theorem exists_witnessRelation_of_mem_NP {L : Language Bool} (h : L ∈ NP) :
    ∃ R : List Bool → List Bool → Prop, WitnessRelation L R := by
  obtain ⟨C, c, V, hV, hL⟩ := mem_NP_iff_exists_length_le.1 h
  refine ⟨fun x y => y.length ≤ C * (x.length + 1) ^ c ∧ pairEncode x y ∈ V, hL, ?_, ?_⟩
  · exact ⟨PolyExpr.normal C c, fun x y hy => by rw [PolyExpr.eval_normal]; exact hy.1⟩
  · refine ⟨fun z => decide ((pairSndD z).length ≤ C * ((pairFstD z).length + 1) ^ c) &&
      MultiTapeTM.indicator V z, ?_, ?_⟩
    · refine polyTimeComputable_and ?_ (test_of_mem_P hV)
      have hlen := polyTimeComputable_lenLe.comp
        (((polyTimeComputable_unaryPoly (PolyExpr.normal C c)).comp
          polyTimeComputable_pairFstD).pairEncode polyTimeComputable_pairSndD)
      convert hlen using 1
      funext z
      simp [PolyExpr.eval_normal]
    · intro x y
      simp [MultiTapeTM.indicator]

/-! ### Efficient provers -/

/-- An interactive proof for `L` with efficient prover with respect to the witness relation
`R` [PS10, Definition 119.5] (Def-119.5): an interactive proof whose prover is efficient (the
witness is its auxiliary input) and which is complete for **every** witness `y` of `x`
(Definition 116.1 only asks for some auxiliary input).

**Deviation (D8; ruling G3-3 of gate 03):** the text's "P is p.p.t." is `Strategy.Efficient`
(time polynomial in the total input length, D8) together with a polynomial bound `B(|x|)` on
the prover's messages on every instance with a witness (`Protocol.ProverBounded`: the text's
p.p.t. machine writes at most `t(|x|)` bits per message, the convention of ch. 6); the
verifier is as in `InteractiveProof`. -/
structure EfficientProverProof (π : Protocol) (L : Language Bool)
    (R : List Bool → List Bool → Prop) : Prop extends InteractiveProof π L where
  /-- The prover is efficient (`Strategy.Efficient`, D8). -/
  efficientP : π.P.Efficient
  /-- The prover's messages have at most `B(|x|)` bits on instances with a witness. -/
  boundedP : ∃ B : PolyExpr, π.ProverBounded R B
  /-- Completeness for every witness. -/
  completeWitness : ∀ x y, R x y → ∀ z : List Bool,
    uprob (fun r : π.ExecCoins π.P x => π.outV π.P x y z r = [true]) = 1

/-- An interactive proof with soundness error `s` and efficient prover with respect to `R`
[PS10, Definition 119.5 with the soundness error of §4.5] (Def-119.5, Def-117.a).

**Deviation (D8; ruling G3-3 of gate 03):** as for `EfficientProverProof` (`Efficient` prover
with messages of at most `B(|x|)` bits on instances with a witness). -/
structure EfficientProverProofErr (π : Protocol) (L : Language Bool)
    (R : List Bool → List Bool → Prop) (s : ℕ → ℝ) : Prop extends InteractiveProofErr π L s where
  /-- The prover is efficient (`Strategy.Efficient`, D8). -/
  efficientP : π.P.Efficient
  /-- The prover's messages have at most `B(|x|)` bits on instances with a witness. -/
  boundedP : ∃ B : PolyExpr, π.ProverBounded R B
  /-- Completeness for every witness. -/
  completeWitness : ∀ x y, R x y → ∀ z : List Bool,
    uprob (fun r : π.ExecCoins π.P x => π.outV π.P x y z r = [true]) = 1

/-- A negligible soundness error gives an interactive proof with efficient prover. -/
theorem EfficientProverProofErr.efficientProverProof {π : Protocol} {L : Language Bool}
    {R : List Bool → List Bool → Prop} {s : ℕ → ℝ} (hs : Negligible s)
    (h : EfficientProverProofErr π L R s) : EfficientProverProof π L R where
  toInteractiveProof := h.toInteractiveProofErr.interactiveProof hs
  efficientP := h.efficientP
  boundedP := h.boundedP
  completeWitness := h.completeWitness

/-- An interactive proof with efficient prover has a negligible soundness error. -/
theorem EfficientProverProof.exists_err {π : Protocol} {L : Language Bool}
    {R : List Bool → List Bool → Prop} (h : EfficientProverProof π L R) :
    ∃ ε : ℕ → ℝ, Negligible ε ∧ EfficientProverProofErr π L R ε := by
  obtain ⟨ε, hε, herr⟩ := h.toInteractiveProof.exists_err
  exact ⟨ε, hε, herr, h.efficientP, h.boundedP, h.completeWitness⟩

/-! ### The trivial NP protocol -/

/-- The one-message protocol in which the prover sends its auxiliary input `y` and the
verifier accepts iff `T ⟨x, y'⟩`, where `y'` is the received message truncated to its first
`p(|x|)` bits [PS10, §4.5, "`NP ⊆ IP`": the certificate is sent in one round, and a
polynomial-time verifier reads at most polynomially many bits of it]: prover first, one
message, no coins.

**Repair (run-3 audit P9-1):** the witness-length bound `p : PolyExpr` is a parameter and the
verifier reads only the first `p(|x|)` bits of the message (`npProtocol_readsPrefix`), so that
the protocol witnesses `L ∈ IP` under the repaired class; the run-2 verifier read the whole
message. -/
def npProtocol (T : List Bool → Bool) (p : PolyExpr) : Protocol where
  P := ⟨fun _ y _ _ => y, .const 0⟩
  V := ⟨fun x _ _ hist => [T (pairEncode x ((hist.headD []).take (p.eval x.length)))], .const 0⟩
  rounds := .const 1
  verifierFirst := false

/-- In `npProtocol T p` the verifier's output against any prover `P'` is the verdict `T` on
`⟨x, m'⟩`, where `m'` is the first `p(|x|)` bits of the single message `P'` sends on the empty
history. -/
theorem npProtocol_outV (T : List Bool → Bool) (p : PolyExpr) (P' : Strategy) (x y z : List Bool)
    (r : (npProtocol T p).ExecCoins P' x) :
    (npProtocol T p).outV P' x y z r =
      [T (pairEncode x ((P'.next x y (List.ofFn r.1) []).take (p.eval x.length)))] := by
  simp [Protocol.outV, Protocol.transcriptWith, npProtocol, exec, moverIsV]

/-- The verifier of `npProtocol T p` reads only the first `p(|x|)` bits of the message
(`List.take_take`). -/
theorem npProtocol_readsPrefix (T : List Bool → Bool) (p : PolyExpr) :
    (npProtocol T p).V.ReadsPrefix p := by
  intro x z r hist
  cases hist with
  | nil => rfl
  | cons m hist => simp [npProtocol, List.take_take]

/-- The verifier of `npProtocol T p` is efficient when `T` is polynomial-time: one activation of
the uniform machine computing `w ↦ [T ⟨x, m.take (p(|x|))⟩]` from the projections of the layout
`⟨⟨⟨1^n, ⟨⟨x, z⟩, msgs⟩⟩, []⟩, r⟩`.

**Proof sketch.** `x` and the first message `m` are fixed `pairFstD`/`pairSndD` projection
chains of the raw input `w` (`PolyTimeComputable.comp`); the truncation `m.take (p(|x|))` is
`Complexity.polyTimeComputable_pairTakePoly p` applied to `⟨x, m⟩`
(`PolyTimeComputable.pairEncode`), and `T` is applied to `⟨x, m.take (p(|x|))⟩` (`hT.comp`).
The uniform machine `NUPPT.ofPolyTimeUniform` of this function has the required next-message
function on every history (`NUPPT.runAtL_ofPolyTimeUniform`, `Strategy.pairFstD_encodeMsgs`). -/
theorem npProtocol_efficientV (T : List Bool → Bool) (p : PolyExpr)
    (hT : PolyTimeComputable fun z => [T z]) : (npProtocol T p).V.Efficient := by
  have harg : PolyTimeComputable fun w => pairSndD (pairFstD (pairFstD w)) :=
    polyTimeComputable_pairSndD.comp (polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD)
  have hx : PolyTimeComputable fun w => pairFstD (pairFstD (pairSndD (pairFstD (pairFstD w)))) :=
    polyTimeComputable_pairFstD.comp (polyTimeComputable_pairFstD.comp harg)
  have hm : PolyTimeComputable fun w => pairFstD (pairSndD (pairSndD (pairFstD (pairFstD w)))) :=
    polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp harg)
  have htake : PolyTimeComputable fun w =>
      (pairFstD (pairSndD (pairSndD (pairFstD (pairFstD w))))).take
        (p.eval (pairFstD (pairFstD (pairSndD (pairFstD (pairFstD w))))).length) := by
    convert (polyTimeComputable_pairTakePoly p).comp (hx.pairEncode hm) using 1
    funext w
    simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have hF : PolyTimeComputable fun w =>
      [T (pairEncode (pairFstD (pairFstD (pairSndD (pairFstD (pairFstD w)))))
        ((pairFstD (pairSndD (pairSndD (pairFstD (pairFstD w))))).take
          (p.eval (pairFstD (pairFstD (pairSndD (pairFstD (pairFstD w))))).length)))] :=
    hT.comp (hx.pairEncode htake)
  refine ⟨NUPPT.ofPolyTimeUniform hF (.const 0), NUPPT.ofPolyTimeUniform_uniform hF _, rfl,
    fun x z r hist => ?_⟩
  simp [npProtocol, Strategy.ofNUPPT_next, NUPPT.runAtL_ofPolyTimeUniform, NUPPT.advInput,
    Strategy.pairFstD_encodeMsgs]

/-- The prover of `npProtocol T p` is efficient: it copies the auxiliary input, the projection
`pairSndD ∘ pairFstD` of the argument of the layout. -/
theorem npProtocol_efficientP (T : List Bool → Bool) (p : PolyExpr) :
    (npProtocol T p).P.Efficient := by
  have harg : PolyTimeComputable fun w => pairSndD (pairFstD (pairFstD w)) :=
    polyTimeComputable_pairSndD.comp (polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD)
  have hF : PolyTimeComputable fun w => pairSndD (pairFstD (pairSndD (pairFstD (pairFstD w)))) :=
    polyTimeComputable_pairSndD.comp (polyTimeComputable_pairFstD.comp harg)
  refine ⟨NUPPT.ofPolyTimeUniform hF (.const 0), NUPPT.ofPolyTimeUniform_uniform hF _, rfl,
    fun x z r hist => ?_⟩
  simp [npProtocol, Strategy.ofNUPPT_next, NUPPT.runAtL_ofPolyTimeUniform, NUPPT.advInput]

/-- The prover of `npProtocol T p` sends its auxiliary input, so on witnesses of length at most
`p(|x|)` its message has at most `p(|x|)` bits (ruling G3-3 of gate 03). -/
theorem npProtocol_proverBounded (T : List Bool → Bool) (p : PolyExpr)
    {R : List Bool → List Bool → Prop} (hp : ∀ x y, R x y → y.length ≤ p.eval x.length) :
    (npProtocol T p).ProverBounded R p :=
  fun x y _ _ hxy => hp x y hxy

/-- Non-vacuity of Definitions 116.1 and 119.5 [PS10, §4.5, "`NP ⊆ IP`"]: for a witness relation
`R` of `L` decided by the polynomial-time predicate `T`, with witnesses of length at most
`p(|x|)`, the one-message protocol in which the prover sends a witness is an interactive proof
for `L` with efficient prover with respect to `R` (the verifier rejects every `x ∉ L` with
probability one).

**Repair (run-3 audit P9-1):** the witness-length bound `p` with `hp` added (the verifier of
`npProtocol T p` reads only `p(|x|)` bits).

**Proof sketch.** The verifier's output is `[T ⟨x, m.take (p(|x|))⟩]` for the message `m` sent
(`npProtocol_outV`); the honest prover sends `y`, which the truncation leaves unchanged since
`|y| ≤ p(|x|)` (`hp`, `List.take_of_length_le`). Completeness for every witness `y`:
`T ⟨x, y⟩ = true` (`hTR`) on every coin pair, so the probability is one
(`HardcoreBit.uprob_eq_one_of_forall`); the prover's message `y` has at most `p(|x|)` bits
(`npProtocol_proverBounded`), and completeness follows for `x ∈ L` with a witness from
`hR.mem_iff` (`Protocol.ProverBounded.exists_complete`). Soundness with `ε n := 2⁻¹ ^ n`
(`negligible_two_pow_neg`; the literal clause is strict, so `ε = 0` is not admissible): for
`x ∉ L` no string — in particular no truncated message — is a witness, so `T ⟨x, ·⟩ = false`
and the verifier outputs `[false]` on every coin pair, with probability `1 > 1 - ε(|x|)`.
Efficiency of both parties: `npProtocol_efficientV`, `npProtocol_efficientP`. -/
theorem npProtocol_interactiveProof {L : Language Bool} {R : List Bool → List Bool → Prop}
    (hR : WitnessRelation L R) (T : List Bool → Bool) (p : PolyExpr)
    (hT : PolyTimeComputable fun z => [T z])
    (hTR : ∀ x y, T (pairEncode x y) = true ↔ R x y)
    (hp : ∀ x y, R x y → y.length ≤ p.eval x.length) :
    EfficientProverProof (npProtocol T p) L R := by
  have hcw : ∀ x y, R x y → ∀ z : List Bool,
      uprob (fun r : (npProtocol T p).ExecCoins (npProtocol T p).P x =>
        (npProtocol T p).outV (npProtocol T p).P x y z r = [true]) = 1 := by
    intro x y hy z
    refine HardcoreBit.uprob_eq_one_of_forall fun r => ?_
    rw [npProtocol_outV]
    simp [npProtocol, List.take_of_length_le (hp x y hy), (hTR x y).2 hy]
  refine
    { efficientV := npProtocol_efficientV T p hT
      complete := (npProtocol_proverBounded T p hp).exists_complete
        (fun x hx => (hR.mem_iff x).1 hx) hcw
      sound := ?_
      efficientP := npProtocol_efficientP T p
      boundedP := ⟨p, npProtocol_proverBounded T p hp⟩
      completeWitness := hcw }
  refine ⟨fun n => (2 : ℝ)⁻¹ ^ n, negligible_two_pow_neg, fun x hx P' z => ?_⟩
  have hall : ∀ r : (npProtocol T p).ExecCoins P' x,
      (npProtocol T p).outV P' x [] z r = [false] := by
    intro r
    rw [npProtocol_outV]
    have hno : ¬ R x ((P'.next x [] (List.ofFn r.1) []).take (p.eval x.length)) :=
      fun hw => hx ((hR.mem_iff x).2 ⟨_, hw⟩)
    have hfalse :
        T (pairEncode x ((P'.next x [] (List.ofFn r.1) []).take (p.eval x.length))) = false := by
      rw [← Bool.not_eq_true, hTR]
      exact hno
    rw [hfalse]
  rw [HardcoreBit.uprob_eq_one_of_forall hall]
  exact sub_lt_self _ (by positivity)

/-- Every language with a witness relation is in `IP` [PS10, §4.5, "`NP ⊆ IP`"] (Claim-117.c):
the one-message protocol `npProtocol T p`, with the relation's decider `T` and witness-length
bound `p`, is an interactive proof whose verifier reads only `p(|x|)` bits of the message
(`npProtocol_readsPrefix`, `npProtocol_interactiveProof`). -/
theorem WitnessRelation.mem_IP {L : Language Bool} {R : List Bool → List Bool → Prop}
    (h : WitnessRelation L R) : L ∈ IP := by
  obtain ⟨p, hp⟩ := h.bounded
  obtain ⟨T, hT, hTR⟩ := h.decidable
  exact ⟨npProtocol T p, p, npProtocol_readsPrefix T p,
    (npProtocol_interactiveProof h T p hT hTR hp).toInteractiveProof⟩

/-- `NP ⊆ IP` [PS10, §4.5] (Claim-117.c): every `NP` language has a witness relation
(`exists_witnessRelation_of_mem_NP`), hence an interactive proof with a prefix-reading
verifier (`WitnessRelation.mem_IP`). -/
theorem NP_subset_IP : NP ⊆ IP := fun _ h =>
  (Classical.choose_spec (exists_witnessRelation_of_mem_NP h)).mem_IP

end TCSlib.Cryptography

## ===== TCSlib/Cryptography/ZeroKnowledge/Defs.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.Interaction
import TCSlib.Cryptography.Asymptotic.Adversary
import TCSlib.Cryptography.Asymptotic.Sampling
import TCSlib.Cryptography.Foundations.Negligible
import TCSlib.Cryptography.ZeroKnowledge.EncodingMachines
import TCSlib.Complexity.Randomized.Closure

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Zero-knowledge: honest-verifier, general, statistical and perfect

The zero-knowledge notions of [PS10, §4.6] on top of the interaction model of
`Interaction.lean` (foundation decision D8): honest-verifier zero-knowledge
[PS10, Definition 121.1], zero-knowledge against every efficient verifier
[PS10, Definition 121.2], and the perfect and statistical variants (Def-122.a) through the
sup-over-test-sets closeness `StatClose` of `Asymptotic/Sampling.lean`, together with the
implications statistical ⇒ computational (`StatZK.zk`, `StatZK.hvzk`), general ⇒ honest-verifier
(`ZK.hvzk`), and the negligibility bookkeeping converting the chapter's per-vertex bounds
`2^{-n}`, `e^{-n}` into functions of the instance length `|x|` (Inf-4.4).

The simulator is a uniform `Complexity.NUPPT` run once at parameter `|x|` on `⟨x, z⟩`
(`Complexity.NUPPT.simulate`); its output is a word read as an encoded view
(`View.encode`: `⟨⟨x, z⟩, ⟨r, messages⟩⟩`), and the distinguisher is a non-uniform PPT run at
parameter `|x|` on the encoded view (`Complexity.NUPPT.distinguisherL`).

**Deviation (D8):** strict PPT simulators (the text's expected polynomial time is not
formalized; the rewinding simulators of the chapter are truncated and the theorems become
statistical); the auxiliary input of the verifier is bounded by an arbitrary polynomial
`Lz : PolyExpr` quantified after the simulator (the class a `t(|x|)`-time verifier can read,
and what the non-uniform reduction of [PS10, Proposition 128.8] needs); the error bound is
a function of `|x|` (the text's `e(n)` leaves `n` undefined); the honest-verifier notion is
stated for a protocol and a witness relation without assuming the proof property, which the
theorems add separately.
The bound `Lz` is necessary, not only convenient (gate 03e, note 9): the distinguisher runs in
time polynomial in its input, the encoded view, which contains `z`; with `|z| ≥ 2^n` it could
invert a one-way permutation on `n`-bit inputs and open the unopened commitments of the
3-colouring protocol, so computational zero-knowledge would fail for every protocol whose
hiding is only computational. Read literally, [PS10, Definition 121.2] (every
`z ∈ {0,1}*`, with `D` polynomial-time in its input) has the same defect. For the same reason
the distinguisher's advice is indexed by the parameter `|x|`, not by its input length.

**Perfect zero-knowledge (ruling G3-4 of gate 03).** With strict simulators and honest parties
drawing polynomially many fair coins (D8, D10), no protocol of the source attains `PerfectZK`
or `PerfectZKAbort` (see their docstrings). The source's perfect zero-knowledge protocol,
graph isomorphism [PS10, Theorem 122.3], is formalized as `StatZK` with negligible error
(`gi_statZK`, `ZeroKnowledge/GraphIsomorphismZK.lean`), the substantive instance of the
notions of this file; `perfectZK_zeroRounds` is a degenerate one. The abort form implies
statistical zero-knowledge with error `2^{-|x|}` (`PerfectZKAbort.statZK`), by running the
aborting simulator `|x|` times on fresh coins (`AbortRetry.retry`).

## Main definitions

* `Complexity.NUPPT.simulate` — the simulator's output on `(x, z)`.
* `TCSlib.Cryptography.HVZK` — honest-verifier zero-knowledge [PS10, Definition 121.1]
  (Def-121.1).
* `TCSlib.Cryptography.ZK` — zero-knowledge [PS10, Definition 121.2] (Def-121.2).
* `TCSlib.Cryptography.StatZK`, `TCSlib.Cryptography.PerfectZK`,
  `TCSlib.Cryptography.PerfectZKAbort` — statistical zero-knowledge with error `δ(|x|)`,
  perfect zero-knowledge (`δ = 0`), and the abort form of perfect zero-knowledge
  [Gol01, Definition 4.3.1] (Def-122.a).
* `TCSlib.Cryptography.AbortRetry.attempt`, `TCSlib.Cryptography.AbortRetry.retry` — one
  attempt of an aborting simulator on a coin block, and the simulator that retries it `|x|`
  times (as functions of the machine layout).

## Main results

* `TCSlib.Cryptography.StatZK.zk`, `TCSlib.Cryptography.StatZK.hvzk` — statistical
  zero-knowledge with negligible error implies zero-knowledge and honest-verifier
  zero-knowledge (`distAdv_le_of_statClose`).
* `TCSlib.Cryptography.ZK.hvzk` — zero-knowledge implies honest-verifier zero-knowledge.
* `TCSlib.Cryptography.PerfectZK.zk`, `TCSlib.Cryptography.StatZK.mono` — perfect
  zero-knowledge is zero-knowledge; weakening the error.
* `TCSlib.Cryptography.perfectZK_zeroRounds` — non-vacuity: the protocol with no messages is
  perfectly zero-knowledge.
* `TCSlib.Cryptography.PerfectZKAbort.statZK`, `TCSlib.Cryptography.PerfectZKAbort.zk` — the
  abort form implies statistical zero-knowledge with error `2^{-|x|}`, hence zero-knowledge
  (`TCSlib.Cryptography.AbortRetry.statClose_retry`: the first non-`⊥` output of `K`
  independent runs of an aborting sampler is `2^{-K}`-close to its conditional law;
  `TCSlib.Cryptography.AbortRetry.exists_retrySimulator`: the retrying simulator is a uniform
  PPT, by `EncodingMachines.polyTimeComputable_firstIdx`, an instance of
  `Complexity.polyTimeComputable_iterateFind`).
* `TCSlib.Cryptography.negligible_inv_pow_sqrt_div`,
  `TCSlib.Cryptography.negligible_two_pow_neg_sqrt_div`,
  `TCSlib.Cryptography.negligible_exp_neg_sqrt_div`,
  `TCSlib.Cryptography.negligible_of_le_inv_pow_sqrt_div` — `a^{-√(N/C)}` is negligible
  in `N` (Inf-4.4): the per-vertex bounds of the graph protocols are negligible in `|x|`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.6 Zero-knowledge, pp. 120–122.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, Lemma 3.1 (statistical distance bounds every advantage).
* [Gol01] O. Goldreich, *Foundations of Cryptography, Volume I: Basic Tools*, Cambridge
  University Press, 2001, Definition 4.3.1 (perfect zero-knowledge with abort).
-/

namespace TCSlib.Cryptography

open Complexity Turing

/-! ### Simulators -/

/-- The simulator's output on `(x, z)` [PS10, Definitions 121.1 and 121.2, `S(x, z)`]: one
activation of `S` at parameter `|x|` on `⟨x, z⟩`, a word read as an encoded view. -/
def _root_.Complexity.NUPPT.simulate (S : NUPPT) (x z : List Bool) (r : S.Coins x.length) :
    List Bool :=
  S.runAt x.length (pairEncode x z) r

/-- `simulate` unfolds to the typed activation at parameter `|x|`. -/
theorem _root_.Complexity.NUPPT.simulate_eq (S : NUPPT) (x z : List Bool)
    (r : S.Coins x.length) : S.simulate x z r = S.runAt x.length (pairEncode x z) r := rfl

/-! ### Honest-verifier and general zero-knowledge -/

/-- Honest-verifier zero-knowledge of `π` for the witness relation `R`
[PS10, Definition 121.1] (Def-121.1): there is a uniform PPT simulator `S` such that for every
auxiliary-input bound `Lz` and every non-uniform PPT distinguisher `D` there is a negligible `ε`
with, for all `x`, witnesses `y` of `x` and auxiliary inputs `z` of length `≤ Lz(|x|)`, the
advantage of `D` (at parameter `|x|`) between the honest verifier's view of
`P(x, y) ↔ V(x, z)` and `S(x, z)` at most `ε(|x|)`.

**Deviation (D8):** strict PPT simulator; auxiliary inputs bounded by `∀ Lz : PolyExpr`;
simulator and distinguisher at parameter `|x|`; views encoded as `⟨⟨x, z⟩, ⟨r, msgs⟩⟩`. -/
def HVZK (π : Protocol) (R : List Bool → List Bool → Prop) : Prop :=
  ∃ S : NUPPT, S.Uniform ∧ ∀ (Lz : PolyExpr) (D : NUPPT), ∃ ε : ℕ → ℝ, Negligible ε ∧
    ∀ x y z, R x y → z.length ≤ Lz.eval x.length →
      distAdv (fun r => (π.viewV x y z r).encode) (S.simulate x z) (D.distinguisherL x.length) ≤
        ε x.length

/-- Zero-knowledge of `π` for the witness relation `R` [PS10, Definition 121.2] (Def-121.2):
for every efficient verifier strategy `V'` there is a uniform PPT simulator `S` such that for
every auxiliary-input bound `Lz` and every non-uniform PPT distinguisher `D` there is a
negligible `ε` with, for all `x`, witnesses `y` and auxiliary inputs `z` of length `≤ Lz(|x|)`,
the advantage of `D` between the view of `V'` in `P(x, y) ↔ V'(x, z)` and `S(x, z)` at most
`ε(|x|)`.

**Deviation (D8):** strict PPT simulator; auxiliary inputs bounded by `∀ Lz : PolyExpr`;
simulator and distinguisher at parameter `|x|`; views encoded as `⟨⟨x, z⟩, ⟨r, msgs⟩⟩`. The
cheating verifier `V'` is only `Efficient`, with no message-prefix cap (question Q-1 of
gate 03, ruled: no cap on `V*`), so its class is larger than the text's. Since the honest
prover's messages are polynomially bounded in `|x|` in the proof systems
(`Protocol.ProverBounded`, ruling G3-3 of gate 03), the view of every efficient `V'` — `x`,
`z`, its tape and the honest prover's messages — is polynomially bounded all the same. -/
def ZK (π : Protocol) (R : List Bool → List Bool → Prop) : Prop :=
  ∀ V' : Strategy, V'.Efficient → ∃ S : NUPPT, S.Uniform ∧
    ∀ (Lz : PolyExpr) (D : NUPPT), ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ x y z, R x y → z.length ≤ Lz.eval x.length →
        distAdv (fun r => ((π.withV V').viewV x y z r).encode) (S.simulate x z)
          (D.distinguisherL x.length) ≤ ε x.length

/-- Statistical zero-knowledge of `π` for `R` with error `δ(|x|)` (Def-122.a, campaign
addition needed for the truncated simulators): for every efficient `V'` there is a uniform PPT
simulator whose output on `(x, z)` is `StatClose` (every test set, sup form) within `δ(|x|)`
to the view of `V'` in `P(x, y) ↔ V'(x, z)`, for all `x`, witnesses `y` and all auxiliary
inputs `z`.

**Deviation (D8):** strict PPT simulator; the bound is in `|x|`. -/
def StatZK (π : Protocol) (R : List Bool → List Bool → Prop) (δ : ℕ → ℝ) : Prop :=
  ∀ V' : Strategy, V'.Efficient → ∃ S : NUPPT, S.Uniform ∧ ∀ x y z, R x y →
    StatClose (fun r => ((π.withV V').viewV x y z r).encode) (S.simulate x z) (δ x.length)

/-- Perfect zero-knowledge [PS10, §4.6, "perfect zero-knowledge"] (Def-122.a): statistical
zero-knowledge with error `0`, i.e. the simulator's output has exactly the law of the view.

**Cost (D8, D10; ruling G3-4 of gate 03):** no protocol of the source attains this notion. A
strict simulator with bit coins outputs every string with a dyadic probability, and an
honest prover drawing polynomially many fair coins cannot draw a uniform permutation of
`n ≥ 3` points (`n! ∤ 2^c`), so the reply of the honest graph-isomorphism prover
[PS10, Protocol 120.6] depends on the witness. [PS10, Theorem 122.3] is formalized as
`StatZK` with negligible error (`gi_statZK`); the instances of this notion are degenerate
(`perfectZK_zeroRounds`). -/
def PerfectZK (π : Protocol) (R : List Bool → List Bool → Prop) : Prop :=
  StatZK π R (fun _ => 0)

/-- Perfect zero-knowledge with abort [Gol01, Definition 4.3.1] (Def-122.a, the GMR form):
for every efficient `V'` there is a uniform PPT simulator that outputs `⊥ = []` with
probability at most `1/2` and whose output, conditioned on not aborting, has exactly the law
of the view of `V'`: for every test set `T`,
`Pr[T(view)] · Pr[S ≠ ⊥] = Pr[S ≠ ⊥ ∧ T(S)]` (`⊥ = []` is never a view encoding).

**Cost (D8, D10; ruling G3-4 of gate 03):** no protocol of the source attains this notion:
as for `PerfectZK`, the honest graph-isomorphism prover's permutation, drawn from fair coins,
is not uniform, so its reply depends on the witness, which no simulator sees. The abort form
holds for ideal permutations at the concrete layer (`giSimAttempt_perfectAbort`). It implies
statistical zero-knowledge with error `2^{-|x|}` (`PerfectZKAbort.statZK`), hence
zero-knowledge (`PerfectZKAbort.zk`); the source's "perfect" results are stated as `StatZK`
with negligible error. -/
def PerfectZKAbort (π : Protocol) (R : List Bool → List Bool → Prop) : Prop :=
  ∀ V' : Strategy, V'.Efficient → ∃ S : NUPPT, S.Uniform ∧ ∀ x y z, R x y →
    uprob (fun r : S.Coins x.length => S.simulate x z r = []) ≤ 1 / 2 ∧
    ∀ T : List Bool → Prop,
      uprob (fun r : (π.withV V').ExecCoins π.P x => T ((π.withV V').viewV x y z r).encode) *
          uprob (fun r : S.Coins x.length => S.simulate x z r ≠ []) =
        uprob (fun r : S.Coins x.length => S.simulate x z r ≠ [] ∧ T (S.simulate x z r))

/-! ### Implications between the notions -/

/-- Statistical zero-knowledge with negligible error implies zero-knowledge
[PS10, §4.6, perfect/statistical ⇒ computational]: the same simulator works for every
distinguisher, with `ε := δ`, since a distinguisher's advantage between `δ`-close samplers is
at most `δ` (`distAdv_le_of_statClose`, [Gar26, Lemma 3.1]). -/
theorem StatZK.zk {π : Protocol} {R : List Bool → List Bool → Prop} {δ : ℕ → ℝ}
    (hδ : Negligible δ) (h : StatZK π R δ) : ZK π R := by
  intro V' hV'
  obtain ⟨S, hS, hclose⟩ := h V' hV'
  exact ⟨S, hS, fun _ D => ⟨δ, hδ, fun x y z hR _ =>
    distAdv_le_of_statClose _ _ (hclose x y z hR) _⟩⟩

/-- Statistical zero-knowledge with negligible error implies honest-verifier zero-knowledge
when the honest verifier is efficient: instantiate `V' := V` (`Protocol.withV_self`) and
apply `distAdv_le_of_statClose`. -/
theorem StatZK.hvzk {π : Protocol} {R : List Bool → List Bool → Prop} {δ : ℕ → ℝ}
    (hδ : Negligible δ) (hV : π.V.Efficient) (h : StatZK π R δ) : HVZK π R := by
  obtain ⟨S, hS, hclose⟩ := h π.V hV
  refine ⟨S, hS, fun _ D => ⟨δ, hδ, fun x y z hR _ => ?_⟩⟩
  have hc := hclose x y z hR
  rw [Protocol.withV_self] at hc
  exact distAdv_le_of_statClose _ _ hc _

/-- Zero-knowledge implies honest-verifier zero-knowledge when the honest verifier is
efficient [PS10, §4.6, after Definition 121.2]: instantiate `V' := V`. -/
theorem ZK.hvzk {π : Protocol} {R : List Bool → List Bool → Prop} (hV : π.V.Efficient)
    (h : ZK π R) : HVZK π R := by
  obtain ⟨S, hS, hsim⟩ := h π.V hV
  refine ⟨S, hS, fun Lz D => ?_⟩
  obtain ⟨ε, hε, hadv⟩ := hsim Lz D
  refine ⟨ε, hε, fun x y z hR hz => ?_⟩
  have hc := hadv x y z hR hz
  rwa [Protocol.withV_self] at hc

/-- Weakening the statistical error. -/
theorem StatZK.mono {π : Protocol} {R : List Bool → List Bool → Prop} {δ δ' : ℕ → ℝ}
    (h : StatZK π R δ) (hle : ∀ n, δ n ≤ δ' n) : StatZK π R δ' := by
  intro V' hV'
  obtain ⟨S, hS, hclose⟩ := h V' hV'
  exact ⟨S, hS, fun x y z hR => (hclose x y z hR).mono (hle _)⟩

/-- The zero function is negligible. -/
theorem negligible_const_zero : Negligible (fun _ => (0 : ℝ)) := fun c =>
  ⟨1, fun n hn => by
    rw [abs_zero]
    exact one_div_pos.mpr (pow_pos (Nat.cast_pos.mpr hn) c)⟩

/-- Perfect zero-knowledge is statistical zero-knowledge with error `0`. -/
theorem PerfectZK.statZK {π : Protocol} {R : List Bool → List Bool → Prop} (h : PerfectZK π R) :
    StatZK π R (fun _ => 0) := h

/-- Perfect zero-knowledge implies zero-knowledge [PS10, §4.6]. -/
theorem PerfectZK.zk {π : Protocol} {R : List Bool → List Bool → Prop} (h : PerfectZK π R) :
    ZK π R :=
  StatZK.zk negligible_const_zero h

/-- Non-vacuity (gate 03e, note 10): the protocol with no messages is perfectly
zero-knowledge for every relation.

**Proof sketch.** The view of any `V'` is `⟨x, z, r, []⟩` (no moves, `exec_zero`), and the
simulator `NUPPT.ofPolyTimeUniform` of the layout map `w ↦ ⟨inArg w, ⟨inCoins w, []⟩⟩` with
`V'`'s coin polynomial outputs `⟨⟨x, z⟩, ⟨r, []⟩⟩` on its own tape `r`; the prover's tape does
not enter the view (`uprob_fst` after `Equiv.prodComm`), so the two laws coincide. -/
theorem perfectZK_zeroRounds (P V : Strategy) (b : Bool) (R : List Bool → List Bool → Prop) :
    PerfectZK ⟨P, V, .const 0, b⟩ R := by
  intro V' _
  have hF : PolyTimeComputable fun w =>
      pairEncode (NUPPT.inArg w) (pairEncode (NUPPT.inCoins w) []) :=
    NUPPT.polyTimeComputable_inArg.pairEncode
      (NUPPT.polyTimeComputable_inCoins.pairEncode (polyTimeComputable_const []))
  refine ⟨NUPPT.ofPolyTimeUniform hF V'.coins, NUPPT.ofPolyTimeUniform_uniform hF _,
    fun x y z _ T => ?_⟩
  have h1 : uprob (fun r : (Protocol.withV ⟨P, V, .const 0, b⟩ V').ExecCoins P x =>
      T ((Protocol.withV ⟨P, V, .const 0, b⟩ V').viewV x y z r).encode) =
      uprob (fun ρ : V'.Coins x.length =>
        T (pairEncode (pairEncode x z) (pairEncode (List.ofFn ρ) []))) := by
    rw [← uprob_comp_equiv (Equiv.prodComm _ _)]
    exact uprob_fst (fun ρ : V'.Coins x.length =>
      T (pairEncode (pairEncode x z) (pairEncode (List.ofFn ρ) [])))
  have h2 : uprob (fun ρ : (NUPPT.ofPolyTimeUniform hF V'.coins).Coins x.length =>
      T ((NUPPT.ofPolyTimeUniform hF V'.coins).simulate x z ρ)) =
      uprob (fun ρ : V'.Coins x.length =>
        T (pairEncode (pairEncode x z) (pairEncode (List.ofFn ρ) []))) := by
    refine OneWay.uprob_congr fun ρ => ?_
    rw [NUPPT.simulate_eq, NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform]
    simp [NUPPT.inArg, NUPPT.inCoins, NUPPT.advInput]
  simp only [h2]
  rw [abs_nonpos_iff, sub_eq_zero]
  exact h1

/-! ### Retrying an aborting simulator -/

namespace AbortRetry

open EncodingMachines Finset Complexity.StateLoop

/-- One attempt of the retrying simulator on its machine layout
`w = ⟨⟨⟨1^n, y⟩, α⟩, r⟩` at the index `t`: the simulator `S` at parameter `n = |1^n|` on the
argument `y`, with empty advice and the `t`-th block of `S.coinLen n` coins of `r`. -/
def attempt (S : NUPPT) (w : List Bool) (t : ℕ) : List Bool :=
  S.output (NUPPT.layout (NUPPT.inParam w) (NUPPT.inArg w) []
    (((NUPPT.inCoins w).drop (t * S.coinLen (NUPPT.inParam w).length)).take
      (S.coinLen (NUPPT.inParam w).length)))

/-- The retrying simulator on its machine layout `w = ⟨⟨⟨1^n, y⟩, α⟩, r⟩`
(for the abort form of [Gol01, Definition 4.3.1], amplified by repetition): the
first of the `n` attempts that does not output `⊥ = []` (the first accepted index,
`EncodingMachines.firstIdx`), or `⊥` if every attempt aborts. -/
noncomputable def retry (S : NUPPT) (w : List Bool) : List Bool :=
  if firstIdx (fun t => decide (attempt S w t ≠ [])) (NUPPT.inParam w).length <
      (NUPPT.inParam w).length then
    attempt S w (firstIdx (fun t => decide (attempt S w t ≠ [])) (NUPPT.inParam w).length)
  else []

/-- One attempt is polynomial-time on the indexed layout `⟨1^t, w⟩`.

**Proof sketch.** The block `(r.drop (t · c)).take c` with `c = S.coinLen n` in unary
(`unaryPoly_comp`, `unaryMul_poly`, `polyTimeComputable_pairDropPoly`, `truncate_poly`), the
layout (`NUPPT.polyTimeComputable_layout`) and the machine of `S`
(`NUPPT.polyTimeComputable_output`). -/
theorem attempt_poly (S : NUPPT) :
    PolyTimeComputable fun u => attempt S (pairSndD u) (pairFstD u).length := by
  have congr : ∀ {f g : List Bool → List Bool}, PolyTimeComputable f → (∀ w, g w = f w) →
      PolyTimeComputable g := fun hf h => by rw [show _ = _ from funext h]; exact hf
  have hpar : PolyTimeComputable fun u => NUPPT.inParam (pairSndD u) :=
    NUPPT.polyTimeComputable_inParam.comp polyTimeComputable_pairSndD
  have hr : PolyTimeComputable fun u => NUPPT.inCoins (pairSndD u) :=
    NUPPT.polyTimeComputable_inCoins.comp polyTimeComputable_pairSndD
  have hc : PolyTimeComputable fun u =>
      List.replicate (S.coinLen (NUPPT.inParam (pairSndD u)).length) true :=
    unaryPoly_comp S.coins hpar
  have ht : PolyTimeComputable fun u => List.replicate (pairFstD u).length true :=
    unaryLength_poly polyTimeComputable_pairFstD
  have hdrop : PolyTimeComputable fun u => (NUPPT.inCoins (pairSndD u)).drop
      ((pairFstD u).length * S.coinLen (NUPPT.inParam (pairSndD u)).length) :=
    congr ((polyTimeComputable_pairDropPoly .var).comp ((unaryMul_poly ht hc).pairEncode hr))
      fun u => by simp
  have hblk := truncate_poly hdrop hc
  have hlay := NUPPT.polyTimeComputable_layout hpar
    (NUPPT.polyTimeComputable_inArg.comp polyTimeComputable_pairSndD)
    (polyTimeComputable_const []) hblk
  exact congr (S.polyTimeComputable_output.comp hlay) fun u => rfl

/-- **The retrying simulator is polynomial-time** as a function of its layout: the first
non-aborting index is `EncodingMachines.polyTimeComputable_firstIdx` (an instance of the
repetition lemma `Complexity.polyTimeComputable_iterateFind`) with the test of
`attempt_poly`, and the output is that attempt (`attempt_poly` at the found index) or `[]`
(`polyTimeComputable_ite`). -/
theorem retry_poly (S : NUPPT) : PolyTimeComputable (retry S) := by
  have congr : ∀ {f g : List Bool → List Bool}, PolyTimeComputable f → (∀ w, g w = f w) →
      PolyTimeComputable g := fun hf h => by rw [show _ = _ from funext h]; exact hf
  have hatt := attempt_poly S
  have hp : PolyTimeComputable fun u =>
      [decide (attempt S (pairSndD u) (pairFstD u).length ≠ [])] :=
    congr (ltTest_poly (unaryConst_poly 0) (unaryLength_poly hatt)) fun u => by
      simp [List.length_pos_iff]
  have hN : PolyTimeComputable fun w => List.replicate (NUPPT.inParam w).length true :=
    unaryLength_poly NUPPT.polyTimeComputable_inParam
  have hidx := polyTimeComputable_firstIdx (p := fun w t => decide (attempt S w t ≠ [])) hp hN
  have hsel : PolyTimeComputable fun w => attempt S w
      (firstIdx (fun t => decide (attempt S w t ≠ [])) (NUPPT.inParam w).length) :=
    congr (hatt.comp (hidx.pairEncode polyTimeComputable_id)) fun w => by simp
  refine congr (polyTimeComputable_ite (ltTest_poly hidx hN) hsel (polyTimeComputable_const []))
    fun w => ?_
  simp only [retry, decide_eq_true_eq]

/-- **The retrying simulator is a uniform PPT**: `NUPPT.ofPolyTimeUniform` of `retry_poly`
with `|x|` blocks of `S.coinLen |x|` coins; on `(x, z)` it computes `retry S` on the layout
`⟨⟨⟨1^{|x|}, ⟨x, z⟩⟩, []⟩, r⟩` (`NUPPT.runAtL_ofPolyTimeUniform`). -/
theorem exists_retrySimulator (S : NUPPT) :
    ∃ S' : NUPPT, S'.Uniform ∧ S'.coins = .mul .var S.coins ∧
      ∀ x z (r : S'.Coins x.length), S'.simulate x z r =
        retry S (NUPPT.layout (List.replicate x.length true) (pairEncode x z) [] (List.ofFn r)) :=
  ⟨NUPPT.ofPolyTimeUniform (retry_poly S) (.mul .var S.coins),
    NUPPT.ofPolyTimeUniform_uniform _ _, rfl, fun x z r => by
      rw [NUPPT.simulate_eq, NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform]
      rfl⟩

/-- The first hit of `K` draws read through `EncodingMachines.firstIdx`: if `a t` is `g` of
the `t`-th draw and `q t` tests `E` on it (for `t < K`), then the first hit mapped by `g` and
defaulted to `d` is `a` at the first index accepted by `q`, or `d` if there is none.

**Proof sketch.** If `i := firstIdx q K < K`, the draw `i` is in `E` (`q_firstIdx`) and no
earlier draw is (`firstIdx_min`); splitting `List.finRange K` at `i`
(`List.drop_eq_getElem_cons`, `List.take_append_drop`, `List.getElem_finRange`) gives
`firstHit E xs = some (xs i)` by `List.findSome?_eq_some_iff`. Otherwise no draw is in `E`
(`firstIdx_eq_iff`) and `firstHit E xs = none` (`firstHit_eq_none_iff`). -/
theorem firstHit_map_getD_eq {α β : Type*} (E : α → Prop) [DecidablePred E] {K : ℕ}
    (xs : Fin K → α) (g : α → β) (d : β) (a : ℕ → β) (q : ℕ → Bool)
    (ha : ∀ t (ht : t < K), a t = g (xs ⟨t, ht⟩))
    (hq : ∀ t (ht : t < K), q t = decide (E (xs ⟨t, ht⟩))) :
    ((firstHit E xs).map g).getD d = if firstIdx q K < K then a (firstIdx q K) else d := by
  split_ifs with h
  · set i := firstIdx q K with hi_def
    have hEi : E (xs ⟨i, h⟩) := by
      have := q_firstIdx h
      rw [hq i h] at this
      exact of_decide_eq_true this
    have hmin : ∀ j (hj : j < i), ¬ E (xs ⟨j, hj.trans h⟩) := fun j hj hE => by
      have := firstIdx_min hj
      rw [hq j (hj.trans h)] at this
      exact absurd (decide_eq_true hE) (by rw [this]; decide)
    have hsome : firstHit E xs = some (xs ⟨i, h⟩) := by
      unfold firstHit
      rw [List.findSome?_eq_some_iff]
      refine ⟨(List.finRange K).take i, ⟨i, h⟩, (List.finRange K).drop (i + 1), ?_, ?_, ?_⟩
      · have hlen : i < (List.finRange K).length := by simpa using h
        have hsplit : List.finRange K = (List.finRange K).take i ++
            (List.finRange K)[i] :: (List.finRange K).drop (i + 1) := by
          rw [← List.drop_eq_getElem_cons hlen, List.take_append_drop]
        rw [List.getElem_finRange] at hsplit
        exact hsplit
      · simp [hEi]
      · intro j hj
        obtain ⟨k, hk, rfl⟩ := List.mem_take_iff_getElem.1 hj
        have hki : k < i := lt_of_lt_of_le hk (min_le_left _ _)
        simp [hmin k hki]
    rw [hsome, ha i h]
    rfl
  · have hall := firstIdx_eq_iff.1 (le_antisymm firstIdx_le (not_lt.1 h))
    have hnone : firstHit E xs = none := (firstHit_eq_none_iff E xs).2 fun t hE => by
      have := hall t t.isLt
      rw [hq t t.isLt] at this
      exact absurd (decide_eq_true hE) (by rw [this]; decide)
    rw [hnone]
    rfl

/-- **Retrying an aborting sampler** (amplification by repetition): let `g` be a
sampler on a finite uniform space `Ω`, `E` the event "`g` does not abort", with
`Pr[¬ E] ≤ 1/2`, and suppose the output of `g` conditioned on `E` has the law of the sampler
`Y`. Then the output of `g` on the first of `K` independent draws in `E` (the default `d₀` if
there is none) is within `2^{-K}` of `Y`.

**Proof sketch.** Let `p := Pr[E] ≥ 1/2` and `f := (1 - p)^K`, the probability that no draw
is in `E` (`uprob_firstHit_none`). Each `a ∈ E` is the first hit with the same probability
`q₀` (`firstHit_uniform_of_some`), so for a test set `T`, splitting over the fibres of
`firstHit` (`uprob_comp_eq_sum_fiber`, `Fintype.sum_option`),
`Pr[T(retry)] = [T d₀] · f + q₀ · #{a ∈ E : T (g a)}`, and with `T := ⊤`,
`1 = f + q₀ · #E`. The conditional-law hypothesis times `|Ω|` is
`Pr[T(Y)] · #E = #{a ∈ E : T (g a)}`, so `Pr[T(retry)] = [T d₀] · f + (1 - f) · Pr[T(Y)]`
(`linear_combination`) and `|Pr[T(Y)] - Pr[T(retry)]| = f · |Pr[T(Y)] - [T d₀]| ≤ f ≤ 2^{-K}`. -/
theorem statClose_retry {Ω τ : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω] [Fintype τ]
    (E : Ω → Prop) [DecidablePred E] (g : Ω → List Bool) (Y : τ → List Bool) (d₀ : List Bool)
    (habort : uprob (fun ω => ¬ E ω) ≤ 1 / 2)
    (hcond : ∀ T : List Bool → Prop,
      uprob (fun t => T (Y t)) * uprob E = uprob (fun ω => E ω ∧ T (g ω)))
    (K : ℕ) :
    StatClose Y (fun ws : Fin K → Ω => ((firstHit E ws).map g).getD d₀) ((2 : ℝ)⁻¹ ^ K) := by
  classical
  intro T
  have hpE : uprob E = 1 - uprob (fun ω => ¬ E ω) := by rw [uprob_not]; ring
  obtain ⟨d, hd⟩ : ∃ d, E d := by
    by_contra hne
    push_neg at hne
    have h0 : uprob E = 0 := by
      rw [← uprob_false (α := Ω)]
      exact OneWay.uprob_congr fun ω => ⟨fun h => hne ω h, False.elim⟩
    linarith
  have hsome : ∀ a, E a → uprob (fun xs : Fin K → Ω => firstHit E xs = some a) =
      uprob (fun xs : Fin K → Ω => firstHit E xs = some d) :=
    fun a ha => firstHit_uniform_of_some E K ha hd
  have hnot : ∀ a, ¬ E a → uprob (fun xs : Fin K → Ω => firstHit E xs = some a) = 0 := by
    intro a ha
    rw [← uprob_false (α := Fin K → Ω)]
    exact OneWay.uprob_congr fun xs => ⟨fun h => ha (firstHit_eq_some_imp E h), False.elim⟩
  have hdec : ∀ S' : Option Ω → Prop, uprob (fun xs : Fin K → Ω => S' (firstHit E xs)) =
      (if S' none then (1 - uprob E) ^ K else 0) +
        uprob (fun xs : Fin K → Ω => firstHit E xs = some d) *
          (univ.filter fun a => E a ∧ S' (some a)).card := by
    intro S'
    rw [uprob_comp_eq_sum_fiber (firstHit E) S', sum_filter, Fintype.sum_option,
      uprob_firstHit_none E K]
    congr 1
    rw [mul_comm, ← nsmul_eq_mul, ← sum_const, sum_filter]
    refine sum_congr rfl fun a _ => ?_
    by_cases hSa : S' (some a)
    · by_cases hEa : E a
      · simp [hSa, hEa, hsome a hEa]
      · simp [hSa, hEa, hnot a hEa]
    · simp [hSa]
  have hsim := hdec fun o => T ((o.map g).getD d₀)
  have htot := hdec fun _ => True
  rw [uprob_true] at htot
  simp only [Option.map_none, Option.getD_none, Option.map_some, Option.getD_some, if_true,
    and_true] at hsim htot
  -- the conditional law in counting form
  have hcard : (Fintype.card Ω : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hc := hcond T
  rw [uprob_eq_card_filter E, uprob_eq_card_filter (fun ω => E ω ∧ T (g ω)), mul_div_assoc',
    div_left_inj' hcard] at hc
  generalize uprob (fun xs : Fin K → Ω => firstHit E xs = some d) = q₀ at hsim htot
  generalize hf : (1 - uprob E) ^ K = f at hsim htot
  have hY0 := uprob_nonneg (fun t => T (Y t))
  have hY1 := uprob_le_one (fun t => T (Y t))
  have hsimeq : uprob (fun xs : Fin K → Ω => T (((firstHit E xs).map g).getD d₀)) =
      (if T d₀ then f else 0) + (1 - f) * uprob (fun t => T (Y t)) := by
    rw [hsim]
    linear_combination (-q₀) * hc + (-uprob (fun t => T (Y t))) * htot
  have hf0 : 0 ≤ f := hf ▸ pow_nonneg (by linarith [uprob_le_one E]) K
  have hfK : f ≤ (2 : ℝ)⁻¹ ^ K :=
    hf ▸ pow_le_pow_left₀ (by linarith [uprob_le_one E]) (by linarith) K
  show |uprob (fun t => T (Y t)) -
    uprob (fun xs : Fin K → Ω => T (((firstHit E xs).map g).getD d₀))| ≤ (2 : ℝ)⁻¹ ^ K
  rw [hsimeq, abs_le]
  split_ifs <;> constructor <;> nlinarith

/-- The probability that the retrying simulator's attempt aborts is the complement of its
success probability (a restatement of `PerfectZKAbort`'s first clause for
`AbortRetry.statClose_retry`). -/
theorem uprob_not_ne_nil_le {Ω : Type*} [Fintype Ω] (g : Ω → List Bool)
    (h : uprob (fun ω => g ω = []) ≤ 1 / 2) : uprob (fun ω => ¬ g ω ≠ []) ≤ 1 / 2 := by
  simpa using h

end AbortRetry

open AbortRetry in
/-- **Perfect zero-knowledge with abort implies statistical zero-knowledge with error
`2^{-|x|}`** (the abort form of [Gol01, Definition 4.3.1], amplified by repetition)
(ruling G3-4 of gate 03): retry the aborting simulator on `|x|` disjoint coin blocks and
output the first non-`⊥` result.

**Proof sketch.** For an efficient `V'` take the aborting simulator `S` of `h`; the
retrying simulator `S'` of `AbortRetry.exists_retrySimulator` is a uniform PPT with `|x|`
blocks of `S.coinLen |x|` coins. Read its tape as `|x|` independent blocks (the bijection
`e` built from `finCongr`, `finProdFinEquiv` and `Equiv.curry`, through
`StatClose.comp_equiv_right`): the `t`-th slice of the tape is `List.ofFn` of block `t`, so
attempt `t` is `S` on block `t` (`S` is uniform, so its advice is `[]`), and the retrying
simulator is the first non-`⊥` attempt (`AbortRetry.firstHit_map_getD_eq`). The two clauses
of `h` are the hypotheses of `AbortRetry.statClose_retry` with `K = |x|`. -/
theorem PerfectZKAbort.statZK {π : Protocol} {R : List Bool → List Bool → Prop}
    (h : PerfectZKAbort π R) : StatZK π R (fun n => (2 : ℝ)⁻¹ ^ n) := by
  intro V' hV'
  obtain ⟨S, hSu, hS⟩ := h V' hV'
  obtain ⟨S', hS'u, hS'c, hS'⟩ := exists_retrySimulator S
  refine ⟨S', hS'u, fun x y z hxy => ?_⟩
  obtain ⟨habort, hcond⟩ := hS x y z hxy
  have hlen : S'.coinLen x.length = x.length * S.coinLen x.length := by
    simp only [NUPPT.coinLen, hS'c, PolyExpr.eval_mul, PolyExpr.eval_var]
  -- the tape of `S'` as `|x|` blocks of `S.coinLen |x|` coins
  let e : S'.Coins x.length ≃ (Fin x.length → S.Coins x.length) :=
    ((Equiv.arrowCongr (finCongr hlen) (Equiv.refl Bool)).trans
      (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl Bool))).trans (Equiv.curry _ _ _)
  have hblock : ∀ (r : S'.Coins x.length) (t : ℕ) (ht : t < x.length),
      ((List.ofFn r).drop (t * S.coinLen x.length)).take (S.coinLen x.length) =
        List.ofFn (e r ⟨t, ht⟩) := by
    intro r t ht
    have hle : t * S.coinLen x.length + S.coinLen x.length ≤ x.length * S.coinLen x.length := by
      rw [← Nat.succ_mul]
      exact Nat.mul_le_mul_right _ ht
    refine List.ext_getElem ?_ fun j h₁ h₂ => ?_
    · simp only [List.length_take, List.length_drop, List.length_ofFn, hlen]
      omega
    · simp only [List.getElem_take, List.getElem_drop, List.getElem_ofFn]
      simp only [e, Equiv.trans_apply, Equiv.arrowCongr_apply, Equiv.coe_refl,
        Function.comp_apply, Equiv.symm_symm, Equiv.curry_apply, Function.curry_apply]
      congr 1
      ext
      simp [finProdFinEquiv]
      ring
  have hatt : ∀ (r : S'.Coins x.length) (t : ℕ) (ht : t < x.length),
      attempt S (NUPPT.layout (List.replicate x.length true) (pairEncode x z) [] (List.ofFn r)) t =
        S.simulate x z (e r ⟨t, ht⟩) := by
    intro r t ht
    simp only [attempt, NUPPT.inParam_layout, NUPPT.inArg_layout, NUPPT.inCoins_layout,
      List.length_replicate]
    rw [hblock r t ht, NUPPT.simulate_eq, NUPPT.runAt_eq, NUPPT.runAtL_eq_output_layout, hSu]
  have heq : ∀ r : S'.Coins x.length, S'.simulate x z r =
      ((firstHit (fun ω => S.simulate x z ω ≠ []) (e r)).map (S.simulate x z)).getD [] := by
    intro r
    rw [hS' x z r, firstHit_map_getD_eq (fun ω => S.simulate x z ω ≠ []) (e r)
      (S.simulate x z) []
      (attempt S (NUPPT.layout (List.replicate x.length true) (pairEncode x z) [] (List.ofFn r)))
      (fun t => decide (attempt S
        (NUPPT.layout (List.replicate x.length true) (pairEncode x z) [] (List.ofFn r)) t ≠ []))
      (hatt r) (fun t ht => by simp only [hatt r t ht])]
    simp only [retry, NUPPT.inParam_layout, List.length_replicate]
  have key := (statClose_retry (fun ω => S.simulate x z ω ≠ []) (S.simulate x z)
    (fun r : (π.withV V').ExecCoins π.P x => ((π.withV V').viewV x y z r).encode) []
    (uprob_not_ne_nil_le _ habort) hcond x.length).comp_equiv_right e
  intro T
  have hu : uprob (fun t : S'.Coins x.length => T (S'.simulate x z t)) =
      uprob (fun t : S'.Coins x.length => T (((firstHit (fun ω => S.simulate x z ω ≠ []) (e t)).map
        (S.simulate x z)).getD [])) :=
    OneWay.uprob_congr fun t => by rw [heq t]
  rw [hu]
  exact key T

/-- **Perfect zero-knowledge with abort implies zero-knowledge** (ruling G3-4 of gate 03):
`PerfectZKAbort.statZK` and `StatZK.zk` with the negligible error `2^{-n}`
(`negligible_two_pow_neg`). -/
theorem PerfectZKAbort.zk {π : Protocol} {R : List Bool → List Bool → Prop}
    (h : PerfectZKAbort π R) : ZK π R :=
  h.statZK.zk negligible_two_pow_neg

/-! ### Negligibility in the instance length (Inf-4.4) -/

/-- For `a > 1` and `C > 0` the function `N ↦ a^{-√(N / C)}` (with `Nat.sqrt` and natural
division) is negligible in `N` (Inf-4.4): the per-vertex error bounds `2^{-n}` and `e^{-n}` of
the graph protocols, whose instances have length `|x| ≥ n² / C`, are negligible in `|x|`.

**Proof sketch.** Fix `c`. Put `t := Nat.sqrt (N / C)`; then `N / C < (t + 1)²`
(`Nat.lt_succ_sqrt`), so `N < C (t + 1)² + C ≤ 2 C (t + 1)²` and
`N ^ c ≤ (2 C)^c (t + 1)^{2c}`. By `tendsto_pow_const_div_const_pow_of_one_lt`
(as in `negligible_two_pow_neg`), `(t + 1)^{2c} / a^{t+1} → 0`, so there is `t₀` with
`(2 C)^c · a · (t + 1)^{2c} < a^{t+1}` for `t ≥ t₀`, i.e. `(2C)^c (t+1)^{2c} < a^t`; and
`t ≥ t₀` as soon as `N ≥ C (t₀ + 1)²` (`Nat.le_sqrt`). Hence for such `N`,
`a⁻¹ ^ t = 1 / a^t < 1 / ((2C)^c (t+1)^{2c}) ≤ 1 / N^c`. -/
theorem negligible_inv_pow_sqrt_div {a : ℝ} (ha : 1 < a) {C : ℕ} (hC : 0 < C) :
    Negligible fun N => a⁻¹ ^ Nat.sqrt (N / C) := by
  intro c
  have ha0 : (0 : ℝ) < a := zero_lt_one.trans ha
  have hCr : (0 : ℝ) < (C : ℝ) ^ c := by positivity
  have hpos : (0 : ℝ) < 1 / ((C : ℝ) ^ c * a) := by positivity
  have ht := tendsto_pow_const_div_const_pow_of_one_lt (2 * c) ha
  obtain ⟨t₀, ht₀⟩ := Filter.eventually_atTop.mp (ht.eventually (gt_mem_nhds hpos))
  refine ⟨max (C * t₀ * t₀) 1, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_of_max_le_right hN
  have hNC : C * t₀ * t₀ ≤ N := le_of_max_le_left hN
  set t := Nat.sqrt (N / C) with ht_def
  -- `t₀ ≤ t` since `C t₀² ≤ N`
  have ht0 : t₀ ≤ t := by
    rw [ht_def, Nat.le_sqrt, Nat.le_div_iff_mul_le hC]
    calc t₀ * t₀ * C = C * t₀ * t₀ := by ring
      _ ≤ N := hNC
  -- `N < (t + 1)² C`
  have hNlt : N < (t + 1) * (t + 1) * C :=
    (Nat.div_lt_iff_lt_mul hC).1 (Nat.lt_succ_sqrt (N / C))
  have hNltR : (N : ℝ) < ((t : ℝ) + 1) ^ 2 * C := by
    have := hNlt
    rw [← pow_two] at this
    exact_mod_cast this
  -- the limit at `t + 1`: `(t + 1)^{2c} C^c < a^t`
  have hlim := ht₀ (t + 1) (by omega)
  have hlim' : ((t : ℝ) + 1) ^ (2 * c) * ((C : ℝ) ^ c * a) < a ^ (t + 1) := by
    have hapos : (0 : ℝ) < a ^ (t + 1) := pow_pos ha0 _
    rw [div_lt_iff₀ hapos] at hlim
    push_cast at hlim
    calc ((t : ℝ) + 1) ^ (2 * c) * ((C : ℝ) ^ c * a)
        < 1 / ((C : ℝ) ^ c * a) * a ^ (t + 1) * ((C : ℝ) ^ c * a) := by
          gcongr
      _ = a ^ (t + 1) := by field_simp
  have hkey : ((t : ℝ) + 1) ^ (2 * c) * (C : ℝ) ^ c < a ^ t := by
    rw [pow_succ, ← mul_assoc] at hlim'
    exact lt_of_mul_lt_mul_right hlim' ha0.le
  -- `N^c ≤ (t + 1)^{2c} C^c`
  have hNpow : (N : ℝ) ^ c ≤ ((t : ℝ) + 1) ^ (2 * c) * (C : ℝ) ^ c := by
    rw [pow_mul, ← mul_pow]
    exact pow_le_pow_left₀ (Nat.cast_nonneg N) hNltR.le c
  have hNpos : (0 : ℝ) < (N : ℝ) ^ c := pow_pos (by exact_mod_cast hN1) c
  show |a⁻¹ ^ t| < 1 / (N : ℝ) ^ c
  rw [abs_of_pos (pow_pos (inv_pos.mpr ha0) t), inv_pow, ← one_div]
  exact one_div_lt_one_div_of_lt hNpos (hNpow.trans_lt hkey)

/-- `2^{-√(N / C)}` is negligible in `N` (Inf-4.4, the graph-isomorphism bound). -/
theorem negligible_two_pow_neg_sqrt_div {C : ℕ} (hC : 0 < C) :
    Negligible fun N => (2 : ℝ)⁻¹ ^ Nat.sqrt (N / C) :=
  negligible_inv_pow_sqrt_div one_lt_two hC

/-- `e^{-√(N / C)}` is negligible in `N` (Inf-4.4, the 3-colouring bound). -/
theorem negligible_exp_neg_sqrt_div {C : ℕ} (hC : 0 < C) :
    Negligible fun N => Real.exp (-(Nat.sqrt (N / C) : ℝ)) := by
  have h1 : (1 : ℝ) < Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  refine (negligible_inv_pow_sqrt_div h1 hC).mono ⟨0, fun n _ => le_of_eq ?_⟩
  congr 1
  rw [Real.exp_neg, inv_pow, ← Real.exp_nat_mul, mul_one]

/-- A function bounded by `a^{-√(N / C)}` is negligible (Inf-4.4 in the form used by the
protocol theorems: a bound `a^{-n}` in the number of vertices `n ≥ √(|x| / C)` is a bound
`a^{-√(|x| / C)}` in the instance length). -/
theorem negligible_of_le_inv_pow_sqrt_div {a : ℝ} (ha : 1 < a) {C : ℕ} (hC : 0 < C)
    {ν : ℕ → ℝ} (hν : ∀ N, |ν N| ≤ a⁻¹ ^ Nat.sqrt (N / C)) : Negligible ν :=
  (negligible_inv_pow_sqrt_div ha hC).mono ⟨0, fun N _ => by
    rw [abs_of_nonneg (pow_nonneg (inv_nonneg.mpr (zero_le_one.trans ha.le)) _)]
    exact hν N⟩

/-- A bound `a^{-n}` in a parameter `n ≥ √(N / C)` transfers to `a^{-√(N / C)}`
(monotonicity of `a⁻¹ ^ ·` for `a > 1`). -/
theorem inv_pow_le_inv_pow_sqrt_div {a : ℝ} (ha : 1 < a) {C N n : ℕ}
    (hn : Nat.sqrt (N / C) ≤ n) : a⁻¹ ^ n ≤ a⁻¹ ^ Nat.sqrt (N / C) :=
  pow_le_pow_of_le_one (inv_nonneg.mpr (zero_le_one.trans ha.le)) (inv_le_one_of_one_le₀ ha.le) hn

end TCSlib.Cryptography

## ===== TCSlib/Cryptography/ZeroKnowledge/Commitment.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.HardCore
import TCSlib.Cryptography.ZeroKnowledge.CommitmentLemmas
import TCSlib.Cryptography.ZeroKnowledge.Interaction
import TCSlib.Cryptography.Pseudorandom.Indistinguishability
import TCSlib.Cryptography.Pseudorandom.GeneratorFromPermutation
import TCSlib.Cryptography.Asymptotic.HardCorePermutation

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Commitment schemes and their construction from a one-way permutation

The material of [PS10, §4.7.1]: single-message commitment schemes [PS10, Definition 126.3]
(a deterministic polynomial-time `Com` with randomness polynomial `ℓ`; *binding*: distinct
values never commit to the same string; *hiding*: commitments to any two values of the same
length are computationally indistinguishable), multi-value hiding "by a simple hybrid
argument" (Claim-126.a), and the construction from a one-way permutation `f` with a hard-core
predicate `h` [PS10, Theorem 126.4]: `Com(b, r) = f(r) ‖ (b ⊕ h(r))` for one bit (Alg-127.a),
extended bitwise to `n`-bit values with independent randomness (`ℓ(n) = n²`). Binding
"directly follows from the construction" (Claim-127.b: `f` is injective and `⊕` cancels);
one-bit hiding is the predictor reduction of [PS10, Theorem 104.4] (Claim-127.c: a
distinguisher between `Com(0, ·)` and `Com(1, ·)` with advantage `ε` predicts `h(r)` from
`f(r)` with probability exactly `1/2 + ε/2`); `n`-bit hiding is the "show this!" hybrid over
the bits (Claim-127.d, Claim-126.a with single-bit values).

Two layers (foundation decision D2). The *concrete* layer reuses the frozen Garg development:
the one-bit scheme `Com(b, ·)` is `owpGen`/`owpGenNot` with `β := Unit`
(`Pseudorandom/GeneratorFromPermutation.lean`), its predictor is `owpPredictorSnoc` of
`Asymptotic/HardCore.lean`, and `predProb_owpPredictor_false/true` **are** Claim-127.c; the
coordinatewise hybrid lemma `exists_pairRed_ge` (new, concrete) generalises
`exists_multicopyRed_ge` and carries Claim-126.a and Claim-127.d. The *asymptotic* layer states
the frozen `Commitment` structure, multi-value hiding and Theorem 126.4 for `NUPPT`
distinguishers. The hiding fills do **not** sample the other coordinates of the hybrid: by
averaging over the reduction's coins (`CommitmentLemmas.exists_fixCoins`) a fixed choice of
the other commitments does at least as well, and the reduction machine merely splices the
challenge between two hard-wired strings (`CommitmentLemmas.exists_spliceRed`,
`exists_pairSpliceRed`) — the non-uniformity of [PS10, Definition 126.3] at work, so no
evaluator of `Com` is needed. The proof infrastructure (averaging, coin transport, tuple
splitting, the splice machines and the bitwise commitment loop `ComLoop` behind the
polynomial-time evaluator of Alg-127.a) is `TCSlib.Cryptography.ZeroKnowledge.CommitmentLemmas`.

**Deviation:** `Commitment`: binding clause with `v₀ ≠ v₁` (source error); `n` an explicit
argument, colours padded to `n` bits (DQ4). In the string form `Com ⟨v, r⟩` the parameter is
`n = |v|`; the 3-colouring protocol pads its 2-bit colours to `n` bits.

## Main definitions

* `TCSlib.Cryptography.Commitment` — commitment scheme [PS10, Definition 126.3] (Def-126.3);
  `TCSlib.Cryptography.multiCom` — a vector of commitments as one string (Claim-126.a).
* `TCSlib.Cryptography.pairTuple`, `pairHybrid`, `pairRed` — coordinatewise products, their
  hybrids and the hybrid reduction (the concrete content of Claim-126.a and Claim-127.d).
* `TCSlib.Cryptography.bitCom` — the one-bit scheme `Com(b, r) = f(r) ‖ (b ⊕ h(r))`
  (Alg-127.a); `TCSlib.Cryptography.owpCom`, `owpComAt`, `owpComStr`, `owpComLen` — the
  `n`-bit scheme (typed, at a parameter, as the string function of `Commitment`; `ℓ(n) = n²`).
* `TCSlib.Cryptography.BitHiding` — hiding of the one-bit scheme against `NUPPT`s.

## Main results

* `TCSlib.Cryptography.exists_pairRed_ge` — the coordinatewise hybrid lemma (concrete);
  `TCSlib.Cryptography.Commitment.multiHiding` — multi-value hiding (Claim-126.a).
* `TCSlib.Cryptography.bitCom_inj`, `owpCom_inj`, `owpComStr_binding` — binding of
  Alg-127.a (Claim-127.b, proved).
* `TCSlib.Cryptography.exists_bitComPredictor` — single-bit hiding is the predictor
  reduction (Claim-127.c, concrete, proved); `HardCore.bitHiding` — its asymptotic form;
  `BitHiding.owpComStr_hides` — the bitwise hybrid (Claim-127.d).
* `TCSlib.Cryptography.owp_commitment` — **[PS10, Theorem 126.4]**: a one-way permutation
  with a hard-core predicate gives a commitment scheme; `exists_commitment_of_owp_hardCore` —
  the existential headline; `exists_commitment_of_owp` — the text's form, from a one-way
  permutation alone (Goldreich–Levin, `exists_owp_hardCore`); `bitCom_false_eq_owpGenPRG` —
  `Com(0, ·)` is the generator of [PS10, Theorem 79.4]; `owpComStr_polyTimeComputable` — its
  `Com` is polynomial-time (the bitwise loop `CommitmentLemmas.ComLoop`).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.7.1: Definition 126.3, Theorem 126.4; §3.3.3–3.3.4: Definition 78.3, Theorem 79.4;
  §3.5.2: Theorem 104.4; Theorem 87.3, Goldreich–Levin.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §3.3.2 (Construction 3.2, Theorem 3.2) and Lemma 3.3 (the
  multicopy hybrid argument).
-/

namespace TCSlib.Cryptography

open Complexity Turing

/-! ## Commitment schemes [PS10, Definition 126.3] -/

/-- A **commitment scheme** [PS10, Definition 126.3] (Def-126.3): a deterministic
polynomial-time string function `Com` (on the pair `⟨v, r⟩`) with a randomness polynomial `ℓ`
such that (1) *binding*: for all `n`, all distinct `v₀, v₁ ∈ {0,1}^n` and all
`r₀, r₁ ∈ {0,1}^{ℓ(n)}`, `Com(v₀, r₀) ≠ Com(v₁, r₁)`; (2) *hiding*: for every non-uniform PPT
`D` there is a negligible `ε` such that for every `n` and `v₀, v₁ ∈ {0,1}^n`, `D` (run at
parameter `n`) distinguishes `{r ← {0,1}^{ℓ(n)} : Com(v₀, r)}` from
`{r ← {0,1}^{ℓ(n)} : Com(v₁, r)}` with advantage at most `ε(n)`.

**Deviation:** `Commitment`: binding clause with `v₀ ≠ v₁` (source error); `n` an explicit
argument, colours padded to `n` bits (DQ4). As printed, binding is unsatisfiable (`v₀ = v₁`,
`r₀ = r₁`); the string form's parameter is `n = |v|`, typed users supply `n` explicitly; the
distinguisher's verdict is the string `[true]` (`NUPPT.distinguisherL`, Deviation 4). Binding
constrains only values of the same length `n` with randomness of length exactly `ℓ(n)`, as in
the text, so a protocol that opens a general `Commitment` must check those lengths, as the
3-colouring verifier `colVerify` does (gate 03e, note 12). -/
structure Commitment (Com : List Bool → List Bool) (ℓ : PolyExpr) : Prop where
  /-- `Com` is computable in deterministic polynomial time. -/
  easy : PolyTimeComputable Com
  /-- Binding: distinct values of length `n` never commit to the same string. -/
  binding : ∀ n (v₀ v₁ r₀ r₁ : List Bool), v₀.length = n → v₁.length = n →
    r₀.length = ℓ.eval n → r₁.length = ℓ.eval n → v₀ ≠ v₁ →
    Com (pairEncode v₀ r₀) ≠ Com (pairEncode v₁ r₁)
  /-- Hiding: commitments to any two `n`-bit values are indistinguishable for every `NUPPT`. -/
  hides : ∀ D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n (v₀ v₁ : Fin n → Bool),
    distAdv (fun r : Fin (ℓ.eval n) → Bool => Com (pairEncode (List.ofFn v₀) (List.ofFn r)))
      (fun r : Fin (ℓ.eval n) → Bool => Com (pairEncode (List.ofFn v₁) (List.ofFn r)))
      (D.distinguisherL n) ≤ ε n

/-- Binding in typed form [PS10, Definition 126.3 (1)]: distinct `n`-bit values with any
`ℓ(n)`-bit randomness commit to different strings (used by Lem-127.f). -/
theorem Commitment.binding_ofFn {Com : List Bool → List Bool} {ℓ : PolyExpr}
    (hC : Commitment Com ℓ) {n : ℕ} {v₀ v₁ : Fin n → Bool} (hne : v₀ ≠ v₁)
    (r₀ r₁ : Fin (ℓ.eval n) → Bool) :
    Com (pairEncode (List.ofFn v₀) (List.ofFn r₀)) ≠
      Com (pairEncode (List.ofFn v₁) (List.ofFn r₁)) :=
  hC.binding n _ _ _ _ (List.length_ofFn) (List.length_ofFn) (List.length_ofFn)
    (List.length_ofFn) (fun h => hne (List.ofFn_injective h))

/-! ## The coordinatewise hybrid lemma (concrete content of Claim-126.a) -/

section Hybrids

variable {σ τ γ ρ : Type*} [Fintype σ] [Fintype τ] [Fintype ρ] {t : ℕ}

/-- The coordinatewise product of a family of samplers: coordinate `i` is `X i` on the `i`-th
seed, all seeds independent (`copies t X` when all `X i` coincide). -/
def pairTuple (X : Fin t → σ → γ) : (Fin t → σ) → Fin t → γ :=
  fun s i => X i (s i)

/-- The `k`-th hybrid between the products of `X` and `Y`: coordinates `< k` are sampled from
`Y`, the others from `X` [PS10, Lemma 71.6, the hybrids `H_k` of Claim-126.a]. -/
def pairHybrid (X : Fin t → σ → γ) (Y : Fin t → τ → γ) (k : ℕ) :
    (Fin t → σ) × (Fin t → τ) → Fin t → γ :=
  fun s i => if (i : ℕ) < k then Y i (s.2 i) else X i (s.1 i)

/-- The hybrid reduction at coordinate `k`: on a challenge `z` (a sample of `X k` or of `Y k`)
it samples coordinates `< k` from `Y`, coordinates `> k` from `X`, plants `z` at position `k`
and calls `D` once (the reduction of Claim-126.a). -/
def pairRed (X : Fin t → σ → γ) (Y : Fin t → τ → γ) (k : Fin t) (D : (Fin t → γ) → ρ → Bool) :
    γ → ((Fin t → σ) × (Fin t → τ)) × ρ → Bool :=
  fun z c => D (fun i => if (i : ℕ) < k then Y i (c.1.2 i) else if (i : ℕ) = k then z
    else X i (c.1.1 i)) c.2

/-- The zeroth hybrid is the product of `X`. -/
theorem acceptProb_pairHybrid_zero [Nonempty τ] (X : Fin t → σ → γ) (Y : Fin t → τ → γ)
    (D : (Fin t → γ) → ρ → Bool) :
    acceptProb (pairHybrid X Y 0) D = acceptProb (pairTuple X) D := by
  have h : pairHybrid X Y 0 = fun s => pairTuple X s.1 := by
    funext s i; simp [pairHybrid, pairTuple]
  rw [h, acceptProb_fst]

/-- The `t`-th hybrid is the product of `Y`. -/
theorem acceptProb_pairHybrid_self [Nonempty σ] (X : Fin t → σ → γ) (Y : Fin t → τ → γ)
    (D : (Fin t → γ) → ρ → Bool) :
    acceptProb (pairHybrid X Y t) D = acceptProb (pairTuple Y) D := by
  have h : pairHybrid X Y t = fun s => pairTuple Y s.2 := by
    funext s i; simp [pairHybrid, pairTuple, i.isLt]
  rw [h, acceptProb_snd]

/-- On a sample of `X k`, the reduction at `k` simulates the `k`-th hybrid for `D`.

**Proof sketch.** Position `k` holds a sample of `X k` in the `k`-th hybrid; overwriting the
ignored seed at position `k` with the challenge's seed leaves the seed tuple uniform
(`acceptProb_update`), as in `acceptProb_multicopyRed_left`. -/
theorem acceptProb_pairRed_left [Nonempty σ] (X : Fin t → σ → γ) (Y : Fin t → τ → γ)
    (k : Fin t) (D : (Fin t → γ) → ρ → Bool) :
    acceptProb (X k) (pairRed X Y k D) = acceptProb (pairHybrid X Y k) D := by
  refine (acceptProb_bind (X k) (fun z (s : (Fin t → σ) × (Fin t → τ)) (i : Fin t) =>
    if (i : ℕ) < k then Y i (s.2 i) else if (i : ℕ) = k then z else X i (s.1 i)) D).trans ?_
  refine Eq.trans ?_ (acceptProb_update (ρ := ρ) k
    (fun u (s' : Fin t → τ) => pairHybrid X Y k (u, s')) D)
  congr 1
  funext w i
  simp only [pairHybrid, Function.update_apply, Fin.ext_iff]
  rcases lt_trichotomy (i : ℕ) k with hlt | heq | hgt
  · simp [hlt]
  · have hik : i = k := Fin.ext heq
    subst hik
    simp
  · simp [hgt.ne', not_lt.mpr hgt.le]

/-- On a sample of `Y k`, the reduction at `k` simulates the `(k + 1)`-th hybrid for `D`.

**Proof sketch.** As `acceptProb_pairRed_left`: position `k` holds a sample of `Y k` in the
`(k + 1)`-th hybrid (`acceptProb_update` after swapping the two seed vectors). -/
theorem acceptProb_pairRed_right [Nonempty τ] (X : Fin t → σ → γ) (Y : Fin t → τ → γ)
    (k : Fin t) (D : (Fin t → γ) → ρ → Bool) :
    acceptProb (Y k) (pairRed X Y k D) = acceptProb (pairHybrid X Y (k + 1)) D := by
  let e : τ × ((Fin t → σ) × (Fin t → τ)) ≃ τ × ((Fin t → τ) × (Fin t → σ)) :=
    (Equiv.refl τ).prodCongr (Equiv.prodComm _ _)
  refine (acceptProb_bind (Y k) (fun z (s : (Fin t → σ) × (Fin t → τ)) (i : Fin t) =>
    if (i : ℕ) < k then Y i (s.2 i) else if (i : ℕ) = k then z else X i (s.1 i)) D).trans ?_
  refine Eq.trans ?_ ((acceptProb_comp_equiv e _ D).trans
    ((acceptProb_update (ρ := ρ) k
      (fun u (s : Fin t → σ) => pairHybrid X Y (k + 1) (s, u)) D).trans
    (acceptProb_comp_equiv (Equiv.prodComm _ _) (pairHybrid X Y (k + 1)) D)))
  congr 1
  funext w i
  simp only [e, pairHybrid, Function.update_apply, Fin.ext_iff, Equiv.prodCongr_apply,
    Equiv.coe_refl, Equiv.prodComm_apply, Prod.map, Prod.fst_swap, Prod.snd_swap, id]
  rcases lt_trichotomy (i : ℕ) k with hlt | heq | hgt
  · simp [hlt, Nat.lt_succ_of_lt hlt, hlt.ne]
  · have hik : i = k := Fin.ext heq
    subst hik
    simp
  · simp [hgt.ne', not_lt.mpr hgt.le, not_lt.mpr (Nat.succ_le_of_lt hgt)]

/-- **The coordinatewise hybrid lemma** (concrete content of Claim-126.a and Claim-127.d;
[PS10, Lemma 71.6] as in [Gar26, Lemma 3.3]): if `D` distinguishes `(X_1(s_1), …, X_t(s_t))`
from `(Y_1(s_1), …, Y_t(s_t))` with advantage `ε` and `t ≥ 1`, then at some coordinate `k`
`pairRed X Y k D` distinguishes `X k` from `Y k` with advantage `≥ ε / t`
(`exists_multicopyRed_ge` is the case of equal pairs).

**Proof sketch.** `exists_hybrid_gap` on `k ↦ Pr[D(H_k) = 1]`; the ends are the two
products (`acceptProb_pairHybrid_zero/self`) and the reduction at `k` accepts `X k`, `Y k`
with the acceptance probabilities of `H_k`, `H_{k+1}` (`acceptProb_pairRed_left/right`). -/
theorem exists_pairRed_ge [Nonempty σ] [Nonempty τ] (X : Fin t → σ → γ) (Y : Fin t → τ → γ)
    (ht : 0 < t) (D : (Fin t → γ) → ρ → Bool) :
    ∃ k : Fin t, distAdv (pairTuple X) (pairTuple Y) D / t ≤
      distAdv (X k) (Y k) (pairRed X Y k D) := by
  obtain ⟨k, hk, hgap⟩ := exists_hybrid_gap (fun i => acceptProb (pairHybrid X Y i) D) ht
  refine ⟨⟨k, hk⟩, ?_⟩
  unfold distAdv
  rw [acceptProb_pairRed_left, acceptProb_pairRed_right, ← acceptProb_pairHybrid_zero X Y D,
    ← acceptProb_pairHybrid_self X Y D]
  exact hgap

end Hybrids

/-! ## Multi-value hiding (Claim-126.a) -/

/-- A vector of `q` commitments as one string: the right-nested pair encoding
(`Strategy.encodeMsgs`) of the list `Com(v_1, r_1), …, Com(v_q, r_q)` — the form in which the
3-colouring prover sends its commitments ([PS10, Protocol 127.5]). -/
def multiCom (Com : List Bool → List Bool) {q n m : ℕ} (v : Fin q → Fin n → Bool)
    (r : Fin q → Fin m → Bool) : List Bool :=
  Strategy.encodeMsgs (List.ofFn fun i => Com (pairEncode (List.ofFn (v i)) (List.ofFn (r i))))

/-- The advice bound of the multi-value hiding reduction: `3 q(n) (2 C (2n + 3 + ℓ(n))^c + 2) + 2`,
where `C (|x|+1)^c` bounds `|Com x|` — the length of the pair `⟨pre_n, suf_n⟩` of the two
hard-wired strings of commitments (`CommitmentLemmas.length_encodeMsgs_le`). -/
private def multiAdvBound (ℓ q : PolyExpr) (C c : ℕ) : PolyExpr :=
  .add (.mul (.const 3) (.mul q (.add (.mul (.const 2) (.mul (.const C)
    (.pow (.add (.add (.mul (.const 2) .var) (.const 3)) ℓ) c))) (.const 2)))) (.const 2)

/-- Unfolding the advice bound of the multi-value hiding reduction. -/
private theorem multiAdvBound_eval (ℓ q : PolyExpr) (C c n : ℕ) :
    (multiAdvBound ℓ q C c).eval n =
      3 * (q.eval n * (2 * (C * (2 * n + 3 + ℓ.eval n) ^ c) + 2)) + 2 := rfl

open CommitmentLemmas in
/-- **The per-parameter bound of Claim-126.a**: at each `n` there are two strings `pre`, `suf`
of bounded length and two values `a, a' ∈ {0,1}^n` such that every pair of `q(n)`-vectors of
values is distinguished by `D` with advantage at most `q(n)` times the advantage of the
spliced distinguisher `z ↦ D(1^n, pre ++ ⟨z, suf⟩)` between `Com(a, ·)` and `Com(a', ·)`.

**Proof sketch.** For `t := q(n) = 0` both distributions coincide. Otherwise take a worst pair
`(v, v')` (`Finset.exists_max_image`); `multiCom` is `encodeMsgs ∘ List.ofFn ∘ pairTuple` of
`X i := r ↦ Com ⟨v i, r⟩`, `Y i := r ↦ Com ⟨v' i, r⟩`, so `exists_pairRed_ge` against
`D' := D ∘ encodeMsgs ∘ List.ofFn` gives a coordinate `k`; averaging over the reduction's seed
vectors (`CommitmentLemmas.exists_fixCoins`) fixes them to some `(c_X, c_Y)`, and with the tuple
`W` of fixed commitments the reduction at `k` is `z ↦ D'(update W k z)`, which is
`D(1^n, encodeMsgs (W|_{<k}) ++ ⟨z, encodeMsgs (W|_{>k})⟩)` by
`CommitmentLemmas.encodeMsgs_ofFn_update`; `a := v k`, `a' := v' k`. The length bound is
`CommitmentLemmas.length_encodeMsgs_le` with `|W i| ≤ C (2n + 3 + ℓ(n))^c`. -/
private theorem exists_multiRed_bound {Com : List Bool → List Bool} (ℓ q : PolyExpr) (D : NUPPT)
    {C c : ℕ} (hCc : ∀ x, (Com x).length ≤ C * (x.length + 1) ^ c) (n : ℕ) :
    ∃ (pre suf : List Bool) (a a' : Fin n → Bool),
      2 * pre.length + 2 + suf.length ≤ (multiAdvBound ℓ q C c).eval n ∧
      ∀ v v' : Fin (q.eval n) → Fin n → Bool,
        distAdv (fun r : Fin (q.eval n) → Fin (ℓ.eval n) → Bool => multiCom Com v r)
          (fun r : Fin (q.eval n) → Fin (ℓ.eval n) → Bool => multiCom Com v' r)
          (D.distinguisherL n) ≤
        q.eval n * distAdv
          (fun r : Fin (ℓ.eval n) → Bool => Com (pairEncode (List.ofFn a) (List.ofFn r)))
          (fun r : Fin (ℓ.eval n) → Bool => Com (pairEncode (List.ofFn a') (List.ofFn r)))
          (fun z c => D.distinguisherL n (pre ++ pairEncode z suf) c) := by
  rw [multiAdvBound_eval]
  set t := q.eval n with ht
  rcases Nat.eq_zero_or_pos t with ht0 | htpos
  · refine ⟨[], [], fun _ => false, fun _ => false, by simp, fun v v' => ?_⟩
    have hvv : v = v' := funext fun i => absurd i.2 (by omega)
    rw [hvv]
    simp only [distAdv, sub_self, abs_zero]
    positivity
  set cm : (Fin t → Fin n → Bool) → Fin t → (Fin (ℓ.eval n) → Bool) → List Bool :=
    fun v i s => Com (pairEncode (List.ofFn (v i)) (List.ofFn s)) with hcm
  set D' : (Fin t → List Bool) → D.Coins n → Bool :=
    fun w c => D.distinguisherL n (Strategy.encodeMsgs (List.ofFn w)) c with hD'
  have hadv : ∀ v v' : Fin t → Fin n → Bool,
      distAdv (fun r : Fin t → Fin (ℓ.eval n) → Bool => multiCom Com v r)
        (fun r : Fin t → Fin (ℓ.eval n) → Bool => multiCom Com v' r) (D.distinguisherL n) =
      distAdv (pairTuple (cm v)) (pairTuple (cm v')) D' := fun v v' => rfl
  obtain ⟨⟨v, v'⟩, -, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun p : (Fin t → Fin n → Bool) × (Fin t → Fin n → Bool) =>
      distAdv (pairTuple (cm p.1)) (pairTuple (cm p.2)) D') Finset.univ_nonempty
  obtain ⟨k, hk⟩ := exists_pairRed_ge (cm v) (cm v') htpos D'
  obtain ⟨c₀, hc₀⟩ := exists_fixCoins (cm v k) (cm v' k) (pairRed (cm v) (cm v') k D')
  set W : Fin t → List Bool :=
    fun i => if (i : ℕ) < k then cm v' i (c₀.2 i) else cm v i (c₀.1 i) with hW
  set pre : List Bool := Strategy.encodeMsgs (List.ofFn fun i : Fin k => W (Fin.castLE k.2.le i))
    with hpre
  set suf : List Bool :=
    Strategy.encodeMsgs (List.ofFn fun i : Fin (t - k - 1) => W ⟨k + 1 + i, by omega⟩) with hsuf
  have hred : ∀ z c, pairRed (cm v) (cm v') k D' z (c₀, c) =
      D.distinguisherL n (pre ++ pairEncode z suf) c := by
    intro z c
    have hTz : (fun i : Fin t => if (i : ℕ) < k then cm v' i (c₀.2 i)
        else if (i : ℕ) = k then z else cm v i (c₀.1 i)) = Function.update W k z := by
      funext i
      rw [Function.update_apply]
      simp only [hW]
      rcases lt_trichotomy (i : ℕ) k with hlt | heq | hgt
      · have hne : i ≠ k := fun hik => by rw [hik] at hlt; exact lt_irrefl _ hlt
        simp [hlt, hne]
      · have : i = k := Fin.ext heq
        subst this
        simp
      · have hne : i ≠ k := fun hik => by rw [hik] at hgt; exact lt_irrefl _ hgt
        simp [hgt.ne', not_lt.mpr hgt.le, hne]
    dsimp only [pairRed]
    simp only [hD']
    rw [hTz, encodeMsgs_ofFn_update]
  have hWlen : ∀ i, (W i).length ≤ C * (2 * n + 3 + ℓ.eval n) ^ c := by
    intro i
    simp only [hW, hcm]
    split_ifs <;>
    · refine (hCc _).trans (le_of_eq ?_)
      rw [length_pairEncode, List.length_ofFn, List.length_ofFn]
      ring_nf
  refine ⟨pre, suf, v k, v' k, ?_, fun v₀ v₁ => ?_⟩
  · have h1 := length_encodeMsgs_le (List.ofFn fun i : Fin k => W (Fin.castLE k.2.le i))
      (C * (2 * n + 3 + ℓ.eval n) ^ c) (List.forall_mem_ofFn_iff.2 fun j => hWlen _)
    have h2 := length_encodeMsgs_le (List.ofFn fun i : Fin (t - k - 1) => W ⟨k + 1 + i, by omega⟩)
      (C * (2 * n + 3 + ℓ.eval n) ^ c) (List.forall_mem_ofFn_iff.2 fun j => hWlen _)
    rw [List.length_ofFn] at h1 h2
    have hk1 : (k : ℕ) * (2 * (C * (2 * n + 3 + ℓ.eval n) ^ c) + 2) ≤
        t * (2 * (C * (2 * n + 3 + ℓ.eval n) ^ c) + 2) := Nat.mul_le_mul_right _ k.2.le
    have hk2 : (t - k - 1) * (2 * (C * (2 * n + 3 + ℓ.eval n) ^ c) + 2) ≤
        t * (2 * (C * (2 * n + 3 + ℓ.eval n) ^ c) + 2) := Nat.mul_le_mul_right _ (by omega)
    simp only [hpre, hsuf]
    omega
  · rw [hadv v₀ v₁]
    refine (hmax (v₀, v₁) (Finset.mem_univ _)).trans ?_
    have ht' : (0 : ℝ) < t := Nat.cast_pos.2 htpos
    rw [div_le_iff₀ ht'] at hk
    have h1 : distAdv (pairTuple (cm v)) (pairTuple (cm v')) D' ≤
        t * distAdv (cm v k) (cm v' k) (pairRed (cm v) (cm v') k D') := by linarith
    refine h1.trans (mul_le_mul_of_nonneg_left (hc₀.trans (le_of_eq ?_)) (Nat.cast_nonneg t))
    rw [show (fun z c => pairRed (cm v) (cm v') k D' z (c₀, c)) =
      fun z c => D.distinguisherL n (pre ++ pairEncode z suf) c
      from funext fun z => funext fun c => hred z c]

/-- **Every commitment scheme is multi-value hiding** [PS10, p. 126, "it directly follows by
a simple hybrid argument that any commitment scheme is multi-value secure"] (Claim-126.a):
for a commitment scheme `(Com, ℓ)`, a polynomial `q` and a non-uniform PPT `D` there is a
negligible `ε` such that for every `n` and every two vectors `v, v'` of `q(n)` values of `n`
bits, `D` (at parameter `n`) distinguishes `(Com(v_i, r_i))_i` from `(Com(v'_i, r_i))_i`,
with independent uniform `r_i ∈ {0,1}^{ℓ(n)}`, with advantage at most `ε(n)`.

**Deviation:** the text does not state the notion; this is the analogue of multi-message
security [PS10, Definition 93.1], the vector encoded by `Strategy.encodeMsgs`, values after `ε`.

**Proof sketch.** Fix `D` and let `C (|x|+1)^c` bound `|Com x|` (`hC.easy.output_length_le`).
At each `n`, `exists_multiRed_bound` chooses a worst pair `(v_n, v'_n)`
(`Finset.exists_max_image`), a coordinate `k_n` from the coordinatewise hybrid lemma
`exists_pairRed_ge` applied to `X i := r ↦ Com ⟨v_n i, r⟩`, `Y i := r ↦ Com ⟨v'_n i, r⟩`
against `D' := D.distinguisherL n ∘ encodeMsgs ∘ List.ofFn`, and — by averaging over the
reduction's seed vectors (`CommitmentLemmas.exists_fixCoins`) — a fixed choice of the other
`q(n) − 1` commitments, so that the reduction is `z ↦ D(1^n, pre_n ++ ⟨z, suf_n⟩)` for two
strings `pre_n`, `suf_n` of total length `≤ multiAdvBound` (`CommitmentLemmas.encodeMsgs_ofFn_update`,
`length_encodeMsgs_le`), and `ε_D(n) ≤ q(n) · distAdv (Com ⟨v_n k_n, ·⟩) (Com ⟨v'_n k_n, ·⟩) (that reduction)`.
The machine `B := CommitmentLemmas.exists_pairSpliceRed D pre suf` has `D`'s coins, advice
`⟨⟨pre_n, suf_n⟩, D.advice n⟩` and calls `D` once (`NUPPT.exists_comp`, `NUPPT.exists_withAdvice`);
by coin transport (`CommitmentLemmas.acceptProb_distinguisherL_of_runAtL`) its advantage is the
reduction's, so `hC.hides B` gives `ε_D(n) ≤ q(n) ε_B(n)`, negligible by
`EnsembleLemmas.negligible_polyExpr_mul`; take `ε := q · ε_B`. -/
theorem Commitment.multiHiding {Com : List Bool → List Bool} {ℓ : PolyExpr}
    (hC : Commitment Com ℓ) (q : PolyExpr) (D : NUPPT) :
    ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n (v v' : Fin (q.eval n) → Fin n → Bool),
      distAdv (fun r : Fin (q.eval n) → Fin (ℓ.eval n) → Bool => multiCom Com v r)
        (fun r : Fin (q.eval n) → Fin (ℓ.eval n) → Bool => multiCom Com v' r)
        (D.distinguisherL n) ≤ ε n := by
  obtain ⟨C, c, hCc⟩ := hC.easy.output_length_le
  choose pre suf a a' hlen hkey using exists_multiRed_bound ℓ q D hCc
  obtain ⟨B, hBc, hB⟩ := CommitmentLemmas.exists_pairSpliceRed D pre suf
    (multiAdvBound ℓ q C c) hlen
  obtain ⟨ε, hε, hεB⟩ := hC.hides B
  refine ⟨fun n => q.eval n * ε n, EnsembleLemmas.negligible_polyExpr_mul q hε, fun n v v' => ?_⟩
  refine (hkey n v v').trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
  have hε' := hεB n (a n) (a' n)
  unfold distAdv at hε' ⊢
  rwa [CommitmentLemmas.acceptProb_distinguisherL_of_runAtL hBc _
    (fun y => pre n ++ pairEncode y (suf n)) (hB n),
    CommitmentLemmas.acceptProb_distinguisherL_of_runAtL hBc _
    (fun y => pre n ++ pairEncode y (suf n)) (hB n)] at hε'

/-! ## The construction from a one-way permutation [PS10, Theorem 126.4] -/

/-- **The one-bit commitment of [PS10, proof of Theorem 126.4]** (Alg-127.a):
`Com(b, r) = f(r) ‖ (b ⊕ h(r))` for a permutation `f` of `{0,1}^n`, a predicate `h` and
randomness `r ∈ {0,1}^n` (`ℓ(n) = n`), an `(n + 1)`-bit string with the masked bit last
(`owpGen f h` / `owpGenNot f h` of the Garg layer up to the trivial `Unit` coordinate). -/
def bitCom {n : ℕ} (f : (Fin n → Bool) ≃ (Fin n → Bool)) (h : (Fin n → Bool) → Bool)
    (b : Bool) (r : Fin n → Bool) : Fin (n + 1) → Bool :=
  Fin.snoc (f r) (xor b (h r))

/-- Unfolding: the first `n` bits of `Com(b, r)` are `f(r)`. -/
@[simp] theorem bitCom_castSucc {n : ℕ} (f : (Fin n → Bool) ≃ (Fin n → Bool))
    (h : (Fin n → Bool) → Bool) (b : Bool) (r : Fin n → Bool) (i : Fin n) :
    bitCom f h b r i.castSucc = f r i := by
  simp [bitCom]

/-- Unfolding: the last bit of `Com(b, r)` is `b ⊕ h(r)`. -/
@[simp] theorem bitCom_last {n : ℕ} (f : (Fin n → Bool) ≃ (Fin n → Bool))
    (h : (Fin n → Bool) → Bool) (b : Bool) (r : Fin n → Bool) :
    bitCom f h b r (Fin.last n) = xor b (h r) := by
  simp [bitCom]

/-- `Com(0, ·)` is `f(r) ‖ h(r)`. -/
theorem bitCom_false {n : ℕ} (f : (Fin n → Bool) ≃ (Fin n → Bool)) (h : (Fin n → Bool) → Bool) :
    bitCom f h false = fun r => Fin.snoc (f r) (h r) := by
  funext r; simp [bitCom]

/-- `Com(1, ·)` is `f(r) ‖ ¬h(r)`. -/
theorem bitCom_true {n : ℕ} (f : (Fin n → Bool) ≃ (Fin n → Bool)) (h : (Fin n → Bool) → Bool) :
    bitCom f h true = fun r => Fin.snoc (f r) (!h r) := by
  funext r; simp [bitCom]

/-- The commitment to `0` is the generator `G(s) = f(s) ‖ h(s)` of [PS10, Theorem 79.4]: the
hiding of Alg-127.a and the pseudorandomness of `owpGenPRG` rest on the same reduction. -/
theorem bitCom_false_eq_owpGenPRG (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) (n : ℕ)
    (r : Fin n → Bool) (i : Fin (n + 1)) :
    bitCom (P.f n) (h n) false r i = (owpGenPRG P h).G n r i := by
  simp [bitCom, owpGenPRG, PRG.oneBit]

/-- **Binding of the one-bit scheme** [PS10, proof of Theorem 126.4, "it directly follows from
the construction that `Com` is binding"] (Claim-127.b, single bit): `Com(b₀, r₀) = Com(b₁, r₁)`
forces `r₀ = r₁` (the first `n` bits are `f(r)` and `f` is injective) and then `b₀ = b₁`
(`⊕ h(r)` cancels). -/
theorem bitCom_inj {n : ℕ} (f : (Fin n → Bool) ≃ (Fin n → Bool)) (h : (Fin n → Bool) → Bool)
    {b₀ b₁ : Bool} {r₀ r₁ : Fin n → Bool} (heq : bitCom f h b₀ r₀ = bitCom f h b₁ r₁) :
    b₀ = b₁ ∧ r₀ = r₁ := by
  have hf : f r₀ = f r₁ := by
    funext i
    have := congrFun heq i.castSucc
    simpa using this
  have hr : r₀ = r₁ := f.injective hf
  subst hr
  refine ⟨?_, rfl⟩
  have hb := congrFun heq (Fin.last n)
  simp only [bitCom_last] at hb
  cases b₀ <;> cases b₁ <;> cases h r₀ <;> simp_all

/-- **The `n`-bit commitment of [PS10, proof of Theorem 126.4]** (Alg-127.a): "a full-fledged
commitment scheme to a value `v ∈ {0,1}^n` can be obtained by individually committing to each
bit of `v`" — `Com(v, (r_i)_i) = (Com(v_i, r_i))_i`, `n` independent `n`-bit `r_i` (`ℓ(n) = n²`). -/
def owpCom (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) (n : ℕ) (v : Fin n → Bool)
    (r : Fin n → Fin n → Bool) : Fin n → Fin (n + 1) → Bool :=
  fun i => bitCom (P.f n) (h n) (v i) (r i)

/-- The typed `n`-bit scheme is the coordinatewise product of the one-bit schemes to the
bits of `v` (the form `exists_pairRed_ge` applies to). -/
theorem owpCom_eq_pairTuple (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) (n : ℕ)
    (v : Fin n → Bool) : owpCom P h n v = pairTuple fun i => bitCom (P.f n) (h n) (v i) := rfl

/-- **Binding of the `n`-bit scheme** (Claim-127.b): equal commitment vectors have equal values
and equal randomness, coordinate by coordinate from `bitCom_inj`. -/
theorem owpCom_inj (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) {n : ℕ}
    {v₀ v₁ : Fin n → Bool} {r₀ r₁ : Fin n → Fin n → Bool}
    (heq : owpCom P h n v₀ r₀ = owpCom P h n v₁ r₁) : v₀ = v₁ ∧ r₀ = r₁ := by
  have hi := fun i => bitCom_inj (P.f n) (h n) (congrFun heq i)
  exact ⟨funext fun i => (hi i).1, funext fun i => (hi i).2⟩

/-- The `n`-bit scheme at an explicit parameter `n` on strings: the value is read as `n` bits,
the randomness as `n²` bits (`padFin`, total), the `n` commitments of `n + 1` bits are
concatenated into one `n(n+1)`-bit string (`FunFamily.blocks`). -/
def owpComAt (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) (n : ℕ) (v r : List Bool) :
    List Bool :=
  List.ofFn ((FunFamily.blocks n (n + 1)).symm
    (owpCom P h n (padFin n v) (FunFamily.blocks n n (padFin (n * n) r))))

/-- **The string function `Com` of Alg-127.a**: on `⟨v, r⟩` it commits to the `|v|` bits of
`v` with the `|v|²` bits of `r` (`owpComAt` at `n = |v|`); the `Com` of `Commitment`. -/
def owpComStr (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) (w : List Bool) : List Bool :=
  owpComAt P h (pairFstD w).length (pairFstD w) (pairSndD w)

/-- The randomness polynomial of Alg-127.a: `ℓ(n) = n · n`. -/
def owpComLen : PolyExpr := .mul .var .var

/-- `ℓ(n) = n²`. -/
@[simp] theorem owpComLen_eval (n : ℕ) : owpComLen.eval n = n * n := rfl

/-- Unfolding `owpComStr` on a well-formed pair. -/
theorem owpComStr_pairEncode (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool)
    (v r : List Bool) : owpComStr P h (pairEncode v r) = owpComAt P h v.length v r := by
  simp [owpComStr]

/-- Unfolding `owpComAt` on encoded typed arguments. -/
theorem owpComAt_ofFn (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) {n : ℕ}
    (v : Fin n → Bool) (r : Fin (n * n) → Bool) :
    owpComAt P h n (List.ofFn v) (List.ofFn r) =
      List.ofFn ((FunFamily.blocks n (n + 1)).symm (owpCom P h n v (FunFamily.blocks n n r))) := by
  simp [owpComAt, padFin_ofFn]

/-- The string scheme on encoded typed arguments is the encoded typed scheme (the bridge
between the `hides` clause and `owpCom`). -/
theorem owpComStr_ofFn (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) {n : ℕ}
    (v : Fin n → Bool) (r : Fin (owpComLen.eval n) → Bool) :
    owpComStr P h (pairEncode (List.ofFn v) (List.ofFn r)) =
      List.ofFn ((FunFamily.blocks n (n + 1)).symm (owpCom P h n v (FunFamily.blocks n n r))) := by
  rw [owpComStr_pairEncode, List.length_ofFn, owpComAt_ofFn]

/-- Two strings of length `n` with the same `n`-bit padding are equal. -/
private theorem padFin_inj {n : ℕ} {v₀ v₁ : List Bool} (hv₀ : v₀.length = n) (hv₁ : v₁.length = n)
    (h : padFin n v₀ = padFin n v₁) : v₀ = v₁ := by
  refine List.ext_getElem (hv₀.trans hv₁.symm) fun i h₁ h₂ => ?_
  have := congrFun h ⟨i, hv₀ ▸ h₁⟩
  simpa [padFin, List.getD_eq_getElem, h₁, h₂] using this

/-- **Binding of `owpComAt`** (Claim-127.b, string form at a parameter): equal commitment
strings of two `n`-bit values force the values to be equal.

**Proof sketch.** `List.ofFn` and the block equivalence are injective, so the typed
commitment vectors agree; `owpCom_inj` gives equal padded values; strings of length `n` with
equal paddings are equal. -/
theorem owpComAt_inj (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) {n : ℕ}
    {v₀ v₁ r₀ r₁ : List Bool} (hv₀ : v₀.length = n) (hv₁ : v₁.length = n)
    (heq : owpComAt P h n v₀ r₀ = owpComAt P h n v₁ r₁) : v₀ = v₁ := by
  have h1 := List.ofFn_injective heq
  have h2 := (FunFamily.blocks n (n + 1)).symm.injective h1
  exact padFin_inj hv₀ hv₁ (owpCom_inj P h h2).1

/-- **Binding of Alg-127.a** [PS10, proof of Theorem 126.4] (Claim-127.b): the binding clause
of `Commitment` for `owpComStr` — for all `n`, distinct `v₀, v₁ ∈ {0,1}^n` and any
`r₀, r₁ ∈ {0,1}^{n²}`, `Com ⟨v₀, r₀⟩ ≠ Com ⟨v₁, r₁⟩`. Only the injectivity of `f` is used. -/
theorem owpComStr_binding (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) :
    ∀ n (v₀ v₁ r₀ r₁ : List Bool), v₀.length = n → v₁.length = n →
      r₀.length = owpComLen.eval n → r₁.length = owpComLen.eval n → v₀ ≠ v₁ →
      owpComStr P h (pairEncode v₀ r₀) ≠ owpComStr P h (pairEncode v₁ r₁) := by
  intro n v₀ v₁ r₀ r₁ hv₀ hv₁ _ _ hne heq
  rw [owpComStr_pairEncode, owpComStr_pairEncode, hv₀, hv₁] at heq
  exact hne (owpComAt_inj P h hv₀ hv₁ heq)

/-! ### Hiding of the one-bit scheme (Claim-127.c) -/

/-- **Single-bit hiding is the predictor reduction** [PS10, proof of Theorem 126.4, "hiding
follows using identically the same proof as in the proof of Theorem 104.4"] (Claim-127.c,
concrete): for every distinguisher `D` between `Com(0, ·) = f(r) ‖ h(r)` and
`Com(1, ·) = f(r) ‖ ¬h(r)` there is a sign `flip` such that `owpPredictorSnoc D flip` (one call
of `D` on `f(r) ‖ σ` for a fresh coin `σ`) predicts `h(r)` from `f(r)` with probability exactly
`1/2 + distAdv(Com(0), Com(1), D) / 2`. Only bijectivity of `f` is used [Gar26, Theorem 3.2].

**Proof sketch.** This is `predProb_owpPredictor_false`/`_true` with `β := Unit`: under the
bijection `(y, (), b) ↦ y ‖ b`, `owpGen f h'` is `Com(0, ·)` and `owpGenNot f h'` is
`Com(1, ·)` (`acceptProb_fst` removes the `Unit` seed coordinate), and the prediction
experiments correspond under `(s, c) ↦ ((s, ()), c)` (`uprob_eq_of_equiv`); choose `flip`
by the sign of `Pr[D(Com(0)) = 1] - Pr[D(Com(1)) = 1]`. -/
theorem exists_bitComPredictor {ρ : Type*} [Fintype ρ] [Nonempty ρ] {n : ℕ}
    (f : (Fin n → Bool) ≃ (Fin n → Bool)) (h : (Fin n → Bool) → Bool)
    (D : (Fin (n + 1) → Bool) → ρ → Bool) :
    ∃ flip : Bool, predProb f h (owpPredictorSnoc D flip) =
      1 / 2 + distAdv (bitCom f h false) (bitCom f h true) D / 2 := by
  let e : (Fin n → Bool) × Unit × Bool ≃ (Fin (n + 1) → Bool) :=
    { toFun := fun z => Fin.snoc z.1 z.2.2
      invFun := fun t => (Fin.init t, (), t (Fin.last n))
      left_inv := fun z => by
        obtain ⟨a, -, b⟩ := z
        simp [Fin.init_snoc, Fin.snoc_last]
      right_inv := fun t => by simp [Fin.snoc_init_self] }
  have h1 : ∀ flip, predProb f h (owpPredictorSnoc D flip) =
      predProb (owpPair f) (fun w : (Fin n → Bool) × Unit => h w.1)
        (owpPredictor (fun z r => D (e z) r) flip) := fun flip => by
    unfold predProb
    exact uprob_eq_of_equiv
      ({ toFun := fun z : (Fin n → Bool) × (Bool × ρ) => ((z.1, ()), z.2)
         invFun := fun z => (z.1.1, z.2)
         left_inv := fun _ => rfl
         right_inv := fun _ => rfl } :
        (Fin n → Bool) × (Bool × ρ) ≃ ((Fin n → Bool) × Unit) × (Bool × ρ))
      fun _ => Iff.rfl
  have h0 : acceptProb (owpGen f fun w : (Fin n → Bool) × Unit => h w.1) (fun z r => D (e z) r) =
      acceptProb (bitCom f h false) D := by
    rw [bitCom_false, ← acceptProb_fst (τ := Unit) (fun r => Fin.snoc (f r) (h r)) D]
    rfl
  have h0' : acceptProb (owpGenNot f fun w : (Fin n → Bool) × Unit => h w.1)
      (fun z r => D (e z) r) = acceptProb (bitCom f h true) D := by
    rw [bitCom_true, ← acceptProb_fst (τ := Unit) (fun r => Fin.snoc (f r) (!h r)) D]
    rfl
  rcases le_total 0 (acceptProb (bitCom f h false) D - acceptProb (bitCom f h true) D) with
    hs | hs
  · refine ⟨false, ?_⟩
    rw [h1, predProb_owpPredictor_false, h0, h0', distAdv, abs_of_nonneg hs]
  · refine ⟨true, ?_⟩
    rw [h1, predProb_owpPredictor_true, h0, h0', distAdv, abs_of_nonpos hs]
    ring

/-- **Hiding of the one-bit scheme against non-uniform PPTs**: for every `NUPPT` `D` there is
a negligible `ε` such that at every `n`, `D` (at parameter `n`, on the `(n+1)`-bit string)
distinguishes `Com(0, ·)` from `Com(1, ·)` with advantage `≤ ε(n)` [PS10, Def. 126.3 (2)]. -/
def BitHiding (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) : Prop :=
  ∀ D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n,
    distAdv (bitCom (P.f n) (h n) false) (bitCom (P.f n) (h n) true)
      (D.distinguisher n (n + 1)) ≤ ε n

/-- **A hard-core predicate makes the one-bit scheme hiding** [PS10, proof of Theorem 126.4,
via the proof of Theorem 104.4] (Claim-127.c, asymptotic): if `h` is hard-core for the
permutation family `f`, then `Com(b, r) = f(r) ‖ (b ⊕ h(r))` is hiding — every `NUPPT` has
negligible advantage between `Com(0, ·)` and `Com(1, ·)` (in fact `≤ 2 ε_h(n)` for the
predictor's bound `ε_h`).

**Deviation:** the text's proof goes through the prediction lemma [PS10, Lemma 73.8]; here the
reduction is the exact one of [Gar26, Theorem 3.2] (`exists_bitComPredictor`), with the sign
of the advantage as non-uniform advice.

**Proof sketch.** Fix `D : NUPPT`. At each `n`, `exists_bitComPredictor (P.f n) (h n)
(D.distinguisher n (n+1))` gives a sign `flip_n` (`Classical.choose`) with
`predProb (P.f n) (h n) (owpPredictorSnoc D' flip_n) = 1/2 + distAdv(Com(0), Com(1), D')/2`.
The predictor machine is `owpPredMachine D flip` of `Asymptotic/HardCoreLemmas.lean` (the
machine of Theorem 79.4: advice `⟨[flip_n], D.advice n⟩`, coins `1 + D.coins`; on `⟨1^n, y⟩` it
reads the first coin `σ`, calls `D` once on `⟨1^n, y ++ [σ]⟩` with the remaining coins and
outputs `[xor (if D accepts then σ else !σ) flip_n]`), whose prediction probability is that
of `owpPredictorSnoc (D.distinguisher n (n+1)) (flip n)` (`owpPredMachine_predProb`). Then
`hh.hard A` (note `P.toFunFamily.outLen.eval n = n`) gives a negligible `ε_h` with
`1/2 + distAdv/2 ≤ 1/2 + ε_h n`, hence `distAdv ≤ 2 ε_h n`; take `ε := 2 ε_h`
(`Negligible.const_mul`). -/
theorem HardCore.bitHiding {P : PermFamily} {h : ∀ n, (Fin n → Bool) → Bool}
    (hh : HardCore P.toFunFamily h) : BitHiding P h := by
  intro D
  have hflip : ∀ n, ∃ flip : Bool,
      predProb (P.f n) (h n) (owpPredictorSnoc (D.distinguisher n (n + 1)) flip) =
        1 / 2 + distAdv (bitCom (P.f n) (h n) false) (bitCom (P.f n) (h n) true)
          (D.distinguisher n (n + 1)) / 2 :=
    fun n => exists_bitComPredictor (P.f n) (h n) _
  choose flip hflip using hflip
  obtain ⟨ε, hε, hbound⟩ := hh.hard (owpPredMachine D flip)
  refine ⟨fun n => 2 * ε n, hε.const_mul 2, fun n => ?_⟩
  have h1 : predProb (P.f n) (h n) ((owpPredMachine D flip).predictor n n) ≤ 1 / 2 + ε n :=
    hbound n
  rw [owpPredMachine_predProb] at h1
  have h3 : predProb (P.f n) (h n) (owpPredictorSnoc (D.distinguisher n (n + 1)) (flip n)) =
      predProb (P.f n) (h n) (fun y (c : Bool × D.Coins n) =>
        xor (if D.distinguisher n (n + 1) (Fin.snoc y c.1) c.2 then c.1 else !c.1) (flip n)) := rfl
  rw [← h3, hflip n] at h1
  linarith

/-! ### Hiding of the `n`-bit scheme (Claim-127.d) and Theorem 126.4 -/

open CommitmentLemmas in
/-- **The per-parameter bound of Claim-127.d**: at each `n` there are two strings `pre`, `suf`
of total length `≤ 3n(n+1)` such that every pair of `n`-bit values is distinguished by `D`
with advantage at most `n` times the advantage of the spliced distinguisher
`z ↦ D(1^n, pre ++ z ++ suf)` between `Com(0, ·)` and `Com(1, ·)`.

**Proof sketch.** For `n = 0` there is one value. Otherwise `owpComStr_ofFn` and the seed
reindexing `acceptProb_comp_equiv (blocks n n)` turn the advantage into
`distAdv (pairTuple (bc v₀)) (pairTuple (bc v₁)) D'` with `bc v i := bitCom (f n) (h n) (v i)`
and `D' := D ∘ List.ofFn ∘ (blocks n (n+1)).symm`. Take a worst pair `(v, v')`
(`Finset.exists_max_image`), a bit position `k` from `exists_pairRed_ge`, and by averaging over
the reduction's seed vectors (`CommitmentLemmas.exists_fixCoins`) a fixed choice `(c_X, c_Y)`;
with the tuple `W` of fixed one-bit commitments the reduction at `k` is `z ↦ D'(update W k z)`,
i.e. `D(1^n, pre ++ z ++ suf)` for the block strings before and after `k`
(`CommitmentLemmas.ofFn_blocks_symm_update`, lengths by `length_flatten_ofFn`). If
`v k = v' k` the advantage is `0`; otherwise the pair is `(Com(0), Com(1))` up to
`distAdv_comm`. -/
private theorem exists_bitRed_bound (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) (D : NUPPT)
    (n : ℕ) :
    ∃ pre suf : List Bool, 2 * pre.length + 2 + suf.length ≤ 3 * (n * (n + 1)) + 2 ∧
      ∀ v₀ v₁ : Fin n → Bool,
        distAdv (fun r : Fin (owpComLen.eval n) → Bool =>
            owpComStr P h (pairEncode (List.ofFn v₀) (List.ofFn r)))
          (fun r : Fin (owpComLen.eval n) → Bool =>
            owpComStr P h (pairEncode (List.ofFn v₁) (List.ofFn r)))
          (D.distinguisherL n) ≤
        n * distAdv (bitCom (P.f n) (h n) false) (bitCom (P.f n) (h n) true)
          (fun z c => D.distinguisherL n (pre ++ List.ofFn z ++ suf) c) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨[], [], by simp, fun v₀ v₁ => ?_⟩
    rw [Subsingleton.elim v₀ v₁]
    simp [distAdv]
  set D' : (Fin n → Fin (n + 1) → Bool) → D.Coins n → Bool :=
    fun w c => D.distinguisherL n (List.ofFn ((FunFamily.blocks n (n + 1)).symm w)) c with hD'
  set bc : (Fin n → Bool) → Fin n → (Fin n → Bool) → Fin (n + 1) → Bool :=
    fun v i => bitCom (P.f n) (h n) (v i) with hbc
  have hadv : ∀ v₀ v₁ : Fin n → Bool,
      distAdv (fun r : Fin (owpComLen.eval n) → Bool =>
          owpComStr P h (pairEncode (List.ofFn v₀) (List.ofFn r)))
        (fun r : Fin (owpComLen.eval n) → Bool =>
          owpComStr P h (pairEncode (List.ofFn v₁) (List.ofFn r)))
        (D.distinguisherL n) = distAdv (pairTuple (bc v₀)) (pairTuple (bc v₁)) D' := by
    intro v₀ v₁
    simp only [owpComStr_ofFn]
    unfold distAdv
    rw [← acceptProb_comp_equiv (FunFamily.blocks n n) (pairTuple (bc v₀)) D',
      ← acceptProb_comp_equiv (FunFamily.blocks n n) (pairTuple (bc v₁)) D']
    rfl
  obtain ⟨⟨v, v'⟩, -, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun p : (Fin n → Bool) × (Fin n → Bool) =>
      distAdv (pairTuple (bc p.1)) (pairTuple (bc p.2)) D') Finset.univ_nonempty
  obtain ⟨k, hk⟩ := exists_pairRed_ge (bc v) (bc v') hn D'
  obtain ⟨c₀, hc₀⟩ := exists_fixCoins (bc v k) (bc v' k) (pairRed (bc v) (bc v') k D')
  set W : Fin n → Fin (n + 1) → Bool :=
    fun i => if (i : ℕ) < k then bc v' i (c₀.2 i) else bc v i (c₀.1 i) with hW
  set pre : List Bool := (List.ofFn fun i : Fin k => List.ofFn (W (Fin.castLE k.2.le i))).flatten
    with hpre
  set suf : List Bool :=
    (List.ofFn fun i : Fin (n - k - 1) => List.ofFn (W ⟨k + 1 + i, by omega⟩)).flatten with hsuf
  have hred : ∀ z c, pairRed (bc v) (bc v') k D' z (c₀, c) =
      D.distinguisherL n (pre ++ List.ofFn z ++ suf) c := by
    intro z c
    have hTz : (fun i : Fin n => if (i : ℕ) < k then bc v' i (c₀.2 i)
        else if (i : ℕ) = k then z else bc v i (c₀.1 i)) = Function.update W k z := by
      funext i
      rw [Function.update_apply]
      simp only [hW]
      rcases lt_trichotomy (i : ℕ) k with hlt | heq | hgt
      · have hne : i ≠ k := fun hik => by rw [hik] at hlt; exact lt_irrefl _ hlt
        simp [hlt, hne]
      · have : i = k := Fin.ext heq
        subst this
        simp
      · have hne : i ≠ k := fun hik => by rw [hik] at hgt; exact lt_irrefl _ hgt
        simp [hgt.ne', not_lt.mpr hgt.le, hne]
    dsimp only [pairRed]
    simp only [hD']
    rw [hTz, ofFn_blocks_symm_update]
  refine ⟨pre, suf, ?_, fun v₀ v₁ => ?_⟩
  · simp only [hpre, hsuf]
    rw [length_flatten_ofFn, length_flatten_ofFn]
    have h1 : (k : ℕ) * (n + 1) ≤ n * (n + 1) := Nat.mul_le_mul_right _ k.2.le
    have h2 : (n - k - 1) * (n + 1) ≤ n * (n + 1) := Nat.mul_le_mul_right _ (by omega)
    omega
  · rw [hadv v₀ v₁]
    refine (hmax (v₀, v₁) (Finset.mem_univ _)).trans ?_
    have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
    rw [div_le_iff₀ hn'] at hk
    have h1 : distAdv (pairTuple (bc v)) (pairTuple (bc v')) D' ≤
        n * distAdv (bc v k) (bc v' k) (pairRed (bc v) (bc v') k D') := by linarith
    refine h1.trans (mul_le_mul_of_nonneg_left (hc₀.trans ?_) (Nat.cast_nonneg n))
    rw [show (fun z c => pairRed (bc v) (bc v') k D' z (c₀, c)) =
      fun z c => D.distinguisherL n (pre ++ List.ofFn z ++ suf) c
      from funext fun z => funext fun c => hred z c]
    simp only [hbc]
    cases v k <;> cases v' k
    · simp only [distAdv, sub_self, abs_zero]; exact abs_nonneg _
    · exact le_rfl
    · rw [distAdv_comm]
    · simp only [distAdv, sub_self, abs_zero]; exact abs_nonneg _

/-- **Hiding of the bitwise scheme by the hybrid lemma** [PS10, proof of Theorem 126.4, "the
security of the full-fledged construction follows as a simple application of the
hybrid lemma (show this!)"] (Claim-127.d): if the one-bit scheme is hiding, the `n`-bit scheme
`owpComStr` satisfies the hiding clause of [PS10, Definition 126.3] — for every `NUPPT` `D`
there is a negligible `ε` with `distAdv(Com⟨v₀, ·⟩, Com⟨v₁, ·⟩, D) ≤ ε(n)` for all `n` and
`v₀, v₁ ∈ {0,1}^n` (the special case of Claim-126.a with `q = n` and single-bit values).

**Proof sketch.** Fix `D`. At each `n`, `exists_bitRed_bound` chooses a worst pair `(v_n, v'_n)`
(`Finset.exists_max_image`), a bit position `k_n` from the coordinatewise hybrid lemma
`exists_pairRed_ge` (after `owpComStr_ofFn`, `distAdv_comp` and the seed reindexing
`acceptProb_comp_equiv (blocks n n)` have turned the two distributions into
`pairTuple (fun i => bitCom (f n) (h n) (v_n i))` and the same for `v'_n`), and — by averaging
over the reduction's seed vectors (`CommitmentLemmas.exists_fixCoins`) — a fixed choice of the
other `n − 1` one-bit commitments, so that the reduction is `z ↦ D(1^n, pre_n ++ z ++ suf_n)`
for two block strings of total length `≤ 3n(n+1)` (`CommitmentLemmas.ofFn_blocks_symm_update`)
and `ε_D(n) ≤ n · distAdv (Com(0)) (Com(1)) (that reduction)` (if `v_n k_n = v'_n k_n` the
advantage is `0`, otherwise up to `distAdv_comm`). The machine
`B := CommitmentLemmas.exists_spliceRed D pre suf` has `D`'s coins, advice
`⟨⟨pre_n, suf_n⟩, D.advice n⟩` and calls `D` once (`NUPPT.exists_comp`,
`NUPPT.exists_withAdvice`); by coin transport (`CommitmentLemmas.acceptProb_distinguisher_of_runAtL`)
its advantage is the reduction's, so `hBit B` gives `ε_D(n) ≤ n ε_B(n)`;
`EnsembleLemmas.negligible_polyExpr_mul` closes with `ε := n · ε_B`. No evaluator of `f` or `h`
is needed: the other commitments are hard-wired, not sampled. -/
theorem BitHiding.owpComStr_hides {P : PermFamily} {h : ∀ n, (Fin n → Bool) → Bool}
    (hBit : BitHiding P h) :
    ∀ D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n (v₀ v₁ : Fin n → Bool),
      distAdv (fun r : Fin (owpComLen.eval n) → Bool =>
          owpComStr P h (pairEncode (List.ofFn v₀) (List.ofFn r)))
        (fun r : Fin (owpComLen.eval n) → Bool =>
          owpComStr P h (pairEncode (List.ofFn v₁) (List.ofFn r)))
        (D.distinguisherL n) ≤ ε n := by
  intro D
  choose pre suf hlen hkey using exists_bitRed_bound P h D
  obtain ⟨B, hBc, hB⟩ := CommitmentLemmas.exists_spliceRed D pre suf
    (.add (.mul (.const 3) (.mul .var (.add .var (.const 1)))) (.const 2))
    (fun n => by simpa using hlen n)
  obtain ⟨ε, hε, hεB⟩ := hBit B
  refine ⟨fun n => n * ε n, by simpa using EnsembleLemmas.negligible_polyExpr_mul .var hε,
    fun n v₀ v₁ => ?_⟩
  refine (hkey n v₀ v₁).trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg n))
  have hε' := hεB n
  unfold distAdv at hε' ⊢
  rwa [CommitmentLemmas.acceptProb_distinguisher_of_runAtL hBc _ (fun y => pre n ++ y ++ suf n)
    (hB n), CommitmentLemmas.acceptProb_distinguisher_of_runAtL hBc _
    (fun y => pre n ++ y ++ suf n) (hB n)] at hε'

open CommitmentLemmas in
/-- **The string commitment is the output of the bitwise loop**: for evaluators `F`, `H` of
`f`, `h` on `⟨1^n, x⟩`, `owpComStr P h w = ComLoop.loopOut F H (ComLoop.init w)` for every
string `w` (`n = |fst w|`).

**Proof sketch.** With `v := fst w`, `r := snd w`, `n := |v|` the loop runs from
`⟨1^n, ⟨v, padL (n²) r⟩⟩` for `|init w| + 1 ≥ n` rounds; round `i < n` emits
`F ⟨1^n, r_i⟩ ++ [v[i] ⊕ H ⟨1^n, r_i⟩]` with `r_i` the `i`-th block of `padFin (n²) r`
(`ComLoop.emit_init_of_lt`), which is `List.ofFn (bitCom (f n) (h n) (padFin n v i) r_i)` by
`hF`, `hH` and `ofFn_snoc_eq`, and rounds `i ≥ n` emit nothing (`ComLoop.emit_init_of_le`,
`CommitmentLemmas.flatMap_range_eq_of_nil`); the concatenation of the `n` block strings is
`List.ofFn ((blocks n (n+1)).symm (owpCom …))` (`EnsembleLemmas.ofFn_blocks_symm`), i.e.
`owpComAt P h n v r`. -/
private theorem owpComStr_eq_loopOut (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool)
    {F H : List Bool → List Bool}
    (hFx : ∀ n (x : Fin n → Bool), F (NUPPT.advInput n (List.ofFn x)) = List.ofFn (P.f n x))
    (hHx : ∀ n (x : Fin n → Bool), H (NUPPT.advInput n (List.ofFn x)) = [h n x]) (w : List Bool) :
    owpComStr P h w = ComLoop.loopOut F H (ComLoop.init w) := by
  rw [ComLoop.init_eq]
  show owpComAt P h (pairFstD w).length (pairFstD w) (pairSndD w) = _
  generalize pairFstD w = v
  generalize pairSndD w = r
  unfold owpComAt ComLoop.loopOut
  set n := v.length with hn
  set T := owpCom P h n (padFin n v) (FunFamily.blocks n n (padFin (n * n) r)) with hT
  set E : ℕ → List Bool :=
    fun i => ComLoop.emit F H (ComLoop.step^[i] (ComLoop.init (pairEncode v r))) with hE
  have hEi : ∀ i (hi : i < n), E i = List.ofFn (T ⟨i, hi⟩) := by
    intro i hi
    simp only [hE]
    rw [ComLoop.emit_init_of_lt F H hi, hFx, hHx, List.headD_cons, ← ofFn_snoc_eq]
    rfl
  have hb : FunFamily.blocks n (n + 1) = EnsembleLemmas.blocks n (n + 1) := rfl
  rw [hb, EnsembleLemmas.ofFn_blocks_symm T E hEi]
  refine (flatMap_range_eq_of_nil E ?_ fun i hi => ComLoop.emit_init_of_le F H hi).symm
  simp only [ComLoop.init, ComLoop.st, length_pairEncode, pairFstD_pairEncode]
  omega

/-- **`Com` of Alg-127.a is polynomial-time** [PS10, Definition 126.3, "a polynomial-time
machine `Com`"; Theorem 126.4]: if `f` and `h` have polynomial-time evaluators on `⟨1^n, x⟩`
(the efficiency clauses of [PS10, Definitions 27.3 and 78.3]), then `owpComStr` is
polynomial-time computable.

**Proof sketch.** On `w`, read `v := pairFstD w`, form `1^n := 1^{|v|}`
(`polyTimeComputable_unary`), pad/cut `pairSndD w` to `n²` bits
(`EnsembleLemmas.polyTimeComputable_padL`) — the initial state `ComLoop.init w` of the bitwise
commitment loop `CommitmentLemmas.ComLoop` — and run the loop `ComLoop.loopOut F H`
(`polyTimeComputable_iterateEmit`, state `⟨1^n, ⟨v.drop i, rest⟩⟩`: each round drops one value
bit and one `n`-bit block and emits `F ⟨1^n, r_i⟩ ++ [v_i ⊕ H ⟨1^n, r_i⟩]`, nothing once the
value bits are exhausted; `StateLoop.headBit_poly`, `StateLoop.xor_poly`,
`PolyTimeComputable.append`, `pairTakePoly/pairDropPoly`). The result equals `owpComStr P h w`
by `owpComStr_eq_loopOut` (`hF`, `hH`, `List.ofFn` of `(blocks n (n+1)).symm` being the
concatenation of the blocks, and `padFin` matching the padding). -/
theorem owpComStr_polyTimeComputable (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool)
    (hF : P.toFunFamily.Easy)
    (hH : ∃ H : List Bool → List Bool, PolyTimeComputable H ∧
      ∀ n (x : Fin n → Bool), H (NUPPT.advInput n (List.ofFn x)) = [h n x]) :
    PolyTimeComputable (owpComStr P h) := by
  obtain ⟨F, hF, hFx⟩ := hF
  obtain ⟨H, hH, hHx⟩ := hH
  convert (CommitmentLemmas.ComLoop.loopOut_poly F H hF hH).comp
    CommitmentLemmas.ComLoop.init_poly using 1
  funext w
  exact owpComStr_eq_loopOut P h hFx hHx w

/-- **Commitment schemes from one-way permutations** [PS10, Theorem 126.4]: if `f` is a
one-way permutation with a hard-core predicate `h`, then `Com(v, (r_i)_i) = (f(r_i) ‖
(v_i ⊕ h(r_i)))_i` (Alg-127.a, `ℓ(n) = n²`) is a commitment scheme: polynomial-time
(`owpComStr_polyTimeComputable`), binding (Claim-127.b, `owpComStr_binding`) and hiding
(Claim-127.c `HardCore.bitHiding` for one bit, Claim-127.d `BitHiding.owpComStr_hides` for `n`
bits).

**Deviation:** the text's hypothesis is "if one-way permutations exist"; its proof uses a
hard-core predicate `h` without stating it (source error 47: [PS10, Theorem 87.3] produces one
for `g(x, r) = (f(x), r)`, not for `f`) and a single permutation family `f` (as in
Theorem 79.4), not the collection of [PS10, Definition 55.1]. Both `OneWayPermutation P` and
`HardCore P.toFunFamily h` are hypotheses here; besides the hard-core property only
`P.toFunFamily.Easy` and the injectivity of `f` are used. -/
theorem owp_commitment (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool)
    (hP : OneWayPermutation P) (hh : HardCore P.toFunFamily h) :
    Commitment (owpComStr P h) owpComLen where
  easy := owpComStr_polyTimeComputable P h hP.easy hh.easy
  binding := owpComStr_binding P h
  hides := hh.bitHiding.owpComStr_hides

/-- **[PS10, Theorem 126.4], existential form**: if there is a one-way permutation with a
hard-core predicate, then commitment schemes exist. -/
theorem exists_commitment_of_owp_hardCore
    (hex : ∃ (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool),
      OneWayPermutation P ∧ HardCore P.toFunFamily h) :
    ∃ (Com : List Bool → List Bool) (ℓ : PolyExpr), Commitment Com ℓ := by
  obtain ⟨P, h, hP, hh⟩ := hex
  exact ⟨owpComStr P h, owpComLen, owp_commitment P h hP hh⟩

/-- **[PS10, Theorem 126.4], the text's form: if one-way permutations exist, then commitment
schemes exist** (gate 03e, note 13): the hard-core predicate of Goldreich–Levin for a padded
one-way permutation (`exists_owp_hardCore`, [PS10, Theorem 87.3]) plugged into
`exists_commitment_of_owp_hardCore`. -/
theorem exists_commitment_of_owp (h : ∃ P : PermFamily, OneWayPermutation P) :
    ∃ (Com : List Bool → List Bool) (ℓ : PolyExpr), Commitment Com ℓ :=
  exists_commitment_of_owp_hardCore (exists_owp_hardCore h)

end TCSlib.Cryptography

## ===== TCSlib/Cryptography/ZeroKnowledge/NP.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring
import TCSlib.Cryptography.ZeroKnowledge.NPLemmas
import TCSlib.Complexity.ClassNP.Reductions

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Zero-knowledge proofs for NP: Levin reductions and Theorem 124.1

Step 2 of [PS10, Theorem 124.1]: "to get a zero-knowledge proof `(P, V)` for any NP language
`L`, both `P` and `V` reduce the instance `x` into an instance `x' = f(x)` of graph
3-colouring, the prover additionally reduces the witness `y` to a witness `y' = w(x, y)` for
`x'`, and the parties execute the 3-colouring protocol on `x'`". The reduction must preserve
witnesses, i.e. be a *Levin reduction* (Def-124.a; the text says "Cook's reduction can be
applied to the witness", which Karp/Cook reductions do not provide — source error 47 of the
plan). Zero-knowledge proofs with efficient prover transfer along Levin reductions
(Claim-124.d), which gives [PS10, Theorem 124.1] in the plan's form (A): for every language
`L` with witness relation `R` and every Levin reduction `(f, w)` of `(L, R)` to `(3COL, R_3COL)`,
the pulled-back 3-colouring protocol is a zero-knowledge proof with efficient prover for `L`,
given a commitment scheme (hence given a one-way permutation with a hard-core predicate,
[PS10, Theorem 126.4]). The "every language in NP" form is the corollary under the hypothesis
that `3COL` is NP-hard *with Levin reductions* (`LevinNPHard`); the string-level Levin
reduction from `3SAT` is not formalized (plan decision on Theorem 124.1, Claim-124.b/c
deferred).

**Deviations:**
* a Levin reduction is taken *length-regular* with `|f x| = p(|x|)` for a `PolyExpr p ≥ id`
  (assumed: padding a Levin reduction to `3COL` with isolated vertices should give this form
  with `p = q²` for a polynomial `q`, the lengths of `encGraph` being perfect squares, but the
  padding is not formalized; gate 03e, note 14), which makes the coin and round polynomials
  of the pulled-back protocol `subst p` of the original ones and the error bounds
  `ε(p(|x|))`, negligible in `|x|` (`Negligible.comp_of_le`);
* the text's "execute protocol `(P, V)` on `x'`" is read as `(P', V')`; the hypothesis of a
  hard-core predicate for the one-way permutation is made explicit (as in Theorem 126.4).

**Proof infrastructure (run 4):** the transfer proofs use the sibling file
`TCSlib.Cryptography.ZeroKnowledge.NPLemmas` (namespace `LevinTransfer`): the execution
congruence `exec_congr`, the uniform coin projections `coinTrunc`/`UnifProj` with
`distAdv_eq_of_unifProj` (the padding of the random tapes is uniform and independent), the
verifier `liftVerifier V'` and the view re-encoder `postView` of the zero-knowledge transfer,
the machines `exists_liftSimulator`/`exists_liftDistinguisher`, and the strict monotonicity of
a length polynomial `p ≥ id` (`polyExpr_strictMono_of_le`, which gives the left inverse of
`p.eval` along which the distinguisher is re-parametrized).

**Bounded prover messages (ruling G3-3 of gate 03):** the bound on the honest prover's
messages transfers along a Levin reduction with bound `B.subst p`
(`Protocol.ProverBounded.pullback`).

**Scope of Theorem 124.1 (DQ5; gate 03e, minor 3).** The text's Theorem 124.1 asserts one
zero-knowledge proof with negligible soundness error. Here the zero-knowledge protocol is one
iteration of the 3-colouring protocol, with soundness error `1 - 1/p(|x|) + 2^{-p(|x|)}`, and
the interactive proof with negligible error is its `n|E|`-fold repetition; that the repetition
is also zero-knowledge, with negligible soundness error, is sequential repetition
[PS10, §7.2.1], which ch. 7 supplies (ruling G3-7(d)), and is not stated here. In the
existential forms the conjunct `∃ π, EfficientProverProof π L R` says nothing about the
zero-knowledge protocol (`npProtocol` already witnesses it, `npProtocol_interactiveProof`);
the tied forms `exists_commitment_zk_proof_of_owp_levinReduction`,
`zk_proof_of_witnessRelation` and `zk_proof_of_witnessRelation_of_owp` state both protocols for
one commitment scheme and one Levin reduction, as `zk_proof_of_levinReduction` does.

**Run-3 repairs (audit P11-1, P11-2):** the transfer lemmas and both forms of Theorem 124.1
take the hypothesis `hLR : ∀ x ∈ L, ∃ y, R x y` (`L ⊆ witnessLanguage R`): no field of
`LevinReduction` relates `L` to `R` (with `R = ∅` the `witness` field is vacuous), and without
it the `complete` clause of the pulled-back proof is false. The "every language in NP" forms
keep the explicit soundness error `1 - 1/p(|x|) + (1/2)^{p(|x|)}` of the Levin reduction's
length polynomial `p ≥ id` (the run-2 `∃ s, EfficientProverProofErr π L R s` was vacuous with
`s = 1`; `one_sub_inv_add_half_pow_lt_one` shows the error is below `1`).

## Main definitions

* `TCSlib.Cryptography.LevinReduction` — Levin (witness-preserving) reductions (Def-124.a).
* `TCSlib.Cryptography.Strategy.pullback`, `TCSlib.Cryptography.Protocol.pullback` — the
  protocol for `L` obtained by reducing to `L'` and running a protocol for `L'`.
* `TCSlib.Cryptography.LevinNPHard` — NP-hardness with Levin reductions (the hypothesis of
  the "every language in NP" form).

## Main results

* `TCSlib.Cryptography.LevinReduction.refl`, `TCSlib.Cryptography.LevinReduction.trans`,
  `TCSlib.Cryptography.LevinReduction.polyTimeReducible` — sanity: Levin reductions compose
  and are Karp reductions (proved).
* `TCSlib.Cryptography.LevinReduction.efficientProverProof`,
  `TCSlib.Cryptography.LevinReduction.efficientProverProofErr`,
  `TCSlib.Cryptography.LevinReduction.zk` — interactive proofs with efficient prover and
  zero-knowledge transfer along Levin reductions (Claim-124.d);
  `TCSlib.Cryptography.Protocol.ProverBounded.pullback` — so does the bound on the prover's
  messages.
* `TCSlib.Cryptography.zk_proof_of_levinReduction` — **[PS10, Theorem 124.1], form (A)**:
  a commitment scheme and a Levin reduction to `3COL` give a zero-knowledge protocol for `L`
  with soundness error `1 - 1/p(|x|) + 2^{-p(|x|)}` whose `n|E|`-fold repetition is an
  interactive proof; `TCSlib.Cryptography.zk_proof_of_owp_levinReduction`,
  `TCSlib.Cryptography.exists_commitment_zk_proof_of_owp_levinReduction` — the same from a
  one-way permutation with a hard-core predicate, untied and tied (Thm-124.1).
* `TCSlib.Cryptography.zk_proof_of_witnessRelation`,
  `TCSlib.Cryptography.zk_proof_of_witnessRelation_of_owp` — the "every language in NP" form
  for every witness relation, under `LevinNPHard L3COL R3COL` (the second from a one-way
  permutation, the text's hypothesis); `TCSlib.Cryptography.zk_proof_of_mem_NP`,
  `TCSlib.Cryptography.zk_proof_of_mem_NP_of_owp` — the corollaries for `L ∈ NP` with the
  witness relation of `exists_witnessRelation_of_mem_NP`, with the explicit soundness error of
  the Levin reduction's length polynomial
  (`TCSlib.Cryptography.one_sub_inv_add_half_pow_lt_one`: the error is below `1`).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.7: Theorem 124.1; Appendix B, Definition 191.11.)
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge
  University Press, 2009. (Definition 2.7, Karp reductions; §2.3, Levin reductions.)
-/

namespace TCSlib.Cryptography

open Complexity Turing LevinTransfer

/-! ### Levin reductions (Def-124.a) -/

/-- A **Levin reduction** `(f, w)` from `(L, R)` to `(L', R')` [PS10, §4.7, Theorem 124.1,
step 2, "Cook's reduction can be applied to the witness"] (Def-124.a): `f` is a
polynomial-time Karp reduction (`x ∈ L ↔ f x ∈ L'`), `w` is polynomial-time on the pair
`⟨x, y⟩` and maps witnesses to witnesses (`R x y → R' (f x) (w x y)`), and `f` is
length-regular: `|f x| = p(|x|)` for the polynomial `p ≥ id`.

**Deviation:** the text never defines Levin reductions; length-regularity with `p ≥ id` is
assumed (padding with isolated vertices should achieve it for `3COL`, with `p = q²`; not
formalized) so that the pulled-back protocol's polynomials are `subst p` of the original ones
and its error bounds `ε(p(|x|))` are negligible in `|x|`. -/
structure LevinReduction (L L' : Language Bool) (R R' : List Bool → List Bool → Prop)
    (f : List Bool → List Bool) (w : List Bool → List Bool → List Bool) (p : PolyExpr) : Prop where
  /-- The instance map is polynomial-time. -/
  f_poly : PolyTimeComputable f
  /-- The witness map is polynomial-time on the pair `⟨x, y⟩`. -/
  w_poly : PolyTimeComputable fun z => w (pairFstD z) (pairSndD z)
  /-- `f` is a Karp reduction. -/
  mem_iff : ∀ x, x ∈ L ↔ f x ∈ L'
  /-- `w` maps witnesses of `x` to witnesses of `f x`. -/
  witness : ∀ x y, R x y → R' (f x) (w x y)
  /-- `f` is length-regular with length polynomial `p`. -/
  length_eq : ∀ x, (f x).length = p.eval x.length
  /-- The length polynomial dominates the identity. -/
  le_eval : ∀ N, N ≤ p.eval N

/-- A Levin reduction is a Karp reduction [AB09, Definition 2.7]. -/
theorem LevinReduction.polyTimeReducible {L L' : Language Bool} {R R' : List Bool → List Bool → Prop}
    {f : List Bool → List Bool} {w : List Bool → List Bool → List Bool} {p : PolyExpr}
    (h : LevinReduction L L' R R' f w p) : PolyTimeReducible L L' :=
  ⟨f, h.f_poly, h.mem_iff⟩

/-- Sanity: the identity is a Levin reduction of `(L, R)` to itself. -/
theorem LevinReduction.refl (L : Language Bool) (R : List Bool → List Bool → Prop) :
    LevinReduction L L R R id (fun _ y => y) .var where
  f_poly := polyTimeComputable_id
  w_poly := polyTimeComputable_pairSndD
  mem_iff _ := Iff.rfl
  witness _ _ h := h
  length_eq _ := rfl
  le_eval _ := le_rfl

/-- Sanity: Levin reductions compose, with length polynomial `p'.subst p`.

**Proof sketch.** `f' ∘ f` by `PolyTimeComputable.comp`; the composed witness map
`⟨x, y⟩ ↦ w' (f x) (w x y)` is `w'` on the pair `⟨f x, w x y⟩` built by
`PolyTimeComputable.pairEncode` (`pairFstD_pairEncode`, `pairSndD_pairEncode`); membership
and witnesses by transitivity; lengths by `PolyExpr.eval_subst`. -/
theorem LevinReduction.trans {L L' L'' : Language Bool}
    {R R' R'' : List Bool → List Bool → Prop} {f f' : List Bool → List Bool}
    {w w' : List Bool → List Bool → List Bool} {p p' : PolyExpr}
    (h : LevinReduction L L' R R' f w p) (h' : LevinReduction L' L'' R' R'' f' w' p') :
    LevinReduction L L'' R R'' (f' ∘ f) (fun x y => w' (f x) (w x y)) (p'.subst p) where
  f_poly := h'.f_poly.comp h.f_poly
  w_poly := by
    have hfun : (fun z => w' (f (pairFstD z)) (w (pairFstD z) (pairSndD z))) =
        fun z => w' (pairFstD (pairEncode (f (pairFstD z)) (w (pairFstD z) (pairSndD z))))
          (pairSndD (pairEncode (f (pairFstD z)) (w (pairFstD z) (pairSndD z)))) := by
      funext z
      rw [pairFstD_pairEncode, pairSndD_pairEncode]
    rw [hfun]
    exact h'.w_poly.comp ((h.f_poly.comp polyTimeComputable_pairFstD).pairEncode h.w_poly)
  mem_iff x := (h.mem_iff x).trans (h'.mem_iff (f x))
  witness x y hxy := h'.witness _ _ (h.witness x y hxy)
  length_eq x := by
    rw [Function.comp_apply, h'.length_eq, h.length_eq, PolyExpr.eval_subst]
  le_eval N := by
    rw [PolyExpr.eval_subst]
    exact (h.le_eval N).trans (h'.le_eval _)

/-! ### Pulling a protocol back along a reduction -/

/-- The strategy that runs `S` on the reduced instance `f x` with the transformed auxiliary
input `g x z` [PS10, §4.7, Theorem 124.1, step 2]: `next x z r hist := S.next (f x) (g x z) r hist`,
coins `S.coins.subst p` (so that the tape at `|x|` has exactly `S.coinLen |f x|` bits when
`|f x| = p(|x|)`). -/
def Strategy.pullback (S : Strategy) (f : List Bool → List Bool)
    (g : List Bool → List Bool → List Bool) (p : PolyExpr) : Strategy where
  next x z r hist := S.next (f x) (g x z) r hist
  coins := S.coins.subst p

/-- The pulled-back strategy's coin length at `|x|` is `S`'s at `|f x|` under length
regularity. -/
theorem Strategy.coinLen_pullback (S : Strategy) (f : List Bool → List Bool)
    (g : List Bool → List Bool → List Bool) {p : PolyExpr} {x : List Bool}
    (hx : (f x).length = p.eval x.length) :
    (S.pullback f g p).coinLen x.length = S.coinLen (f x).length := by
  simp [Strategy.pullback, Strategy.coinLen, PolyExpr.eval_subst, hx]

/-- The protocol for `L` obtained from a protocol `π` for `L'` and a reduction `(f, w)`
[PS10, §4.7, Theorem 124.1, step 2]: `P(x, y) := P'(f x, w x y)`, `V(x, z) := V'(f x, z)`,
rounds `π.rounds.subst p`, same first mover (Claim-124.d, construction).

**Deviation:** "execute protocol `(P, V)` on `x'`" read as `(P', V')`. -/
def Protocol.pullback (π : Protocol) (f : List Bool → List Bool)
    (w : List Bool → List Bool → List Bool) (p : PolyExpr) : Protocol where
  P := π.P.pullback f w p
  V := π.V.pullback f (fun _ z => z) p
  rounds := π.rounds.subst p
  verifierFirst := π.verifierFirst

/-- Unfolding: the verifier's output in the pulled-back protocol against a prover `P'` is
`π.V.next` on the reduced instance after `π.rounds.eval (p |x|)` moves of `exec` with the
reduced inputs. -/
theorem Protocol.pullback_outV (π : Protocol) (f : List Bool → List Bool)
    (w : List Bool → List Bool → List Bool) (p : PolyExpr) (P' : Strategy) (x y z : List Bool)
    (r : (π.pullback f w p).ExecCoins P' x) :
    (π.pullback f w p).outV P' x y z r =
      π.V.next (f x) z (List.ofFn r.2)
        (exec P' (π.V.pullback f (fun _ z => z) p) π.verifierFirst x y z (List.ofFn r.1)
          (List.ofFn r.2) (π.rounds.eval (p.eval x.length))).2 := by
  simp [Protocol.outV, Protocol.transcriptWith, Protocol.pullback, Strategy.pullback,
    PolyExpr.eval_subst]

/-- A pulled-back strategy is efficient when the original is and `f`, `g` are
polynomial-time (on `⟨x, z⟩` for `g`): compose the machine of `S` with the FP function
`⟨⟨x, z⟩, msgs⟩ ↦ ⟨⟨f x, g x z⟩, msgs⟩` and re-parametrize `1^{|x|}` to `1^{p |x|}`
(`NUPPT.exists_reparam p`, `NUPPT.exists_comp`, `PolyExpr.eval_subst`, `hx`).

**Proof sketch.** From `hS` take the uniform `A` with `S.next x' z' r hist =
A.runAtL |x'| ⟨⟨x', z'⟩, encodeMsgs hist⟩ r`. `NUPPT.exists_comp A hpre polyTimeComputable_id`
with `pre := ⟨⟨f ∘ pairFstD ∘ pairFstD, g on the pair⟩, pairSndD⟩` (pairing calculus) gives
`B` with `B.runAtL m y r = A.runAtL m (pre y) r`; `NUPPT.exists_reparam B p` gives `C` with
`C.runAtL n y r = B.runAtL (p n) y r`, uniform, coins `A.coins.subst p = (S.pullback …).coins`;
on `n = |x|`, `p n = |f x|` (`hx`), so `C` computes the pulled-back next-message function
(`Strategy.ofNUPPT_next`, `pairFstD_pairEncode`, `pairSndD_pairEncode`). -/
theorem Strategy.pullback_efficient {S : Strategy} (hS : S.Efficient) {f : List Bool → List Bool}
    (hf : PolyTimeComputable f) {g : List Bool → List Bool → List Bool}
    (hg : PolyTimeComputable fun z => g (pairFstD z) (pairSndD z)) {p : PolyExpr}
    (hx : ∀ x, (f x).length = p.eval x.length) : (S.pullback f g p).Efficient := by
  obtain ⟨A, hA, hc, hnext⟩ := hS
  have hpre : PolyTimeComputable fun y =>
      pairEncode (pairEncode (f (pairFstD (pairFstD y)))
        (g (pairFstD (pairFstD y)) (pairSndD (pairFstD y)))) (pairSndD y) :=
    ((hf.comp (polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD)).pairEncode
      (hg.comp polyTimeComputable_pairFstD)).pairEncode polyTimeComputable_pairSndD
  obtain ⟨B, hBc, -, hBadv, hB⟩ := A.exists_comp hpre polyTimeComputable_id
  obtain ⟨C, hCc, hCu, hC⟩ := B.exists_reparam p
  refine ⟨C, hCu fun n => by rw [hBadv]; exact hA n, ?_, fun x z r hist => ?_⟩
  · show S.coins.subst p = C.coins
    rw [hCc, hBc, hc]
  · rw [Strategy.ofNUPPT_next, hC, hB]
    show S.next (f x) (g x z) r hist = _
    rw [hnext, Strategy.ofNUPPT_next, ← hx x]
    simp only [id, pairFstD_pairEncode, pairSndD_pairEncode]

/-- **Bounded prover messages transfer along a Levin reduction** with bound `B.subst p`
(ruling G3-3 of gate 03): the pulled-back prover runs `π.P` on `(f x, w x y)`, `R x y` gives
`R' (f x) (w x y)` (`LevinReduction.witness`), and `|f x| = p(|x|)`
(`LevinReduction.length_eq`, `PolyExpr.eval_subst`). -/
theorem Protocol.ProverBounded.pullback {L L' : Language Bool}
    {R R' : List Bool → List Bool → Prop} {f : List Bool → List Bool}
    {w : List Bool → List Bool → List Bool} {p : PolyExpr} (h : LevinReduction L L' R R' f w p)
    {π : Protocol} {B : PolyExpr} (hB : π.ProverBounded R' B) :
    (π.pullback f w p).ProverBounded R (B.subst p) := by
  intro x y r hist hxy
  rw [PolyExpr.eval_subst, ← h.length_eq x]
  exact hB (f x) (w x y) r hist (h.witness x y hxy)

/-! ### Negligibility along polynomial reparametrization -/

/-- A negligible function composed with a map `φ ≥ id` is negligible: for `N ≥ max n₀ 1`,
`φ N ≥ N ≥ n₀` so `|μ (φ N)| < 1 / (φ N)^c ≤ 1 / N^c` (the bookkeeping for the error bounds
`ε(|f x|) = ε(p(|x|))` of the pulled-back protocol, Claim-124.d). -/
theorem Negligible.comp_of_le {μ : ℕ → ℝ} (hμ : Negligible μ) (φ : ℕ → ℕ) (hφ : ∀ N, N ≤ φ N) :
    Negligible fun N => μ (φ N) := by
  intro c
  obtain ⟨n₀, h₀⟩ := hμ c
  refine ⟨max n₀ 1, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hφN : n₀ ≤ φ N := le_trans (le_trans (le_max_left _ _) hN) (hφ N)
  refine lt_of_lt_of_le (h₀ (φ N) hφN) ?_
  have hNpos : (0 : ℝ) < (N : ℝ) ^ c := pow_pos (by exact_mod_cast hN1) c
  exact one_div_le_one_div_of_le hNpos (pow_le_pow_left₀ (by positivity) (by exact_mod_cast hφ N) c)

/-! ### Executions of the pulled-back protocol -/

/-- The execution of two pulled-back strategies on `x` is the execution of the original
strategies on `f x` with the transformed auxiliary inputs and the same random tapes
(`LevinTransfer.exec_congr`; the pulled-back next-message functions are those of the
originals on the reduced inputs by definition). -/
private theorem exec_pullback (P V : Strategy) (f : List Bool → List Bool)
    (g g' : List Bool → List Bool → List Bool) (p : PolyExpr) (vFirst : Bool)
    (x zP zV rP rV : List Bool) (k : ℕ) :
    exec (P.pullback f g p) (V.pullback f g' p) vFirst x zP zV rP rV k =
      exec P V vFirst (f x) (g x zP) (g' x zV) rP rV k := by
  refine exec_congr ?_ ?_ vFirst k <;> intro _ <;> rfl

/-- The execution of an arbitrary prover `P'` against a pulled-back verifier on `x` is the
execution of the prover `⟨fun _ _ r hist => P'.next x [] r hist, const (P'.coinLen |x|)⟩`
(which hard-wires `x` and has `P'`'s random tape) against the original verifier on `f x`
(`LevinTransfer.exec_congr`). -/
private theorem exec_pullback_cheat (P' V : Strategy) (f : List Bool → List Bool)
    (g' : List Bool → List Bool → List Bool) (p : PolyExpr) (vFirst : Bool)
    (x zV rP rV : List Bool) (k : ℕ) :
    exec P' (V.pullback f g' p) vFirst x [] zV rP rV k =
      exec ⟨fun _ _ r hist => P'.next x [] r hist, .const (P'.coinLen x.length)⟩ V vFirst (f x)
        [] (g' x zV) rP rV k := by
  refine exec_congr ?_ ?_ vFirst k <;> intro _ <;> rfl

/-- The coin length of a pulled-back strategy at `|x|` is at least (in fact equal to) the
original's at `|f x|` under length regularity — the form in which `LevinTransfer.coinTrunc`
casts the honest coins of the pulled-back protocol to those of `π` on `f x`. -/
private theorem coinLen_le_coinLen_pullback (S : Strategy) (f : List Bool → List Bool)
    (g : List Bool → List Bool → List Bool) {p : PolyExpr} {x : List Bool}
    (hx : (f x).length = p.eval x.length) :
    S.coinLen (f x).length ≤ (S.pullback f g p).coinLen x.length :=
  (Strategy.coinLen_pullback S f g hx).ge

/-- **The honest execution of the pulled-back protocol is the honest execution of `π` on the
reduced instance:** the verifier's output in `(π.pullback f w p)` on `(x, y, z)` with coins
`r` is the output of `π` on `(f x, w x y, z)` with the coins cast along
`Strategy.coinLen_pullback` (`Protocol.pullback_outV`, `exec_pullback`,
`LevinTransfer.ofFn_coinTrunc_of_eq`, the move count `π.rounds (p |x|) = π.rounds |f x|`). -/
private theorem outV_pullback_honest (π : Protocol) (f : List Bool → List Bool)
    (w : List Bool → List Bool → List Bool) {p : PolyExpr} {x : List Bool}
    (hx : (f x).length = p.eval x.length) (y z : List Bool)
    (r : (π.pullback f w p).ExecCoins (π.pullback f w p).P x) :
    (π.pullback f w p).outV (π.pullback f w p).P x y z r =
      π.outV π.P (f x) (w x y) z
        (Prod.map (coinTrunc (coinLen_le_coinLen_pullback π.P f w hx))
          (coinTrunc (coinLen_le_coinLen_pullback π.V f (fun _ z => z) hx)) r) := by
  rw [Protocol.pullback_outV]
  simp only [Protocol.outV, Protocol.transcriptWith, Protocol.pullback, Prod.map]
  rw [ofFn_coinTrunc_of_eq _ (Strategy.coinLen_pullback π.P f w hx).symm,
    ofFn_coinTrunc_of_eq _ (Strategy.coinLen_pullback π.V f (fun _ z => z) hx).symm,
    exec_pullback, ← hx]

/-- **A cheating prover for the pulled-back protocol is a cheating prover for `π`:** the
verifier's output in `(π.pullback f w p)` against `P'` on `x` with coins `r` is the output
of `π` on `f x` against the prover `P* := ⟨fun _ _ r hist => P'.next x [] r hist,
const (P'.coinLen |x|)⟩` (which hard-wires `x` and has `P'`'s random tape) with the verifier
coins cast along `Strategy.coinLen_pullback` (`exec_congr`). -/
private theorem outV_pullback_cheat (π : Protocol) (f : List Bool → List Bool)
    (w : List Bool → List Bool → List Bool) {p : PolyExpr} {x : List Bool}
    (hx : (f x).length = p.eval x.length) (P' : Strategy) (z : List Bool)
    (r : (π.pullback f w p).ExecCoins P' x) :
    (π.pullback f w p).outV P' x [] z r =
      π.outV ⟨fun _ _ r hist => P'.next x [] r hist, .const (P'.coinLen x.length)⟩ (f x) [] z
        (Prod.map (coinTrunc le_rfl)
          (coinTrunc (coinLen_le_coinLen_pullback π.V f (fun _ z => z) hx)) r) := by
  rw [Protocol.pullback_outV]
  simp only [Protocol.outV, Protocol.transcriptWith, Prod.map]
  rw [ofFn_coinTrunc_of_eq _ rfl,
    ofFn_coinTrunc_of_eq _ (Strategy.coinLen_pullback π.V f (fun _ z => z) hx).symm,
    exec_pullback_cheat, ← hx]

/-! ### Claim-124.d: zero-knowledge proofs transfer along Levin reductions -/

/-- **Interactive proofs with efficient prover transfer along Levin reductions, soundness
error `s ∘ p`** [PS10, §4.7, "it is easy to verify that the above protocol is a
zero-knowledge proof"] (Claim-124.d, proof half): if `π` is an interactive proof for `L'` with
efficient prover w.r.t. `R'` and soundness error `s`, `(f, w)` is a Levin reduction of
`(L, R)` to `(L', R')`, and every `x ∈ L` has an `R`-witness (`hLR`, i.e.
`L ⊆ witnessLanguage R`), then `π.pullback f w p` is an interactive proof for `L` with
efficient prover w.r.t. `R` and soundness error `N ↦ s (p N)`.

**Repair (run-3 audit P11-1):** the hypothesis `hLR : ∀ x ∈ L, ∃ y, R x y` was added. No
field of `LevinReduction` relates `L` to `R` — with `R = ∅` the `witness` field is vacuous, so
a witness map that outputs non-witnesses is a valid Levin reduction — while the `complete`
clause of the conclusion needs the pulled-back honest prover, which runs `π.P` on `w x y`, to
hold a witness `y` with `R x y`; without `hLR` the statement is refutable (`npProtocol` for
the relation `|x| = |y|` pulled back along `id` and `w x y := ⟨x, x⟩`). Equivalent
alternative: state the lemma for `L := witnessLanguage R`.

**Proof sketch.** Efficiency of both parties: `Strategy.pullback_efficient` with `h.f_poly`,
`h.w_poly` (for `V` the map `g := fun _ z => z` is `polyTimeComputable_pairSndD`), `h.length_eq`.
Completeness for every witness: for `R x y`, `R' (f x) (w x y)` (`h.witness`), and the
execution of the pulled-back protocol on `(x, y, z)` with coins `r` is the execution of `π` on
`(f x, w x y, z)` with the coins cast along `Strategy.coinLen_pullback` (`outV_pullback_honest`:
`Protocol.pullback_outV` and `LevinTransfer.exec_congr` — the pulled-back next-message
functions are those of `π` on `(f x, w x y)` and `(f x, z)` by definition — with the move
count `π.rounds.eval (p |x|) = π.rounds.eval |f x|` by `h.length_eq`); the cast is a uniform
projection (`LevinTransfer.unifProj_coinTrunc`, `UnifProj.uprob_comp`), so
`hπ.completeWitness` gives probability one. Bounded prover messages:
`Protocol.ProverBounded.pullback` with the bound `B.subst p` of `hπ.boundedP`. Completeness:
for `x ∈ L` take `y` with `R x y` (`hLR`); the honest messages have at most `B(p(|x|))` bits
and the verifier accepts with probability one (`Protocol.ProverBounded.exists_complete`).
Soundness: for `x ∉ L`, `f x ∉ L'` (`h.mem_iff`); a prover `P'` for the pulled-back protocol
on `x` is the prover `P* := ⟨fun _ _ r hist => P'.next x [] r hist, .const (P'.coinLen |x|)⟩`
for `π` on `f x` with the same coins (`outV_pullback_cheat`,
`P*.coinLen |f x| = P'.coinLen |x|`), and
`hπ.sound (f x) _ P* z` gives `1 - s |f x| ≤ Pr[out = [false]]`, i.e. `1 - s (p |x|)` by
`h.length_eq`. -/
theorem LevinReduction.efficientProverProofErr {L L' : Language Bool}
    {R R' : List Bool → List Bool → Prop} {f : List Bool → List Bool}
    {w : List Bool → List Bool → List Bool} {p : PolyExpr} (h : LevinReduction L L' R R' f w p)
    (hLR : ∀ x ∈ L, ∃ y, R x y) {π : Protocol} {s : ℕ → ℝ}
    (hπ : EfficientProverProofErr π L' R' s) :
    EfficientProverProofErr (π.pullback f w p) L R (fun N => s (p.eval N)) := by
  have hcompl : ∀ x y, R x y → ∀ z : List Bool,
      uprob (fun r : (π.pullback f w p).ExecCoins (π.pullback f w p).P x =>
        (π.pullback f w p).outV (π.pullback f w p).P x y z r = [true]) = 1 := by
    intro x y hxy z
    have hx := h.length_eq x
    have key := hπ.completeWitness (f x) (w x y) (h.witness x y hxy) z
    rw [← ((unifProj_coinTrunc (coinLen_le_coinLen_pullback π.P f w hx)).prod
      (unifProj_coinTrunc (coinLen_le_coinLen_pullback π.V f (fun _ z => z) hx))).uprob_comp
      (fun r' => π.outV π.P (f x) (w x y) z r' = [true])] at key
    rw [← key]
    congr 1
    funext r
    rw [outV_pullback_honest π f w hx]
  obtain ⟨B, hB⟩ := hπ.boundedP
  refine ⟨⟨Strategy.pullback_efficient hπ.efficientV h.f_poly polyTimeComputable_pairSndD
    h.length_eq, (hB.pullback h).exists_complete hLR hcompl, fun x hx P' z => ?_⟩,
    Strategy.pullback_efficient hπ.efficientP h.f_poly h.w_poly h.length_eq,
    ⟨B.subst p, hB.pullback h⟩, hcompl⟩
  · have hlen := h.length_eq x
    have hfx : f x ∉ L' := fun hfx => hx ((h.mem_iff x).2 hfx)
    have hU : UnifProj (Prod.map (coinTrunc le_rfl)
        (coinTrunc (coinLen_le_coinLen_pullback π.V f (fun _ z => z) hlen)) :
          (π.pullback f w p).ExecCoins P' x →
            π.ExecCoins ⟨fun _ _ r hist => P'.next x [] r hist, .const (P'.coinLen x.length)⟩
              (f x)) :=
      (unifProj_coinTrunc _).prod (unifProj_coinTrunc _)
    have key := hπ.sound (f x) hfx
      ⟨fun _ _ r hist => P'.next x [] r hist, .const (P'.coinLen x.length)⟩ z
    rw [← hU.uprob_comp] at key
    refine le_of_eq_of_le (by rw [hlen]) (le_of_le_of_eq key ?_)
    congr 1
    funext r
    rw [outV_pullback_cheat π f w hlen]

/-- **Interactive proofs with efficient prover transfer along Levin reductions** (Claim-124.d,
proof half, negligible error): as `LevinReduction.efficientProverProofErr`, the soundness
error `ε (p N)` being negligible by `Negligible.comp_of_le` with `h.le_eval`
(`EfficientProverProof.exists_err`, `EfficientProverProofErr.efficientProverProof`).

**Repair (run-3 audit P11-1):** hypothesis `hLR : ∀ x ∈ L, ∃ y, R x y` added (see
`LevinReduction.efficientProverProofErr`). -/
theorem LevinReduction.efficientProverProof {L L' : Language Bool}
    {R R' : List Bool → List Bool → Prop} {f : List Bool → List Bool}
    {w : List Bool → List Bool → List Bool} {p : PolyExpr} (h : LevinReduction L L' R R' f w p)
    (hLR : ∀ x ∈ L, ∃ y, R x y) {π : Protocol} (hπ : EfficientProverProof π L' R') :
    EfficientProverProof (π.pullback f w p) L R := by
  obtain ⟨ε, hε, herr⟩ := hπ.exists_err
  exact (h.efficientProverProofErr hLR herr).efficientProverProof (hε.comp_of_le _ h.le_eval)

/-- **Zero-knowledge transfers along Levin reductions** [PS10, §4.7, "it is easy to verify
that the above protocol is a zero-knowledge proof"] (Claim-124.d, zero-knowledge half): if `π`
is zero-knowledge for `R'` and `(f, w)` is a Levin reduction of `(L, R)` to `(L', R')`, then
`π.pullback f w p` is zero-knowledge for `R`.

**Proof sketch.** Let `V*` be an efficient verifier for the pulled-back protocol. The
verifier `V*' := LevinTransfer.liftVerifier V*` for `π`, `V*'.next x' z' r hist := V*.next
(pairFstD z') (pairSndD z') (r.take (V*.coinLen |pairFstD z'|)) hist` with coins `V*.coins`
(at `|x'| = p |x| ≥ |x|` the tape is long enough, `PolyExpr.eval_mono`, `h.le_eval`), recovers
`x` from its auxiliary input `z' = ⟨x, z⟩` and ignores `x'`; it is efficient
(`LevinTransfer.liftVerifier_efficient`, from `V*`'s machine with
`polyTimeComputable_pairTakePoly`). `hzk V*'` gives a uniform simulator `S'`; the simulator for
`V*` is `S` with `S.simulate x z r = post (S'.simulate (f x) ⟨x, z⟩ r)`, where
`post := LevinTransfer.postView V*.coins` re-encodes the view `⟨⟨x', ⟨x, z⟩⟩, ⟨r', msgs⟩⟩` as
`⟨⟨x, z⟩, ⟨r'.take (V*.coinLen |x|), msgs⟩⟩` (`LevinTransfer.exists_liftSimulator`:
`NUPPT.exists_comp` with `pre y := ⟨f (fst y), y⟩`, then `NUPPT.exists_reparam p`; uniform,
coins `S'.coins.subst p`). For `Lz`, `D`: the distinguisher `D'` for `π` at parameter
`|x'| = p |x|` is `D` re-parametrized along the left inverse `φ N' := min (invFun p.eval N') N'`
of `p.eval` — well defined since `p ≥ id` is strictly increasing
(`LevinTransfer.polyExpr_strictMono_of_le`) — composed with `post`
(`LevinTransfer.exists_liftDistinguisher`: `NUPPT.exists_reparam_advice`, `NUPPT.exists_comp`);
auxiliary bound `Lz' := add (add (mul (const 2) var) (const 2)) Lz` (`|⟨x, z⟩| ≤ 2|x| + 2
+ Lz |x| ≤ Lz' |x'|`). `hzk V*' Lz' D'` gives `ε'`; on `R x y` (so `R' (f x) (w x y)`), `post` of
the view of `V*'` in `π` on `(f x, w x y, ⟨x, z⟩)` with coins `(r₁, r₂')` is the view of `V*` in
the pulled-back protocol with coins `(r₁, r₂'.take (V*.coinLen |x|))`
(`LevinTransfer.exec_congr`, `liftVerifier_next`, `postView_encode`), and `D'`'s verdict is
`D`'s on the re-encoded sample with truncated coins (`LevinTransfer.distinguisherL_lift`);
the truncations are uniform projections, so the two advantages coincide
(`LevinTransfer.distAdv_eq_of_unifProj`) and `distAdv ≤ ε' |f x| = ε' (p |x|)`;
`ε := ε' ∘ p.eval` is negligible by `Negligible.comp_of_le`. -/
theorem LevinReduction.zk {L L' : Language Bool} {R R' : List Bool → List Bool → Prop}
    {f : List Bool → List Bool} {w : List Bool → List Bool → List Bool} {p : PolyExpr}
    (h : LevinReduction L L' R R' f w p) {π : Protocol} (hzk : ZK π R') :
    ZK (π.pullback f w p) R := by
  intro V' hV'
  obtain ⟨S', hS'u, hS'⟩ := hzk (liftVerifier V') (liftVerifier_efficient hV')
  obtain ⟨S, hSc, hSu, hS⟩ := exists_liftSimulator S' h.f_poly V'.coins p
  refine ⟨S, hSu hS'u, fun Lz D => ?_⟩
  -- the left inverse `φ` of the (strictly increasing) length polynomial
  have hmono := polyExpr_strictMono_of_le h.le_eval
  set φ : ℕ → ℕ := fun n => min (Function.invFun p.eval n) n with hφ_def
  have hφle : ∀ n, φ n ≤ n := fun n => min_le_right _ _
  have hφp : ∀ N, φ (p.eval N) = N := fun N => by
    simp only [hφ_def, Function.leftInverse_invFun hmono.injective N]
    exact min_eq_left (h.le_eval N)
  obtain ⟨D', hD'c, hD'⟩ := exists_liftDistinguisher D φ hφle V'.coins
  set Lz' : PolyExpr := .add (.add (.mul (.const 2) .var) (.const 2)) Lz with hLz'
  obtain ⟨ε', hε', hadv⟩ := hS' Lz' D'
  refine ⟨fun N => ε' (p.eval N), hε'.comp_of_le _ h.le_eval, fun x y z hxy hz => ?_⟩
  have hlen := h.length_eq x
  have hz' : (pairEncode x z).length ≤ Lz'.eval (f x).length := by
    rw [length_pairEncode, hlen, hLz']
    simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
    have h₁ := h.le_eval x.length
    have h₂ := Lz.eval_mono (h.le_eval x.length)
    omega
  have key := hadv (f x) (w x y) (pairEncode x z) (h.witness x y hxy) hz'
  -- coin-space bookkeeping
  have hxle : x.length ≤ (f x).length := by rw [hlen]; exact h.le_eval _
  have hφx : φ (f x).length = x.length := by rw [hlen]; exact hφp _
  have hDle : D.coinLen x.length ≤ D'.coinLen (f x).length := by
    simp only [NUPPT.coinLen, hD'c]
    exact D.coins.eval_mono hxle
  have hVle : V'.coinLen x.length ≤ (liftVerifier V').coinLen (f x).length := by
    rw [liftVerifier_coinLen]
    exact V'.coins.eval_mono hxle
  have hPeq : (π.P.pullback f w p).coinLen x.length = π.P.coinLen (f x).length :=
    Strategy.coinLen_pullback π.P f w hlen
  have hSeq : S.coinLen x.length = S'.coinLen (f x).length := by
    simp only [NUPPT.coinLen, hSc, PolyExpr.eval_subst, hlen]
  calc distAdv (fun r => (((π.pullback f w p).withV V').viewV x y z r).encode) (S.simulate x z)
        (D.distinguisherL x.length)
      = distAdv (fun r => ((π.withV (liftVerifier V')).viewV (f x) (w x y) (pairEncode x z) r).encode)
          (S'.simulate (f x) (pairEncode x z)) (D'.distinguisherL (f x).length) := by
        refine (distAdv_eq_of_unifProj ((unifProj_coinTrunc hPeq.le).prod (unifProj_coinTrunc hVle))
          (unifProj_coinTrunc hSeq.le) (unifProj_coinTrunc hDle) (fun r ρ => ?_)
          (fun r ρ => ?_)).symm
        · -- the view of `V*'` in `π` re-encodes to the view of `V'` in the pulled-back protocol
          rw [distinguisherL_lift hD' hφx hDle]
          congr 2
          simp only [Protocol.viewV, Protocol.transcriptWith, Protocol.withV_P, Protocol.withV_V,
            Protocol.withV_rounds, Protocol.withV_verifierFirst, Protocol.pullback, Prod.map,
            postView_encode]
          rw [ofFn_coinTrunc_of_eq _ hPeq, ofFn_coinTrunc]
          simp only [PolyExpr.eval_subst, ← hlen, Strategy.coinLen]
          congr 2
          refine congrArg Prod.snd (exec_congr ?_ ?_ _ _)
          · intro _
            rfl
          · intro _
            exact liftVerifier_next V' _ x z _ _
        · -- the simulator for `V'` is `postView` of the simulator for `V*'`
          rw [distinguisherL_lift hD' hφx hDle]
          congr 2
          simp only [NUPPT.simulate, NUPPT.runAt_eq, hS, pairFstD_pairEncode]
          rw [ofFn_coinTrunc_of_eq _ hSeq, ← hlen]
    _ ≤ ε' (f x).length := key
    _ = ε' (p.eval x.length) := by rw [hlen]

/-! ### Theorem 124.1 -/

/-- **[PS10, Theorem 124.1], form (A): a commitment scheme and a Levin reduction to `3COL`
give a zero-knowledge protocol for `L` with soundness error `1 - 1/p(|x|) + 2^{-p(|x|)}` whose
`n|E|`-fold repetition is an interactive proof** (Thm-124.1): for a commitment scheme
`(Com, ℓ)` and a Levin reduction `(f, w)` of `(L, R)` to `(3COL, R_3COL)` with
`L ⊆ witnessLanguage R` (`hLR`),
the pulled-back `n|E|`-fold 3-colouring protocol is an interactive proof for `L` with
efficient prover w.r.t. `R`, and the pulled-back one-iteration protocol is zero-knowledge for
`R` and an interactive proof with efficient prover and soundness error
`1 - 1/p(|x|) + (1/2)^{p(|x|)}`.

**Deviation (DQ5):** the proof and the zero-knowledge statements are for the repeated and
the single-iteration protocols respectively (sequential composition, [PS10, §7.2.1], is out
of scope; the text's single zero-knowledge proof with negligible soundness error is debt that
ch. 7 discharges, ruling G3-7(d)); the reduction is an explicit hypothesis (the text's
"Cook's reduction applied to the witness" is a Levin reduction, never defined there).

**Repair (run-3 audit P11-1):** hypothesis `hLR : ∀ x ∈ L, ∃ y, R x y` added — the first and
third conjuncts are instances of `LevinReduction.efficientProverProofErr`, and without it
the reduction `id`, `w x y := []` of `(3COL, ∅)` to `(3COL, R_3COL)` refutes them on the
2-vertex one-edge graph (the pulled-back prover commits to the constant colouring
`decColoring n [] = 0` and opens two equal colours). -/
theorem zk_proof_of_levinReduction {Com : List Bool → List Bool} {ℓ : PolyExpr}
    (hC : Commitment Com ℓ) {L : Language Bool} {R : List Bool → List Bool → Prop}
    {f : List Bool → List Bool} {w : List Bool → List Bool → List Bool} {p : PolyExpr}
    (h : LevinReduction L L3COL R R3COL f w p) (hLR : ∀ x ∈ L, ∃ y, R x y) :
    EfficientProverProof ((colProtocolRep Com ℓ).pullback f w p) L R ∧
      ZK ((colProtocol Com ℓ).pullback f w p) R ∧
      EfficientProverProofErr ((colProtocol Com ℓ).pullback f w p) L R
        (fun N => 1 - 1 / (p.eval N : ℝ) + (1 / 2 : ℝ) ^ p.eval N) :=
  ⟨h.efficientProverProof hLR (colRep_efficientProverProof hC), h.zk (col_zk hC),
    h.efficientProverProofErr hLR (col_efficientProverProofErr hC)⟩

/-- **[PS10, Theorem 124.1]: if one-way permutations (with a hard-core predicate) exist, every
language with a Levin reduction to `3COL` has a zero-knowledge protocol with soundness error
`1 - 1/p(|x|) + 2^{-p(|x|)}`** (Thm-124.1, untied existential form): for `L ⊆ witnessLanguage R`
(`hLR`) there is a protocol that is an interactive proof for `L` with efficient prover w.r.t.
`R`, and a protocol that is zero-knowledge for `R` and an interactive proof with efficient
prover and soundness error `1 - 1/p(|x|) + (1/2)^{p(|x|)}` — the commitment scheme of
[PS10, Theorem 126.4] (`exists_commitment_of_owp_hardCore`) plugged into
`zk_proof_of_levinReduction`.

**Deviation:** hard-core predicate explicit (source error 47); single OWP rather than a
collection; see `zk_proof_of_levinReduction` for the two-protocol form (DQ5). The first
conjunct alone says nothing about the zero-knowledge protocol (gate 03e, minor 3:
`npProtocol` pulled back along `(f, w)` already witnesses it); the tied form, both protocols
from one commitment scheme, is `exists_commitment_zk_proof_of_owp_levinReduction`.

**Repair (run-3 audit P11-1):** hypothesis `hLR : ∀ x ∈ L, ∃ y, R x y` added (see
`zk_proof_of_levinReduction`). -/
theorem zk_proof_of_owp_levinReduction
    (how : ∃ (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool),
      OneWayPermutation P ∧ HardCore P.toFunFamily h)
    {L : Language Bool} {R : List Bool → List Bool → Prop} {f : List Bool → List Bool}
    {w : List Bool → List Bool → List Bool} {p : PolyExpr}
    (h : LevinReduction L L3COL R R3COL f w p) (hLR : ∀ x ∈ L, ∃ y, R x y) :
    (∃ π : Protocol, EfficientProverProof π L R) ∧
      ∃ π : Protocol, ZK π R ∧ EfficientProverProofErr π L R
        (fun N => 1 - 1 / (p.eval N : ℝ) + (1 / 2 : ℝ) ^ p.eval N) := by
  obtain ⟨Com, ℓ, hC⟩ := exists_commitment_of_owp_hardCore how
  obtain ⟨h1, h2, h3⟩ := zk_proof_of_levinReduction hC h hLR
  exact ⟨⟨_, h1⟩, _, h2, h3⟩

/-- **[PS10, Theorem 124.1], tied form: if one-way permutations exist, every language with a
Levin reduction to `3COL` has a zero-knowledge protocol with soundness error
`1 - 1/p(|x|) + 2^{-p(|x|)}` whose `n|E|`-fold repetition is an interactive proof**
(Thm-124.1; gate 03e, minor 3): from the text's hypothesis, a single one-way permutation, there
is a commitment scheme `(Com, ℓ)` (`exists_commitment_of_owp`, [PS10, Theorem 126.4] with the
hard-core predicate of Goldreich–Levin) for which the conclusion of
`zk_proof_of_levinReduction` holds: both protocols are built from `Com` and the reduction.

**Deviation (DQ5):** as for `zk_proof_of_levinReduction`. -/
theorem exists_commitment_zk_proof_of_owp_levinReduction
    (how : ∃ P : PermFamily, OneWayPermutation P)
    {L : Language Bool} {R : List Bool → List Bool → Prop} {f : List Bool → List Bool}
    {w : List Bool → List Bool → List Bool} {p : PolyExpr}
    (h : LevinReduction L L3COL R R3COL f w p) (hLR : ∀ x ∈ L, ∃ y, R x y) :
    ∃ (Com : List Bool → List Bool) (ℓ : PolyExpr), Commitment Com ℓ ∧
      EfficientProverProof ((colProtocolRep Com ℓ).pullback f w p) L R ∧
      ZK ((colProtocol Com ℓ).pullback f w p) R ∧
      EfficientProverProofErr ((colProtocol Com ℓ).pullback f w p) L R
        (fun N => 1 - 1 / (p.eval N : ℝ) + (1 / 2 : ℝ) ^ p.eval N) := by
  obtain ⟨Com, ℓ, hC⟩ := exists_commitment_of_owp how
  exact ⟨Com, ℓ, hC, zk_proof_of_levinReduction hC h hLR⟩

/-- Sanity (run-3 audit P11-2): the soundness error `1 - 1/k + (1/2)^k` of the one-iteration
protocols is strictly below `1` for `k ≥ 1`, since `k < 2^k` (`Nat.lt_two_pow_self`). Hence
`EfficientProverProofErr π L R (fun N => 1 - 1/(p N) + (1/2)^{p N})` with `p N ≥ N ≥ 1`
asserts genuine soundness: the verifier rejects every `x ∉ L` with probability at least
`1/p(|x|) - 2^{-p(|x|)} > 0`. -/
theorem one_sub_inv_add_half_pow_lt_one {k : ℕ} (hk : 0 < k) :
    1 - 1 / (k : ℝ) + (1 / 2 : ℝ) ^ k < 1 := by
  have hlt : k < 2 ^ k := Nat.lt_two_pow_self
  have h2 : (k : ℝ) < (2 : ℝ) ^ k := by exact_mod_cast hlt
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have h3 : (1 / 2 : ℝ) ^ k = 1 / (2 : ℝ) ^ k := by rw [one_div_pow]
  have h4 : 1 / (2 : ℝ) ^ k < 1 / (k : ℝ) := one_div_lt_one_div_of_lt hkpos h2
  linarith

/-- NP-hardness with Levin reductions [PS10, §4.7, Theorem 124.1, step 2, the implicit
hypothesis] (Claim-124.b/c as a hypothesis): every language with a witness relation Levin-reduces
to `(L', R')`. The string-level Levin reduction `3SAT → 3COL` that would establish
`LevinNPHard L3COL R3COL` is not formalized (plan decision on Theorem 124.1). -/
def LevinNPHard (L' : Language Bool) (R' : List Bool → List Bool → Prop) : Prop :=
  ∀ (L : Language Bool) (R : List Bool → List Bool → Prop), WitnessRelation L R →
    ∃ (f : List Bool → List Bool) (w : List Bool → List Bool → List Bool) (p : PolyExpr),
      LevinReduction L L' R R' f w p

/-- **[PS10, Theorem 124.1], "every language in NP", for every witness relation** (Thm-124.1;
gate 03e, minors 3 and 4): under NP-hardness of `3COL` with Levin reductions, for a commitment
scheme `(Com, ℓ)` and every witness relation `R` of `L` there is a Levin reduction `(f, w)` of
`(L, R)` to `(3COL, R_3COL)` with length polynomial `p ≥ id` for which the pulled-back
one-iteration 3-colouring protocol is zero-knowledge for `R` with soundness error
`1 - 1/p(|x|) + 2^{-p(|x|)}`, and its `n|E|`-fold repetition is an interactive proof with
efficient prover (`zk_proof_of_levinReduction`, with `hLR` from `WitnessRelation.mem_iff`).

**Deviation (DQ5):** as for `zk_proof_of_levinReduction`. -/
theorem zk_proof_of_witnessRelation (h3 : LevinNPHard L3COL R3COL)
    {Com : List Bool → List Bool} {ℓ : PolyExpr} (hC : Commitment Com ℓ) {L : Language Bool}
    {R : List Bool → List Bool → Prop} (hR : WitnessRelation L R) :
    ∃ (f : List Bool → List Bool) (w : List Bool → List Bool → List Bool) (p : PolyExpr),
      (∀ N, N ≤ p.eval N) ∧
      EfficientProverProof ((colProtocolRep Com ℓ).pullback f w p) L R ∧
      ZK ((colProtocol Com ℓ).pullback f w p) R ∧
      EfficientProverProofErr ((colProtocol Com ℓ).pullback f w p) L R
        (fun N => 1 - 1 / (p.eval N : ℝ) + (1 / 2 : ℝ) ^ p.eval N) := by
  obtain ⟨f, w, p, h⟩ := h3 L R hR
  exact ⟨f, w, p, h.le_eval, zk_proof_of_levinReduction hC h fun x hx => (hR.mem_iff x).1 hx⟩

/-- **[PS10, Theorem 124.1], "if one-way permutations exist then every language in NP has a
zero-knowledge proof", for every witness relation** (Thm-124.1; gate 03e, minors 3 and 4):
from the text's hypothesis, a one-way permutation, there is a commitment scheme
(`exists_commitment_of_owp`) for which the conclusion of `zk_proof_of_witnessRelation` holds,
under NP-hardness of `3COL` with Levin reductions.

**Deviation (DQ5):** as for `zk_proof_of_levinReduction`. -/
theorem zk_proof_of_witnessRelation_of_owp (h3 : LevinNPHard L3COL R3COL)
    (how : ∃ P : PermFamily, OneWayPermutation P) {L : Language Bool}
    {R : List Bool → List Bool → Prop} (hR : WitnessRelation L R) :
    ∃ (Com : List Bool → List Bool) (ℓ : PolyExpr), Commitment Com ℓ ∧
      ∃ (f : List Bool → List Bool) (w : List Bool → List Bool → List Bool) (p : PolyExpr),
        (∀ N, N ≤ p.eval N) ∧
        EfficientProverProof ((colProtocolRep Com ℓ).pullback f w p) L R ∧
        ZK ((colProtocol Com ℓ).pullback f w p) R ∧
        EfficientProverProofErr ((colProtocol Com ℓ).pullback f w p) L R
          (fun N => 1 - 1 / (p.eval N : ℝ) + (1 / 2 : ℝ) ^ p.eval N) := by
  obtain ⟨Com, ℓ, hC⟩ := exists_commitment_of_owp how
  exact ⟨Com, ℓ, hC, zk_proof_of_witnessRelation h3 hC hR⟩

/-- **[PS10, Theorem 124.1], "every language in NP", one-iteration form: a zero-knowledge
protocol with soundness error `1 - 1/p(|x|) + 2^{-p(|x|)}`**, under NP-hardness of `3COL` with
Levin reductions: for a commitment scheme and every `L ∈ NP` there is a witness relation `R` for
`L` with an interactive proof with efficient prover, and a protocol that is zero-knowledge
for `R` and an interactive proof with efficient prover and soundness error
`1 - 1/p(|x|) + (1/2)^{p(|x|)}`, where `p ≥ id` is the length polynomial of the Levin
reduction (the two protocols of `zk_proof_of_levinReduction`; the witness relation from
`exists_witnessRelation_of_mem_NP`, [PS10, Definition 191.11], supplies `hLR`). This is the
corollary of `zk_proof_of_witnessRelation`, which holds for every witness relation (gate 03e,
minor 4) and ties the two protocols together; here the conjunct
`∃ π, EfficientProverProof π L R` alone says nothing about the zero-knowledge protocol
(`npProtocol` witnesses it, minor 3).

**Repair (run-3 audit P11-2):** the run-2 conclusion `∃ s, EfficientProverProofErr π L R s`
asserted no soundness (`s := 1` turns the clause into `0 ≤ uprob …`, so it followed from the
parties' efficiency and completeness alone); the explicit error of the Levin reduction's
length polynomial is kept, together with `∀ N, N ≤ p.eval N`, so that the error is below `1`
by the noticeable margin `1/p(N) - 2^{-p(N)}` (`one_sub_inv_add_half_pow_lt_one`). -/
theorem zk_proof_of_mem_NP (h3 : LevinNPHard L3COL R3COL) {Com : List Bool → List Bool}
    {ℓ : PolyExpr} (hC : Commitment Com ℓ) {L : Language Bool} (hL : L ∈ NP) :
    ∃ R : List Bool → List Bool → Prop, WitnessRelation L R ∧
      (∃ π : Protocol, EfficientProverProof π L R) ∧
      ∃ (π : Protocol) (p : PolyExpr), (∀ N, N ≤ p.eval N) ∧ ZK π R ∧
        EfficientProverProofErr π L R
          (fun N => 1 - 1 / (p.eval N : ℝ) + (1 / 2 : ℝ) ^ p.eval N) := by
  obtain ⟨R, hR⟩ := exists_witnessRelation_of_mem_NP hL
  obtain ⟨_, _, p, hp, h1, h2, h3'⟩ := zk_proof_of_witnessRelation h3 hC hR
  exact ⟨R, hR, ⟨_, h1⟩, _, p, hp, h2, h3'⟩

/-- **[PS10, Theorem 124.1], "if one-way permutations exist then every language in NP has a
zero-knowledge proof", one-iteration form: a zero-knowledge protocol with soundness error
`1 - 1/p(|x|) + 2^{-p(|x|)}`**, under NP-hardness of `3COL` with Levin reductions and with the
hard-core predicate explicit (`exists_commitment_of_owp_hardCore`, `zk_proof_of_mem_NP`):
the zero-knowledge protocol has the explicit soundness error `1 - 1/p(|x|) + (1/2)^{p(|x|)}`
of the Levin reduction's length polynomial `p ≥ id`.

**Repair (run-3 audit P11-2):** explicit soundness error instead of the vacuous
`∃ s, EfficientProverProofErr π L R s` (see `zk_proof_of_mem_NP`). The form for every witness
relation, from the text's hypothesis (a one-way permutation) and with the two protocols tied,
is `zk_proof_of_witnessRelation_of_owp` (gate 03e, minors 3 and 4). -/
theorem zk_proof_of_mem_NP_of_owp (h3 : LevinNPHard L3COL R3COL)
    (how : ∃ (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool),
      OneWayPermutation P ∧ HardCore P.toFunFamily h)
    {L : Language Bool} (hL : L ∈ NP) :
    ∃ R : List Bool → List Bool → Prop, WitnessRelation L R ∧
      (∃ π : Protocol, EfficientProverProof π L R) ∧
      ∃ (π : Protocol) (p : PolyExpr), (∀ N, N ≤ p.eval N) ∧ ZK π R ∧
        EfficientProverProofErr π L R
          (fun N => 1 - 1 / (p.eval N : ℝ) + (1 / 2 : ℝ) ^ p.eval N) := by
  obtain ⟨Com, ℓ, hC⟩ := exists_commitment_of_owp_hardCore how
  exact zk_proof_of_mem_NP h3 hC hL

end TCSlib.Cryptography

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/03e-pack.md =====

# Gate 03e ([PS10] ch. 2–4, interaction and ZK definitions): external statement audit pack

**Status: ready to dispatch** (staged 2026-11-05 at the merged head after #192 and #193; the evidence is under `evidence/e/`).

**What is audited:** the asymptotic layer of [PS10] ch. 2–4 on `cryptography/pass-shelat-ch2-4`, at
`a3c5fa8b72e50939822f22364647dc844a3914a0`. This pack covers the interaction model (strategies, executions, views, protocols), interactive proofs, the zero-knowledge definitions, commitments, and the NP layer used by Thm 124.1.
- **Gate type:** an external **statement gate** (`workflow.md` §3; user's ruling of 2026-11-05),
  over a layer written in another campaign (Frederick Dehmel's, now closed). That layer had only
  an internal audit (run 3a, summary in the bundle).
- **The deliverable:** **`gate03e-findings.md`**.

The bundle holds this pack, then every file named below under a `## ===== <path> =====` header.
**The source is attached separately:** [PS10], 3rd ed., January 2010 (PDF). Book page = PDF
page − 12. This pack needs §4.4–§4.7 (book pp. 114–127) and the appendix definition Def 191.11.

## Brief for the auditor

Pack 03a's brief applies unchanged (its pack is in the bundle): the trusted surface, the six
things to hunt for, the inventory check, restating every definition in your own words, and 1–3
sentences per theorem. Attempt at least **three adversarial instantiations**, for example:
- a verifier that is efficient but reads exponentially long messages;
- a "proof" whose soundness holds only because the verifier's verdict is ill-defined;
- a simulator that is efficient only because the auxiliary input is bounded.

Check the run-3a repairs in scope instead of re-finding them. Do not give a blanket approval.

## Scope

| Item | Where |
|---|---|
| Under audit | `TCSlib/Cryptography/ZeroKnowledge/{Interaction, InteractiveProofs, Defs, Commitment, NP}.lean` |
| The common brief | `briefs/pass-shelat-ch5-8/gates/03-ch2-4/03a-pack.md` (for its brief and severity guide; its questions are not this pack's) |
| Context, not under audit | packs 03a–03d's files: earlier packs of this gate |
| Design record | `briefs/pass-shelat/DESIGN.md` (§1 D1–D11, §2.15 the frozen ch. 4 signatures (with D8, the interaction reading), §5 the deviations register) |
| Inventory | `briefs/pass-shelat/inventory-ch4.md`: Def-114.a, Def-114.b, Def-115.a–d, Def-116.a, Def-116.b, Def-116.1, Def-117.a, Def-117.b, Claim-117.c, Def-119.5, Def-119.e, Def-191.11, Def-121.1, Def-121.2, Def-122.a, Claim-122.b, Def-124.a, Def-126.3, Claim-126.a, Thm-126.4, Alg-127.a, Claim-127.b–d |
| Internal audit record | `audits/pass-shelat/run3-audit-summary.md` |
| Source | [PS10] as above (PDF attached) |
| Standards | `policy.md` |
| Out of scope | tactic proofs; the protocols and their proofs (graph isomorphism, 3-colouring: packs 03g and 03k) |

## Attestations (maintainer execution claims; evidence under `evidence/` in the bundle)

### Attestation results at `a3c5fa8b72e50939822f22364647dc844a3914a0` (evidence under `evidence/e/`)

1. **Elaboration** (`replay.log`): the closure of this pack's files, 358 modules, each
   checked alone into a fresh olean tree by `scripts/lean_check_tree.sh`: all pass, 0 errors;
   25 `sorry` warnings in the closure.
2. **Axioms** (`axioms.log`): 26 headline prints from `audits/pass-shelat/Checks.lean` for
   declarations in this pack's files: 22 use only the standard axioms, and
   4 depend on `sorryAx`.
3. **Admissions** (`admissions.txt`): 0 declarations in this pack's files contain `sorry`.
4. **Lint** (`lint.log`): `scripts/style_lint.py` on this pack's files: 0 findings in 5 files.

Pack-specific notes (as drafted):
- elaboration (a fresh replay of the closure);
- the axiom prints for this pack's headline theorems (`audits/pass-shelat/Checks.lean`);
- admissions: none in these five files;
- lint;
- interface use. The declarations cited by ch. 5–8 are `Strategy`, `View`, `Protocol`, `InteractiveProof`, `ZK`, `PerfectZK`, `PerfectZKAbort` and
  `Commitment`. **Context for the auditor:** ch. 5–8 runs protocols in a new framework, through a
  bridge to these definitions (`Party.exec`, under D8's reading). The ruling of 2026-11-05 carries
  D8's strict or truncated simulators into the sequential composition of ch. 7.

## Specific questions

1. **The interaction model (Defs 114.a–116.b; D8).**
   - Is the fixed-alternation reading of D8 (the next-message function on the complete history is
     the output; a halting party sends `[]`) benign for every use in ch. 4?
   - Is the verdict convention (P9-3: the verifier's last message is its verdict when it moves
     last) a restriction that excludes any protocol of the source?
2. **Efficiency (Def 116.b).**
   - `Strategy.Efficient` is polynomial in the total input length, with `ReadsPrefix` restoring
     the bound in `|x|`. Is that faithful to "time `t(|x|)` regardless of messages"?
   - Is `ReadsPrefix` required wherever the source needs it?
   - **Known consequence (maintainer, 2026-11-05).** `ZK` quantifies over `Strategy.Efficient`
     verifiers without `ReadsPrefix`. Such a verifier may double its messages from activation to
     activation, so over polynomially many rounds, against an honest prover that echoes it, its
     view can grow exponentially, and no strict-PPT simulator can output it. Ch. 5–8's sequential
     composition (Thm 175.1) therefore assumes bounded honest-prover messages
     (`Protocol.ProverBounded`). Does any ch. 2–4 ZK theorem depend on this gap? The honest
     provers of the graph protocols have fixed message lengths. Should `ZK` itself require
     `ReadsPrefix` of `V*`? (Queued for the user as Q-1.)
3. **Interactive proofs (Def 116.1).** Are completeness and soundness stated against every
   (unbounded) prover, with the source's error bounds?
4. **Zero knowledge (Defs 121.1, 121.2, 122.a).**
   - Are `ZK` (every n.u.p.p.t. `V*` with auxiliary input), `PerfectZK` and the statistical form
     faithful?
   - D8 uses strict PPT simulators where the source has expected polynomial time. Is
     `PerfectZKAbort` (truncation with abort) an adequate stand-in for the source's perfect ZK
     protocols?
5. **Commitments (Def 126.3, Thm 126.4, Alg 127.a).** Are hiding and binding at the source's
   strength (computational hiding, perfect binding), and is the OWP-based scheme stated correctly?
6. **NP and Levin reductions (Def 124.a, Def 191.11; `NP.lean`).** Is the NP relation (efficient
   verifier, polynomially bounded witness) and the witness-preserving reduction the one
   Thm 124.1's form (A) needs?

## Findings format (auditor fills)

As in pack 03a: one table, `# | Severity | File · declaration | Claim | Evidence / counterexample |
Proposed fix`, with the same severity guide. The pack closes at **0 blockers and 0 majors**.

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/03a-pack.md =====

# Gate 03a ([PS10] ch. 2–4, machines and probability): external statement audit pack

**Status: ready to dispatch** (staged 2026-11-05 at the merged head after #192 and #193; the evidence is under `evidence/a/`).

**What is audited:** the asymptotic layer of [PS10] ch. 2–4 on `cryptography/pass-shelat-ch2-4`, at
`a3c5fa8b72e50939822f22364647dc844a3914a0`. This pack covers the machine model and the probability
notions on which the rest of the layer, and ch. 5–8, are stated.
- **Gate type:** an external **statement gate** (`workflow.md` §3; user's ruling of 2026-11-05).
  The layer was written in another campaign (Frederick Dehmel's, now closed). It had an internal
  adversarial statement audit (run 3a, summary in the bundle), but never an external one.
- **The deliverable:** **`gate03a-findings.md`**.

The bundle holds this pack, then every file named below under a `## ===== <path> =====` header.
**The source is attached separately:** [PS10] R. Pass, a. shelat, *A Course in Cryptography*, 3rd
ed., January 2010 (PDF). Book page = PDF page − 12; item numbers carry the book page. This pack
needs §2.1 and Definition 27.2 (book pp. 21–27), and §3.1 (book pp. 69–73).

## Brief for the auditor

You are auditing the **trusted surface**: definitions, theorem statements, docstrings and proof
sketches. Most proofs are machine-checked; do not review tactic scripts. Hunt for:
1. **Infidelity to the source:** a definition or statement that differs from [PS10]'s, other than
   by a deviation declared in its docstring and in `DESIGN.md` (§1 decisions D1–D11, §5 the
   deviations register). Check that each declared deviation is benign, or that its cost is stated.
2. **Wrong semantics:** a definition that does not compute what its docstring says.
3. **Trivialization:** vacuous or unsatisfiable hypotheses; definitions satisfiable for
   degenerate reasons (for example, a machine class that is empty, or that contains every function).
4. **Wrong strength:** a theorem weaker or stronger than its docstring claims; boundary cases
   (`n = 0`, empty coin strings, length-0 advice).
5. **Fitness for the layer's use:** these declarations are the interface that every later
   statement of ch. 2–4 and of ch. 5–8 cites. A definition that cannot express its later uses is a
   finding.
6. **Attribution:** `policy.md` §2.

**Checking against the inventories.** For every row of `inventory-ch2.md` and `inventory-ch3.md`
whose location is one of this pack's files, state whether the item is formalized faithfully. For
**every definition**, restate it in your own mathematical English before reading its docstring,
and report any daylight. For **every theorem**, say in 1–3 sentences whether its statement is what
the docstring claims. Attempt at least **three adversarial instantiations** (a degenerate machine,
a degenerate ensemble, an adversary exploiting the advice). The run-3a summary lists the internal
audit's findings and repairs: check that its repairs hold, and do not re-report a finding it
resolved unless the resolution is wrong. Do not give a blanket approval.

## Scope

| Item | Where |
|---|---|
| Under audit | `TCSlib/Complexity/Randomized/{PolyExpr, PPT, Primitives, Closure, Repetition, NonUniform}.lean`, `TCSlib/Cryptography/Asymptotic/{Adversary, Sampling, Ensembles}.lean`, and the new bridge `TCSlib/Cryptography/Asymptotic/SamplingFinDist.lean` (`StatClose` of samplers is `EpsClose` of their laws; duplication-ledger item DL-4) |
| Context, not under audit | `TCSlib/Cryptography/Foundations/Negligible.lean` (audited in the Garg ch. 1–3 campaign) |
| Design record (states the intent and the declared deviations) | `briefs/pass-shelat/DESIGN.md` |
| Inventories | `briefs/pass-shelat/inventory-ch2.md`, `briefs/pass-shelat/inventory-ch3.md` |
| Internal audit record | `audits/pass-shelat/run3-audit-summary.md` |
| Source | [PS10] §2.1, Def 27.2, §3.1 (PDF attached) |
| Standards | `policy.md` |
| Out of scope | tactic proofs; the machine constructions of `Complexity/Randomized/Build/` (pack 03l), whose statements this pack's files use |

## Attestations (maintainer execution claims; evidence under `evidence/` in the bundle)

### Attestation results at `a3c5fa8b72e50939822f22364647dc844a3914a0` (evidence under `evidence/a/`)

1. **Elaboration** (`replay.log`): the closure of this pack's files, 323 modules, each
   checked alone into a fresh olean tree by `scripts/lean_check_tree.sh`: all pass, 0 errors;
   22 `sorry` warnings in the closure.
2. **Axioms** (`axioms.log`): 41 headline prints from `audits/pass-shelat/Checks.lean` for
   declarations in this pack's files: 40 use only the standard axioms, and
   1 depend on `sorryAx`.
3. **Admissions** (`admissions.txt`): 1 declarations in this pack's files contain `sorry`.
4. **Lint** (`lint.log`): `scripts/style_lint.py` on this pack's files: 2 findings in 11 files.
   Both are in `SamplingFinDist.lean`, the dedup's new bridge (the maintainer's file): a missing
   `set_option maxHeartbeats 0` and a missing `## Main definitions` heading. Style only; fixed with
   gate 03's repairs.

Pack-specific notes (as drafted):
1. **Elaboration:** a fresh replay of the closure.
2. **Axioms:** the prints for this pack's headline theorems, from `audits/pass-shelat/Checks.lean`.
3. **Admissions:** the one `sorry` in scope, `NUPPT.decides_of_decidesWithAdviceInTime`
   (`NonUniform.lean`), an optional bridge outside the mandatory core (Frederick's open question 5).
4. **Lint.**
5. **Interface use:** the declarations of this pack cited by ch. 5–8 (S1 note, point 3) are
   `Complexity.NUPPT`, `Complexity.PPT`, `NUPPT.Uniform`, `NUPPT.runAt`, `NUPPT.Computes`,
   `NUPPT.ofPolyTime`, the closure calculus, `Negligible`, `Ensemble`, `Ensemble.Indist`,
   `Ensemble.Samplable` and `StatClose`.

## Specific questions

1. **The machine model.**
   - Do `PPT` and `NUPPT` capture [PS10] Defs 23.4, 23.5 and 26.8?
     - The coins are an explicit polynomial-length input.
     - The advice has length `Cα (n+1)^cα`, and the machine runs on `⟨⟨x, α |x|⟩, r⟩`.
     - The time bound is polynomial in what?
   - Is `NUPPT.Uniform` the uniform class?
   - Does the D4 reading of "|A_i| < d(i)" (advice in place of a sequence of machines) lose
     anything?
2. **Computing with probability 1** (Def 24.6). Does `NUPPT.Computes` require the same output on
   every coin string, and is that the source's notion?
3. **Polynomials.** Does `PolyExpr` (explicit polynomial expressions) cover every bound the layer
   needs? Is anything stated "for some polynomial" where the source quantifies differently?
4. **The closure calculus** (Claim 26.3).
   - Is each closure lemma of `Closure.lean` and `Repetition.lean` what the reductions of ch. 2–4
     need: pre- and post-composition, pairing, hard-wiring, polynomially many calls with fresh coins?
   - Is any hypothesis stronger than the uses can meet?
5. **Statistical closeness** (`Sampling.lean`, `SamplingFinDist.lean`). Is `StatClose` the source's
   statistical distance, or an equivalent form, for samplers? Is it preserved by the operations
   stated? Does `statClose_iff_epsClose_map` make it exactly `main`'s `EpsClose` ([PS10, Def 181.1])
   on finite sample spaces?
6. **Ensembles and indistinguishability** (Defs 69.3, 69.4; Lems 71.5, 71.6).
   - Is `Ensemble.Indist` "for every n.u.p.p.t. distinguisher, the advantage is negligible", with
     the source's quantifier order?
   - Is the advice of the distinguisher handled as the source does?
   - Are the hybrid lemma and the closure under efficient operations stated at the right strength?
7. **Adversaries** (`Adversary.lean`). Is the adversary interface faithful to how [PS10] quantifies
   over adversaries in ch. 2–3?
8. **The one admission.** Is `decides_of_decidesWithAdviceInTime` true as stated, and correctly
   labelled optional?

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | blocker / major / minor / note | | | | |

Severity guide:
- **blocker:** a downstream statement (in ch. 2–4 or ch. 5–8) would build on a wrong definition or
  statement;
- **major:** fixable but materially misleading as it stands, or debt that needs explicit human
  acknowledgment;
- **minor:** an edge case, or a naming or attribution defect;
- **note:** an observation; no change required.

The pack closes at **0 blockers and 0 majors**.

## ===== policy.md =====

# TCSlib Contribution Policy

Standards for all Lean contributions to this repository, whether written by humans or by
agents. This document covers three things: **modularity** (how code is organized),
**attribution** (how every result is traced to a source), and **proof sketches** (how every
formal proof is accompanied by readable mathematics).

It complements, and does not replace:

- `workflow.md` — the campaign formalization process (phases, audit gates, fill epochs)
  that produces code meeting these standards.
- `.github/copilot-instructions.md` — build workflows, import rules, CI integration points.
- `AGENTS.md` / `.claude/CLAUDE.md` — the sorry-ladder proof workflow and agent roster.
- `blueprint/BLUEPRINT_PIPELINE.md` — how blueprint entries are generated and validated.

Where this document names an existing mechanism (blueprint macros, hygiene scripts), the
policy is to *use that mechanism*, not to invent a parallel one.

## 1. Modularity

**Layout.** Content lives at `TCSlib/<Area>/<Topic>/<Piece>.lean`, one coherent concept or
lemma cluster per file, with a facade file `TCSlib/<Area>/<Topic>.lean` that imports every
child and carries a `/-! -/` module docstring with a `## Contents` list (one line per child).
See `TCSlib/Complexity/NPReductions.lean` for the reference example.

**File size.** Target 150–600 lines per math file. A file approaching 1000 lines should be
split unless there is a positive reason not to (e.g. a single long proof that cannot be
usefully decomposed).

**Exports.** Every new topic facade must be imported from `TCSlib.lean`. CI only builds what
is reachable from `TCSlib.lean`; an unexported file is invisible to CI, docs, and the
blueprint.

**Imports.** Precise module imports only. A bare `import Mathlib` fails CI. Import only what
the file uses.

**Namespaces.** Namespaces are area-local: pick one namespace root per topic and use it
consistently within that topic. Do not leak auxiliary definitions into the root namespace;
mark internal helpers `private` or put them in a dedicated inner namespace.
*Model registry exception*: a model-defining **type** (a machine, circuit, formula, or
decision-tree model) may live at the root namespace, Mathlib-style, provided it is
registered in the catalog facade `TCSlib/ComputationalModels.lean`; its operations and
lemmas still live in the type's own namespace. Anything else at root is a leak.

**Layering.** Keep definition files separate from heavyweight theorem files, so that
downstream work can import a model or a class definition without pulling in every proof about
it. When a development has both a "raw/general" layer and a "bundled" layer (e.g. a machine
model that is parametric in its types, plus a bundled version carrying finiteness instances),
headline definitions and theorems are stated against the bundled layer; the raw layer is
internal plumbing.

**Helpers.** Foundational helper lemmas that serve a whole area belong in that area's
`Basic.lean`, not in the file that first needed them.

**Definitions land with their lemmas** (user, 2026-10-16). Every new public `def` is published,
in the same PR and beside the definition, with the lemmas that let a consumer read it without
unfolding:
- a structure-valued definition (a contract, a configuration, zone contents): its field
  equations, generated by `simps` with `(config := { isSimp := false })` and explicit
  projections (`simps!` where the body is another constructor's result);
- any other definition: an equation lemma `<name>_eq` (by `rfl` where that holds), or case
  lemmas that together cover every input (`_of_lt`/`_of_le`, `_true`/`_false`, one per
  constructor);
- a predicate: an `_iff` characterization;
- a machine: its run or contract lemma, the only way consumers read a machine.

None carries `@[simp]` unless a gate approves it, and each docstring states its formula. Consumers
never unfold another file's definition (the no-unfolding rule of the briefs, user 2026-10-16). The
rule binds TCSlib's own definitions: core and Mathlib definitions may reduce in a `rfl`, `decide`
or `show` step, but are never passed to `simp`, `rw` or `unfold`; use their equation lemmas
(`Bool.toNat_true`, not `simp [Bool.toNat]`) (user, 2026-10-23).
**Reducible abbreviations are notation** (user, 2026-10-26). Lean unfolds a TCSlib `abbrev` (such
as `Turing.Cfg.Halted`, `cfg.state = none`) at every step, and the standard seal cannot cover it:
under Lean's default reducibility validation, `attribute [local irreducible]` fails on a reducible
declaration (only the unsafe override `set_option allowUnsafeReducibility true`, which the
campaign's seals do not use, lifts the check). So reading an abbreviation through its body,
for example `¬ c.Halted` as `c.state ≠ none`, is allowed and is not a definitional closure. A
consumer names it in `simp`, `rw` or `unfold` only through a published lemma where one exists, and
a new public `abbrev` still lands with its `_iff` or `_eq` lemma.
They read the machine model's primitives (`MultiTapeTM.step`, `runFrom`, `Action.apply`,
`Cfg.mapState`) through the existing lemmas. The style lint's check 8 reports, per file, every
public `def` with no lemma named after it and no `simps` attribute, so a head-against-base diff
of the lint shows any new definition that lacks one. Definitions that predate the rule are listed
by the same check and covered as consumers need them.

**Construction reuse.** Machines are built from the verified construction layers, not from
scratch: the combinators and routine catalog of `TCSlib/Complexity/TuringMachine/Build/`
(conventions, wrappers, loops, primitives, embeddings, seams, and the catalog rows —
`machine-library-design.md` is the registry), the registered hosts (**Hosts come first**,
below), and the program layers (`LogProg.ARM`, `CounterProg`, and the general programming
layer of `machine-library-design.md` §15 once it lands) where a program-level description
suffices. Before writing a transition
table by hand, check the registry; a routine that exists is cited, not re-derived. A routine
that *almost* exists is the interesting case: do not write a third private variant — either
consume the general form, or commission the missing form into the shared layer (during a
fill batch: a `private` local copy plus a "requested shared lemma" in the report, promoted
at the next shared-file window). A hand-built machine is acceptable only when no layer
covers the need, and its docstring must say so and name what was missing — that sentence is
what turns the gap into the next catalog row. The chapter-1/2 files that predate this layer
re-derived the same bank/relocation/dispatch/frame families four times over (`emitterBank*`,
`clBank*`, `clSlot*`, …); the retrofit paying that debt back is the standing cautionary
tale. The same discipline applies to circuit construction once `CircuitComplexity`'s gadget
layer exists: gadgets, wiring combinators, and size/depth ledgers get one shared home and a
registry, and new circuits are assembled from it.

**Hosts come first.** A *host* is a control structure that drives other routines rather than
computing one value: a search or traversal (BFS, DFS, backtracking, an odometer over
assignments), a recursion or evaluation scheme (AND/OR evaluation, Savitch's midpoint
recursion), an interpreter or simulation step block, a clocked or windowed runner, a dispatcher
over a data structure (tables, records), or an input device. Any routine whose natural contract
does not depend on its first consumer counts as a host; leaf rows (copy, compare, seek,
arithmetic) do not. **A host is never built `private` inside the proof that first needs it.**
Its public contract is designed, statement-gated and placed in the shared construction layer
first, generic in the parts its consumers vary (the leaf test, the step relation, the data
domain), with time and space (head-envelope) clauses. Consumers cite it, under the campaign's
proved-modulo rule while its own fill is still running. The host registry is
`machine-library-design.md` §14. A private host already in the tree is harvested into the
shared layer before a second consumer is briefed against it. The rule exists because private
hosts were the main way the library overfitted to single proofs: four configuration encodings,
three reachability notions and a private search host per theorem, each to be re-derived by the
next consumer (assessment of 2026-10-12, recorded in the design document). (User, binding,
2026-10-12.)

**Duplication.** Some duplication is mechanically forced by the campaign discipline —
exclusive file ownership, the statement freeze, and `private` visibility leave a fill batch
no other legal way to use another file's unexported machinery — and occasionally it is the
right engineering call. It is never silently acceptable: **every instance of duplicated
proved material must be human-approved.** A fill batch discloses each copy in its report;
the maintainer's integration ledger totals copied material per file (`workflow.md` §4); and
the audit template treats accumulated duplication as a major finding that a gate cannot
close over without the human maintainer explicitly accepting the debt and naming where and
when it is paid back (the registry's dedup/refactor queue). Duplication that was never
disclosed is a freeze violation, not debt.

**File header.** Every math file begins with the Mathlib-style copyright block, its imports,
the repo-standard options

```
set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false
```

then a module docstring containing `# Title`, `## Main definitions`, `## Main results`, and
`## References` (see §2).

## 2. Attribution

Every mathematical statement in the library must be traceable to a source, at the level of
precision of a textbook theorem number or a paper section.

**File-level.** Every math file's module docstring contains a `## References` section giving
full citations with short tags, e.g.

```
## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
```

**Declaration-level.** Every definition, theorem, and lemma that corresponds to a result in
a source carries the tag with a precise location in its docstring: `[AB09, Claim 1.6]`,
`[AB09, §1.7]`, `[GRS25, Thm 4.2.1]`. Purely technical glue lemmas with no textbook
counterpart may omit the tag; anything a reader would recognize as "a result" may not.

**Deviations.** If the formal statement deviates from the source — different constants,
strengthened or weakened hypotheses, a reformulation — the docstring must say so and briefly
say why (e.g. "stated with explicit constant 5k rather than O(·), following the proof").

**Statement prose.** Every public declaration's docstring begins with a natural-language
statement of what it asserts (for a definition: what it is), precise enough that a reader
could judge the formalization's fidelity without parsing the Lean. The `[Tag, location]`
citation and any deviation note attach to that statement; the proof sketch (§3) follows it.
A bare label ("Unfolding lemma", "Helper for X") is not a statement. Instances are exempt,
as are vendored files (which follow upstream style). `private` declarations should carry
docstrings too, but at reviewer discretion rather than as a hard requirement. The blueprint
remains the cross-referenced informal layer for dependency structure (see **Blueprint**);
the docstring statement is what external audits compare blind restatements against, so it
is part of the trusted surface.

**Blueprint.** When an ingested reference exists under `blueprint/src/references/`, blueprint
entries use `\statementsource{<ref>}{<anchor>}` and `\proofsource{<ref>}{<anchor>}` to cite
it, subject to the existing rule that these are written only after an approved proofmatch
run. When starting a new chapter or paper, ingest it as a reference pair
(`<name>.raw.md` + `<name>.md`) so these citations are possible: put the PDF under
`blueprint/src/references/` in the change that formalizes it and run
`python3 scripts/dataset_pipeline.py --yes`, which ingests it, matches every text the
blueprint does not cite yet, and carries the new statements into the dataset
(`python3 scripts/sources.py add TAG=<pdf or md>` does the ingest and match alone, with
the docstring tag above; `python3 scripts/sources.py` shows which texts are attached and
which are still missing; see `dataset/INSTRUCTIONS.md`). The dataset builder does not
search outside that directory for sources; an unattached text leaves the theorems with
informalized proof notes instead of citations.

**Vendored code.** Lean code adapted from another project keeps the original copyright
header and license notice, and its file docstring names the source project, the commit it
was taken from, and a summary of local modifications.

**Design adaptation.** When a construction, proof architecture, or module design is
adapted from — or materially inspired by — another project's code, the debt is cited even
when no code is transcribed. The module docstring's `## References` section names the
source project, author, module or archive entry, the commit or version consulted, and its
license, with a short tag usable at declaration level; the precedent is
`TuringMachine/Composition.lean`'s `[Balbach22]` for the Isabelle AFP `Cook_Levin`
composition-combinator architecture. Design documents and blueprint entries built on the
adapted design carry the same citation. Examining external code purely for comparison,
with nothing taken, creates no citation duty, but on a campaign it belongs in the
campaign's records (plan decision log or backlog) so the provenance question is answerable
later. (Maintainer guideline, binding, 2026-10-06.)

## 3. Proof sketches

Every nontrivial formal proof is accompanied by a human-readable English proof sketch, kept
next to the Lean it describes.

**What counts as nontrivial.** Rule of thumb: any proof longer than ~20 lines of tactics, or
that would rate difficulty ≥ 3 on the blueprint scale. One-line `simp`/`omega`/`exact`
proofs need no sketch.

**Where sketches live.** In the Lean file itself:

- For most theorems: a `**Proof sketch.**` paragraph at the end of the theorem's docstring,
  written in mathematical English (not Lean identifiers), naming the key intermediate steps.
- For long proofs: additionally, short comments at the major `have`/section boundaries tying
  the tactics back to the sketch's steps.

The named intermediate steps of a sketch should be visible in the formalization as `have`s
or standalone lemmas — if the sketch says "first reduce to the one-tape case", there should
be a lemma that is that reduction.

**Where sketches do not live.** Not in the blueprint. Blueprint statement entries state
claims only; `scripts/dataset_hygiene.py --strict` hard-fails on proof content there. The
blueprint records *what* is true and its dependency structure; the Lean docstrings record
*why* it is true.

**Sketches and the sorry ladder.** When landing a sorry-skeleton, write the sketch at
skeleton time — the sketch *is* the plan, and each `sorry` should correspond to a named step
of it. A skeleton whose sketch cannot be written is not ready to land.

**Synchronization.** When a proof strategy changes, the sketch changes in the same commit.
A sketch that describes a proof the code no longer performs is worse than no sketch.

## Review checklist

Before merging new Lean content, check:

1. Files follow the Area/Topic layout with a facade, and `TCSlib.lean` exports are updated.
2. Imports are precise; no bare `import Mathlib`.
3. Every file has a `## References` section; every source-derived declaration has a
   `[Tag, location]` in its docstring; deviations from sources are noted.
4. Every nontrivial proof (or sorry-stub standing in for one) has a proof sketch.
5. Every public declaration (instances and vendored files excepted) has a docstring
   opening with a natural-language statement of what it asserts
   (`python3 scripts/style_lint.py` checks presence mechanically; statement quality is
   review judgment).
6. `zsh scripts/lean_check.sh <file>` reports zero errors for each touched file.
7. If blueprint content was touched: `python3 scripts/blueprint_validate.py --strict` and
   `python3 scripts/dataset_hygiene.py --strict` pass.
8. No new private host: every search, recursion, interpreter, runner or input device the
   change introduces is a registered public host, or cites one (§1, **Hosts come first**).

## ===== briefs/pass-shelat/DESIGN.md =====

# FROZEN DESIGN — Pass–shelat Chapters 2–4 computational-model layer and workstream map

Run 1 synthesis (2026-10-27). Inputs: `inventory-ch{2,3,4}.md`, `design-reuse-max.md`,
`design-abstract-interface.md`, `design-faithful-tapes.md`, three judge reports. Output of
this file: (1) the frozen Lean signatures, (2) the final text of the foundation decisions,
(3) the workstream map covering every core inventory item exactly once, (4) the
consolidated list of source errors, (5) the open questions for the maintainer.

**Evidence.** Every signature in §2 is reproduced from
`briefs/pass-shelat/DESIGN-freeze-scratch.lean` (1252 lines, 205 declarations), compiled on
2026-10-27 with `lake env lean` against the worktree: **exit 0, 0 errors, 53 `declaration
uses 'sorry'` warnings**, every sorry being a theorem stub under a stated proof plan (the
inventory of the 53 stubs is in §9). The proved parts are `PolyExpr.eval_*`, `eval_subst`,
`eval_mono`, `eval_le`, `NUPPT.output_spec`, `computesFunInTime`, `polyTimeComputable_output`,
`output_eq_of_computesInTime`, `length_advInput`, `output_ofPolyTime`,
`ofPolyTimeUniform_uniform`, `NUPPT.nonempty`, `invProbOpt_le_invProb`, `invProbOpt_some`,
`hybrid_lemma`, `prfAdv_toOracleAdversary`.

**Verdict adopted.** REUSE-MAXIMAL is the base (all three judges rank it first). The panel's
mandatory repairs are applied (§3) and the recommended grafts are taken (§4): syntactic
`PolyExpr` lengths everywhere, distribution-level samplability, `∀ q` oracle budgets, a
first-mover field and a fixed-alternation execution, literal `[false]` soundness, `≤` advice
length, literal Def 26.1 / Def 69.4 forms next to the `1^n` forms with the bridging lemmas,
abort-form perfect ZK, rejection-sampled permutations and positions, non-vacuity theorems in
`Checks.lean`, and the repaired construction of the repetition lemma. ABSTRACT-INTERFACE's
bundled class and FAITHFULNESS-FIRST's coin tape, pair-form bridges, oracle machines and
`NUPPTSeq` equivalence are **not** on the critical path (the latter two survive as optional
modules with one named admission each).

---

## 1. Foundation decisions D1–D11 (final text for `PassShelatChapter2-4Plan.md`)

D1. **Base and branch.** Branch `cryptography/pass-shelat-ch2-4` from `cryptography/garg-ch1-3`;
    worktree `/Users/dehmelf/Research/tcslib-pass-shelat`. Verification by shell
    `lake build <module>` / `lake env lean <file>` (user-approved deviation from `AGENTS.md`),
    one Lean process at a time.

D2. **Two layers, as in the Garg plan.** Concrete reductions are reused verbatim from
    `TCSlib/Cryptography/{Foundations,OneWayFunctions,HardcoreBit,Pseudorandom}`; the
    asymptotic layer adds machines, negligible functions and closure. Every asymptotic theorem
    is proved as (i) instantiate the concrete reduction at each `n`, (ii) exhibit the reduction
    as a `Complexity.NUPPT` by `NUPPT.ofPolyTime` of a function obtained from the FP calculus of
    `ClassNP/PolyTimePairing.lean` with `NUPPT.polyTimeComputable_output` as a black box, plus
    the two new machine lemmas of D11, (iii) negligible-function arithmetic through
    `not_negligible_iff`. New concrete lemmas go into campaign-owned files, never into the
    frozen Garg files. *Exception* (gate 03a, ruling G3-7a, user 2026-11-05): the general
    helper `negligible_zero` moved from `Asymptotic/Ensembles.lean` into
    `Foundations/Negligible.lean`, full name `TCSlib.Cryptography.negligible_zero` unchanged; its
    copy `negligible_const_zero` (`ZeroKnowledge/Defs.lean`) is left to the duplicate clean-up
    (ruling G3-5).

D3. **Probabilistic machines.** One structure `Complexity.NUPPT` (file
    `TCSlib/Complexity/Randomized/PPT.lean`): a `Turing.FinTM Bool` that halts on **every** input
    `z` within `Ct * (|z| + 1) ^ ct` steps, an explicit coin polynomial `coins : PolyExpr`, an
    advice polynomial `adv : PolyExpr` and an advice function. The single semantic primitive is
    `output z` (the output tape when the budget expires); `output` is `PolyTimeComputable`
    (proved) and every `PolyTimeComputable` function gives an `NUPPT` (`ofPolyTime`, proved).
    A PPT ([PS10, Def 23.4]) is an `NUPPT` with empty advice (`Uniform`; `Complexity.PPT` is the
    subtype). The activation at security parameter `n` on argument `y` with coins `r` is
    `runAt n y r := output ⟨⟨⟨1^n, y⟩, advice n⟩, r⟩` with `r : Fin (coins.eval n) → Bool`; the
    random tape is part of the input, the time bound holds for every coin string
    ([PS10, Def 23.5], worst case), and "`A` computes `f` with probability 1" ([PS10, Def 24.6])
    is `Computes`: equality for every coin string. `Computes` does not require `Uniform`: Def
    24.6 proper is the case `A.Uniform ∧ A.Computes f`; for a non-uniform `A` it is the advice
    analogue and holds for uncomputable `f` (advice `[h n]`), so `∃ A, A.Computes f` is not "a
    PPT computes `f`" (gate 03a, finding 1). Honest evaluators ("easy to compute") are
    stated as `PolyTimeComputable` string functions on `⟨1^n, x⟩`. Recorded deviations:
    totality on all inputs (behaviour class unchanged: a machine polynomial-time on well-formed
    inputs is clocked by `timed_universal`; the optional lemma `NUPPT.ofPartial` is not needed
    by any theorem); time measured in the machine-input length (a polynomial in `n + |y|`,
    so the classes coincide); advice and coins indexed by the parameter `n` read from `1^n`
    rather than by the input length (interdefinable in every experiment of the text, and what
    makes one random tape per `n` well-typed for the oracle and interactive layouts).

D4. **Non-uniform PPT** ([PS10, Def 26.8]) in the advice formulation: `advice n` of length
    `≤ adv.eval n`, run on `⟨⟨⟨1^n, y⟩, advice n⟩, r⟩`. The input-length-indexed activation
    `A_{|y|}(y)` of the text is `runLit y r := runAt |y| y r` (the prefix `1^{|y|}` carries no
    information); it is the layout of the literal forms of Def 26.1 and Def 69.4 (D5, D6). The
    machine-sequence formulation (`NUPPTSeq`, with `CodeTM.serialize` size) is an **optional**
    corollary module (`Randomized/Sequence.lean`) with the equivalence
    `nuppt_seq_iff_advice` as one named, non-blocking admission; it is not formalized in the
    core (Deviation recorded in the docstring of `NUPPT`).

D5. **Domains are typed at each parameter.** A function family is
    `FunFamily := ⟨inLen outLen : PolyExpr, f n : (Fin (inLen.eval n) → Bool) → (Fin (outLen.eval n) → Bool)⟩`;
    the textbook `f : {0,1}* → {0,1}*` is `FunFamily.ofString f p` (`inLen = var`; exact for
    length-regular `f`, `ofFn_ofString_f`, otherwise the `false`-padding is lossy). An
    inverter's output is decoded by `decodeFin` as an `inLen n`-bit string and a wrong length is
    a failure (`invProbOpt`, bridged to the concrete `invProb` by `invProbOpt_le_invProb` and
    `invProbOpt_some`). Adversaries receive `1^n` exactly where the text gives it
    (Defs 27.3, 28.4, 75.2, 96.1, …); where the text withholds it (Def 26.1: `A(f(x))`;
    Def 69.4: `D(t)`) the frozen definition is the literal one (`WorstCaseOneWay` with
    `inverterLit`, `Ensemble.IndistLit`), and the `1^n` form (`Ensemble.Indist`) is the headline
    form of the theorems, related by `Indist.toLit` (always) and `IndistLit.toIndist`
    (injective `ℓ`, i.e. every ensemble of the text; for constant `ℓ` the two forms coincide
    as well, by point tests, which is not formalized: gate 03a, note 14). The two are never
    unified silently.

D6. **Ensembles** ([PS10, Def 69.3]) are `Ensemble ℓ := ⟨σ : ℕ → Type, Fintype, X n : σ n → (Fin (ℓ.eval n) → Bool)⟩`
    with arbitrary finite seed types (the uniform ensemble has seeds `Fin (ℓ n) → Bool`, the
    random-function oracle has function tables). "Efficiently samplable" is the predicate
    `Samplable` at the **distribution level**: a polynomial-time sampler from `s.eval n` uniform
    bits whose output law equals `X n` (`StatClose … 0`). Lemma 71.5 is `Indist.push` (image
    under an `NUPPT`, padded to an explicit `ℓ' : PolyExpr`), the multicopy corollary
    `Indist.copies` takes `Samplable X`, `Samplable Y`, and the hybrid lemma is the concrete
    `exists_hybrid_gap`. Deviation: every samplable distribution is dyadic; non-dyadic
    distributions of the text (primes, `Z_q`, permutations) appear only as *ideal* distributions
    in experiments and are approximated by rejection samplers within `StatClose` error (D10).

D7. **Oracle adversaries** ([PS10, Def 96.1]) are next-query machines: an `NUPPT` activated once
    per query on the encoded history of (query, answer) pairs with one random tape per `n`, and
    an explicit query budget `q : PolyExpr` quantified universally in the definition
    (`∀ D q`); `NUPPT.toOracleAdversary n ℓ₁ ℓ₂ (q.eval n)` builds the concrete `QueryTree`
    (`OracleAdversary`), `toOracleAdversary_boundedBy` supplies `BoundedBy q` for
    `ggm_prfAdv_le`/`exists_ggmBits_dist`. No oracle tapes (the library's `OracleTM` is a
    language oracle); the bridge `exists_queryTree` from `OracleTM`-level machines is an optional
    module. Deviation recorded.

D8. **Interactive protocols** ([PS10, §4.4]). A `Strategy` is a next-message function
    `next x z r received` with an explicit random-tape polynomial `coins : PolyExpr`; its value
    on the complete history is the party's output. A `Protocol` is `⟨P, V, rounds, verifierFirst⟩`
    where `rounds : PolyExpr` is the number of messages exchanged and `verifierFirst` the first
    mover (GNI: verifier; GI, 3COL: prover). `exec` is the fixed alternation of
    `rounds.eval |x|` moves; the verifier's verdict is `V.next` on the complete history
    (`outV`), so it is always defined and the literal `out_V = 0` is `outV = [false]`.
    `Strategy.Efficient` = one activation of a uniform `NUPPT` at parameter `|x|` on
    `⟨⟨x, z⟩, messages⟩` with the whole random tape (time polynomial in the total input,
    Deviation from the text's `t(|x|)`). Soundness quantifies `∃ ε` before `∀ x ∉ L ∀ P' ∀ z`
    over arbitrary strategies `P'` (unbounded provers; polynomial coin tapes lose nothing by
    averaging). Zero knowledge: `∀ V* efficient, ∃ S uniform NUPPT, ∀ Lz D, ∃ ε, ∀ x y z`,
    `R x y → |z| ≤ Lz.eval |x| → distAdv ≤ ε |x|` — strict PPT simulators, auxiliary inputs
    bounded by an arbitrary polynomial quantified after the simulator (the class a `t(|x|)`-time
    verifier can read; required for the non-uniform reduction of Prop 128.8). Statistical ZK
    (`StatZK δ`, sup-over-test-sets `StatClose`), `PerfectZK := StatZK 0` and Goldreich's abort
    form `PerfectZKAbort` are stated; GI and 3COL are proved statistically (truncated
    simulators, rejection-sampled permutations). Deviations: fixed number of moves (a halting
    party is modelled as sending `[]`; all protocols of the text are fixed-round), strict
    simulators, statistical instead of perfect ZK, `|z|` polynomially bounded.

D9. **Lengths are syntax.** Every length or budget that depends on the parameter (coins,
    advice, input/output lengths of families and ensembles, stretch, query budgets, rounds,
    auxiliary-input bounds) is a `Complexity.PolyExpr` (`const/var/add/mul/pow`, `eval`,
    `subst`, `eval_subst`, `eval_mono`, `eval_le`, `normal C c = C(n+1)^c`). Time bounds of
    machines stay in the normal form `Ct (n+1)^ct` (the shape of `PolyTimeComputable`).
    `polyTimeComputable_unaryPoly p : x ↦ 1^{p(|x|)}` is proved by induction with the new
    primitive `computesFunInTime_unaryMul`, never through the repetition lemma. Abstract
    `ℕ → ℕ` lengths appear only as hypotheses of theorems with a `PolyExpr` majorant
    (`exists_reparam_advice`), never in a definition.

D10. **Sampling device.** `TCSlib/Cryptography/Asymptotic/Sampling.lean` owns
    `StatClose` (with `distAdv_le_of_statClose`, `StatClose.prod`, `StatClose.map`),
    `rejectionSample m k T` (`T` trials of `k` bits; uniform on `Fin m` conditioned on `some`,
    failure `(1 - m/2^k)^T`) and `permFromCoins` (Fisher–Yates with rejection-sampled offsets).
    Experiments use ideal uniform distributions (as the text); honest parties and reductions
    sample by rejection with `2^{-n}`-close laws and the theorems carry the explicit
    statistical term. This one device serves Theorem 35.1's uniform position (`m = 2nq(n)` is
    kept literal), SamplePrime/`Z_q`/`Z_N^*`/`QR_N` (Q3), and Chapter 4's permutations, edges
    and colour permutations (DQ1 option A at the concrete level).

D11. **Admissions policy.** `Complexity.polyTimeComputable_iterateFind`
    (`Randomized/Repetition.lean`) is the single machine lemma that may remain admitted at the
    end of run 4; every theorem that repeats an adversary depends on it and on nothing else
    admitted. The two new primitives (`pairSplitAt`, `unaryMul`) are built in the `Build/`
    style in the campaign-owned `Randomized/Primitives.lean`. `NUPPTSeq`'s equivalence,
    `NUPPT.ofPartial` and `exists_queryTree` are optional modules, each with its own named
    admission, off every critical path. Number-theoretic machine facts (binary `mul`,
    `add`, `sub`, `divMod`, `xgcd`, `modExp`, comparison, bit length, primality; run-3
    audit P7-1 added `add`/`sub`/bit length) are explicit hypotheses
    (`Candidates/Arithmetic.lean` bundle), never axioms; `#print axioms` of every headline must
    show `[propext, Classical.choice, Quot.sound]` plus, at most, the admissions named here.
    *Status* (gate 03a, note 20; decision log 2026-10-28): run 3b proved
    `polyTimeComputable_iterateFind`, so the permitted machine admission is unused.
    `NUPPT.ofPartial` was never written; the only machine-layer `sorry` is the optional bridge
    `NUPPT.decides_of_decidesWithAdviceInTime` (`Randomized/NonUniform.lean`), whose sketch does
    `ofPartial`'s clocking inline. It is the named admission of that optional module (open
    question 5, ruled outside the core on 2026-10-27).

---

## 2. Frozen Lean signatures

All code below is verbatim from `DESIGN-freeze-scratch.lean` (compiled). Namespaces:
`Complexity` for the machine layer (`open Turing`), `TCSlib.Cryptography` for everything
else (`open Complexity Turing`). Each file's `## References` lists `[PS10]`, `[Gar26]`, `[AB09]`.
Docstrings in the skeleton must begin with the natural-language statement, then the
`[PS10, …]` citation, then the Deviation notes quoted in §5.

### 2.1 `TCSlib/Complexity/Randomized/PolyExpr.lean`

```lean
namespace Complexity

inductive PolyExpr : Type
  | const : ℕ → PolyExpr
  | var : PolyExpr
  | add : PolyExpr → PolyExpr → PolyExpr
  | mul : PolyExpr → PolyExpr → PolyExpr
  | pow : PolyExpr → ℕ → PolyExpr
  deriving DecidableEq, Repr

namespace PolyExpr
def eval : PolyExpr → ℕ → ℕ                       -- structural
def subst : PolyExpr → PolyExpr → PolyExpr          -- p[q/n]
def normal (C c : ℕ) : PolyExpr := mul (const C) (pow (add var (const 1)) c)
@[simp] theorem eval_const (c n : ℕ) : (const c).eval n = c := rfl       -- likewise eval_var/add/mul/pow
theorem eval_normal (C c n : ℕ) : (normal C c).eval n = C * (n + 1) ^ c := rfl
theorem eval_subst (p q : PolyExpr) (n : ℕ) : (p.subst q).eval n = p.eval (q.eval n)   -- proved
theorem eval_mono (p : PolyExpr) : Monotone p.eval                                       -- proved
theorem eval_le (p : PolyExpr) : ∃ C c : ℕ, ∀ n, p.eval n ≤ C * (n + 1) ^ c               -- proved
end PolyExpr

/-- `1^{p(|x|)}` is polynomial-time computable. Proof: induction on `p`; `const` =
`polyTimeComputable_const`, `var` = `polyTimeComputable_unary`, `add` = `PolyTimeComputable.append`,
`mul` = `computesFunInTime_unaryMul` (§2.4) composed with `PolyTimeComputable.pairEncode` of the
two unary strings, `pow p c` = induction on `c` through `mul`. -/
theorem polyTimeComputable_unaryPoly (p : PolyExpr) :
    PolyTimeComputable fun x => List.replicate (p.eval x.length) true
end Complexity
```

### 2.2 `TCSlib/Complexity/Randomized/PPT.lean` — the structure and its primitive

```lean
namespace Complexity
open Turing

/-- NUPPT [PS10, Def 26.8, advice formulation]; PPT [PS10, Def 23.4] = `Uniform`. -/
structure NUPPT where
  M : FinTM Bool
  Ct : ℕ
  ct : ℕ                                  -- M halts within Ct (|z|+1)^ct on EVERY input z
  coins : PolyExpr                        -- coins.eval n uniform coins at parameter n
  adv : PolyExpr                          -- |advice n| ≤ adv.eval n
  advice : ℕ → List Bool
  advice_length : ∀ n, (advice n).length ≤ adv.eval n
  halts : ∀ z : List Bool, ∃ out : List Bool, M.ComputesInTime z out (Ct * (z.length + 1) ^ ct)

namespace NUPPT
variable (A : NUPPT)
def timeBound (m : ℕ) : ℕ := A.Ct * (m + 1) ^ A.ct
def coinLen (n : ℕ) : ℕ := A.coins.eval n
def adviceLen (n : ℕ) : ℕ := A.adv.eval n
def output (z : List Bool) : List Bool :=
  (A.M.tm.runFrom (A.M.tm.initCfg z) (A.timeBound z.length)).output
theorem output_spec (z) : A.M.ComputesInTime z (A.output z) (A.timeBound z.length)      -- proved
theorem computesFunInTime : A.M.ComputesFunInTime A.output A.timeBound                   -- proved
theorem polyTimeComputable_output : PolyTimeComputable A.output                          -- proved
theorem output_eq_of_computesInTime {z w t} (h : A.M.ComputesInTime z w t) : A.output z = w  -- proved
def advInput (n : ℕ) (y : List Bool) : List Bool := pairEncode (List.replicate n true) y   -- ⟨1^n, y⟩
theorem length_advInput (n y) : (advInput n y).length = 2 * n + 2 + y.length                -- proved
abbrev Coins (n : ℕ) : Type := Fin (A.coinLen n) → Bool
def runAt (n : ℕ) (y : List Bool) (r : A.Coins n) : List Bool :=
  A.output (pairEncode (pairEncode (advInput n y) (A.advice n)) (List.ofFn r))
def runAtL (n : ℕ) (y r : List Bool) : List Bool :=
  A.output (pairEncode (pairEncode (advInput n y) (A.advice n)) r)
theorem runAt_eq (n y r) : A.runAt n y r = A.runAtL n y (List.ofFn r) := rfl
/-- `A_{|y|}(y)` of [PS10, Def 26.8]: activation at the input length. -/
def runLit (y : List Bool) (r : A.Coins y.length) : List Bool := A.runAt y.length y r
def Uniform : Prop := ∀ n, A.advice n = []
/-- [PS10, Def 24.6]. -/
def Computes (f : List Bool → List Bool) : Prop := ∀ n y (r : A.Coins n), A.runAt n y r = f (advInput n y)
noncomputable def ofPolyTime {f} (hf : PolyTimeComputable f) (coins adv : PolyExpr)
    (advice : ℕ → List Bool) (hα : ∀ n, (advice n).length ≤ adv.eval n) : NUPPT
theorem output_ofPolyTime … : (ofPolyTime hf coins adv advice hα).output = f                -- proved
noncomputable def ofPolyTimeUniform {f} (hf : PolyTimeComputable f) (coins : PolyExpr) : NUPPT
theorem ofPolyTimeUniform_uniform … : (ofPolyTimeUniform hf coins).Uniform                  -- proved
end NUPPT

def PPT : Type 1 := {A : NUPPT // A.Uniform}
theorem NUPPT.nonempty : Nonempty NUPPT                                                       -- proved
end Complexity
```

### 2.3 `TCSlib/Complexity/Randomized/NonUniform.lean` — Def 26.8 material

Contents: the docstring of Def 26.8 (both formulations, the advice one frozen), `runLit` lemmas
(`runLit_eq_runAt`), `Uniform` lemmas (`ofPolyTime` with empty advice; `Uniform.advice_eq`),
the sanity bridge to the library's advice machines, and the optional `NUPPTSeq`:

```lean
/-- Optional sanity bridge (needs the clocking construction `NUPPT.ofPartial`; off the
critical path). -/
theorem NUPPT.decides_of_decidesWithAdviceInTime (M : FinTM Bool) (L : Language Bool)
    (α : ℕ → List Bool) (C c Ca ca : ℕ) (hα : ∀ n, (α n).length = Ca * (n + 1) ^ ca)
    (h : M.DecidesWithAdviceInTime L α (fun n => C * (n + 1) ^ c)) :
    ∃ A : NUPPT, ∀ x (r : A.Coins x.length),
      A.runAt x.length x r = [MultiTapeTM.indicator (L : Set (List Bool)) x]
```

Optional module `Randomized/Sequence.lean` (owner: machine-core, deferred): `NUPPTSeq`
(FAITHFUL §2.1 verbatim with `CodeTM.serialize`) and `nuppt_seq_iff_advice` (⇒ conditional on
`PolyBound c.canonizerTime` as in `TMSAT_mem_NP`; ⇐ via the hard-wiring construction), one
named admission; no theorem of chapters 2–4 depends on it.

### 2.4 `TCSlib/Complexity/Randomized/Primitives.lean` — two new machines

```lean
namespace Turing.FinTM
/-- NEW: `⟨u, b⟩ ↦ ⟨b.take |u|, b.drop |u|⟩` (coin splitting at a unary length). -/
theorem computesFunInTime_pairSplitAt :
    ∃ (M : FinTM Bool) (c : ℕ), M.ComputesFunInTime
      (fun z => match pairDecode z with
        | some (u, b) => pairEncode (b.take u.length) (b.drop u.length) | none => [])
      fun n => c * (n + 1)
/-- NEW: unary multiplication `⟨1^a, 1^b⟩ ↦ 1^{a·b}`. -/
theorem computesFunInTime_unaryMul :
    ∃ (M : FinTM Bool) (c : ℕ), M.ComputesFunInTime
      (fun z => match pairDecode z with
        | some (u, v) => List.replicate (u.length * v.length) true | none => [])
      fun n => c * (n + 1) ^ 2
end Turing.FinTM

theorem Complexity.polyTimeComputable_pairTakePoly (p : PolyExpr) :
    PolyTimeComputable fun z => (pairSndD z).take (p.eval (pairFstD z).length)
theorem Complexity.polyTimeComputable_pairDropPoly (p : PolyExpr) :
    PolyTimeComputable fun z => (pairSndD z).drop (p.eval (pairFstD z).length)
```

Construction sketches. `pairSplitAt`: the buffered aligned parser of `computesFunInTime_pairFst`
(reads the doubled prefix `u` onto a work tape without emitting), then a copy scan of `b` that
emits the doubled bit `bb` while the work head walks across `u`, then the separator `01`, then
the remainder verbatim; linear, two work tapes (≈ 300–500 lines). `unaryMul`: copy `1^b` onto a
work tape (the parser of `pairSnd`), then for each token of `u` replay the work tape onto the
output (`emitAction`-style) and rewind; `O(ab + a + b)` steps, ≈ 300–500 lines. Fallback for
`unaryMul` only: an instance of `polyTimeComputable_iterateEmit` (state `⟨1^{rest}, 1^b⟩`,
`emit = pairSndD`, step pops one token) — acceptable only after `iterateFind` is closed.
`pairTakePoly p` = `pairFstD ∘ pairSplitAt ∘ pairEncode (unaryPoly p ∘ pairFstD) pairSndD`
by `polyTimeComputable_of_linear`, `PolyTimeComputable.pairEncode`, `.comp`.

### 2.5 `TCSlib/Complexity/Randomized/Closure.lean` — closure catalogue

Every lemma is `NUPPT.ofPolyTime` of an FP function built from
`A.polyTimeComputable_output`, `PolyTimeComputable.comp/.pairEncode/.append`,
`polyTimeComputable_const/_prepend/_unary/_pairFstD/_pairSndD/_iterate_pairFstD/_pairConcat/_pairSwap/_ite/_and/_lenLe/_lenEq`,
`polyTimeComputable_unaryPoly` and `pairTakePoly/DropPoly`; the equation is `output_ofPolyTime`
+ `pairDecode_pairEncode` + `funext`. `Uniform` is preserved whenever the advice is `A.advice`
or `[]`.

```lean
theorem NUPPT.exists_comp (A : NUPPT) {pre post} (hpre : PolyTimeComputable pre) (hpost : PolyTimeComputable post) :
    ∃ B : NUPPT, B.coins = A.coins ∧ B.adv = A.adv ∧ B.advice = A.advice ∧
      ∀ n y r, B.runAtL n y r = post (A.runAtL n (pre y) r)
theorem NUPPT.exists_reparam (A : NUPPT) (p : PolyExpr) :                        -- n ↦ p(n), uniform
    ∃ B : NUPPT, B.coins = A.coins.subst p ∧ (A.Uniform → B.Uniform) ∧
      ∀ n y r, B.runAtL n y r = A.runAtL (p.eval n) y r
theorem NUPPT.exists_reparam_advice (A : NUPPT) (φ : ℕ → ℕ) (p : PolyExpr) (hφ : ∀ n, φ n ≤ p.eval n) :
    ∃ B : NUPPT, B.coins = A.coins.subst p ∧
      ∀ n y r, B.runAtL n y r = A.runAtL (φ n) y (r.take (A.coinLen (φ n)))      -- 1^{φ n}, advice (φ n) hard-wired
theorem NUPPT.exists_withAdvice (A : NUPPT) (β : ℕ → List Bool) (b : PolyExpr) (hβ : ∀ n, (β n).length ≤ b.eval n) :
    ∃ B : NUPPT, B.coins = A.coins ∧ ∀ n y r, B.runAtL n y r = A.runAtL n (pairEncode y (β n)) r
theorem NUPPT.exists_split (A : NUPPT) (p : PolyExpr) :                          -- extra coins as data
    ∃ B : NUPPT, B.coins = .add p A.coins ∧ B.advice = A.advice ∧
      ∀ n y r, B.runAtL n y r = A.runAtL n (pairEncode y (r.take (p.eval n))) (r.drop (p.eval n))
theorem NUPPT.exists_seq (A B : NUPPT) :                                          -- sunglass composition
    ∃ C : NUPPT, C.coins = .add A.coins B.coins ∧ (A.Uniform → B.Uniform → C.Uniform) ∧
      ∀ n y r, C.runAtL n y r =
        B.runAtL n (pairEncode y (A.runAtL n y (r.take (A.coinLen n)))) (r.drop (A.coinLen n))
```

| Lemma | Raw function on `⟨⟨⟨1^n, y⟩, α⟩, r⟩` | Supplier |
| --- | --- | --- |
| `exists_comp` | re-pair with `pre y`, apply `A.output`, apply `post` | `pairFstD`, `pairSndD`, `pairEncode`, `comp`, `A.polyTimeComputable_output` |
| `exists_reparam p` | advice `A.advice (p n)` (length `A.adv.subst p` by `eval_subst`); machine replaces `1^n` by `1^{p n}` (`unaryPoly p` on `pairFstD (pairFstD (pairFstD z))`) and re-pairs | `unaryPoly`, `pairEncode`, `comp` |
| `exists_reparam_advice φ p` | advice `⟨1^{φ n}, A.advice (φ n)⟩` (length `2p+2+A.adv.subst p`); coins `A.coins.subst p ≥ A.coins.eval (φ n)` (`eval_mono`); the machine cuts `1^{A.coins.eval (φ n)}` coins (`unaryPoly A.coins` on the advice's `1^{φ n}`, then `pairSplitAt`) | `pairSplitAt`, `unaryPoly`, `eval_mono` |
| `exists_withAdvice` | advice `⟨A.advice n, β n⟩`, length `2·A.adv + 2 + b`; re-pair `y` with `β n` | pairing calculus |
| `exists_split p` | cut `r` at `1^{p n}`; pass the head as data | `pairTakePoly p`, `pairDropPoly p` |
| `exists_seq` | cut at `1^{A.coinLen n}`; run `A.output` on the first part, then `B.output` on `⟨⟨⟨1^n, ⟨y, a⟩⟩, α_B⟩, r₂⟩`; advice `⟨α_A, α_B⟩` | both outputs, `pairTakePoly/DropPoly`, pairing |
| negation / `[true]` normalisation | `computesFunInTime_ifEq` via `exists_comp` | Composition.lean |
| branching | FP-level `polyTimeComputable_ite`, `computesFunInTime_cond` | PolyTimePairing, Build/Wrappers |
| length tests | `polyTimeComputable_lenEq/_lenLe` | PolyTimePairing |
| loop fuel | `computesFunInTime_polyBits` (normal form) and `unaryPoly` + `computesFunInTime_lengthBits` (general `PolyExpr`) | Build/Primitives |

### 2.6 `TCSlib/Complexity/Randomized/Repetition.lean` — the load-bearing lemma, repaired

```lean
theorem polyTimeComputable_iterateFind {g} (hg : PolyTimeComputable g)
    {acc : List Bool → Bool} (hacc : PolyTimeComputable fun s => [acc s])
    {out} (hout : PolyTimeComputable out) (R P : PolyExpr)
    (horbit : ∀ x i, i ≤ R.eval x.length → (g^[i] x).length ≤ P.eval x.length) :
    PolyTimeComputable fun x =>
      match (List.range (R.eval x.length + 1)).find? (fun i => acc (g^[i] x)) with
      | some i => out (g^[i] x) | none => []
theorem polyTimeComputable_iterate {g} (hg) (R P) (horbit) : PolyTimeComputable fun x => g^[R.eval x.length] x
theorem polyTimeComputable_iterateEmit {g emit} (hg) (hemit) (R P) (horbit) :
    PolyTimeComputable fun x => (List.range (R.eval x.length + 1)).flatMap fun i => emit (g^[i] x)
theorem polyTimeComputable_majority : PolyTimeComputable fun w => [decide (w.length < 2 * w.count true)]
theorem polyTimeComputable_pairXor : PolyTimeComputable fun z => List.zipWith xor (pairFstD z) (pairSndD z)
theorem polyTimeComputable_pairEq : PolyTimeComputable fun z => [decide (pairFstD z = pairSndD z)]
theorem polyTimeComputable_blockMap (b : PolyExpr) {g} (hg) :
    PolyTimeComputable fun z => (List.range ((pairSndD z).length / b.eval (pairFstD z).length)).flatMap fun i =>
      g (((pairSndD z).drop (i * b.eval (pairFstD z).length)).take (b.eval (pairFstD z).length))
```

**Construction of `iterateFind` (instance of `exists_loopFindTM`, Loop.lean:2633), with the
three panel repairs built in.**

1. *State word carries the input.* `s0 x := pairEncode x x` (the second component is the
   current orbit point). Loop data: `stepF x w := if |pairSndD w| ≤ P|x| then pairEncode x (g (pairSndD w)) else w`
   (**length-guarded**), `acceptF x w := acc (pairSndD w)`, `out x w := out (pairSndD w)`,
   `Inv x w := pairFstD w = x ∧ (pairSndD w).length ≤ P.eval x.length`. `hInv0` is
   `pairDecode_pairEncode`; `hInvStep` holds because the guard fixes the state once the bound
   is exceeded and otherwise `|g s| ≤ …` is **not** needed: the guarded step keeps the second
   component unchanged when it is already too long, so `Inv` is closed under `stepF` for every
   `w` (refutation J1-7/J2-15/J3-5). On the orbit `i ≤ R|x|`, `horbit` shows the guard is never
   taken, so `(stepF x)^[i] (s0 x) = pairEncode x (g^[i] x)` and the `find?` of the conclusion
   is the statement's (a 40-line pure lemma `iterate_guard_eq`).
2. *Modules.* From `hg`, `hacc`, `hout` build three clean-call modules over the state word:
   `C₁ := exists_installCallTM` for `w ↦ pairEncode [acc (pairSndD w)] w` (verdict as the first
   cell of the installed word: `pairEncode [b] w = [b, b, false, true] ++ w`, no scan needed),
   `C₂ := exists_installCallTM` for `w ↦ stepF' (pairSndD w)` where `stepF'` is the guarded step
   on the pair (FP: `polyTimeComputable_ite` with `polyTimeComputable_lenLe` on
   `⟨pairSndD w, 1^{P|pairFstD w|}⟩` by `unaryPoly P ∘ pairFstD`), `C₃ := exists_emitCallTM` for
   `w ↦ out (pairSndD (pairSndD w))`. Each module promises first-visit-to-exit from the clean
   seam over an arbitrary native input (Loop.lean:5645/5691) and `0 < C.k`.
3. *Gluing without overriding `exit`.* Body state `Unit ⊕ (C₁.State ⊕ C₂.State ⊕ C₃.State) ⊕ Fin 3`;
   the tape counts are equalised with idle tapes (`leftAction`/`leftCfg_run`, Simulation.lean).
   **The anchor is the fresh state `inl ()`** whose transition is stationary into `C₁.entry`
   (refutation J2-16/J3-6: no module-internal state is the anchor). The module tables are
   copied with every transition *targeting* `Cᵢ.exit` **redirected** to a fresh branch state
   (`inr (inr k)`), so the module's own table at `exit` is never consulted and the case
   `entry = exit` is harmless: the first positive visit of `exit` promised by the contract is
   exactly the first entry into the branch state, with the clean seam on the tapes. Branch
   states: after `C₁`, read tape-0 cell 0 — `true` → `C₃.entry`, `false` → `C₂.entry`; after
   `C₂` → anchor (one stationary step); after `C₃` → halt.
4. *`hstart`.* From `initCfg x`, install `s0 x = pairEncode x x` on tape 0: this is one more
   `exists_installCallTM` module for `pairDup` (`computesFunInTime_pairDup`) applied to the
   argument word `x` itself, which must first be on tape 0: a one-state copy scan of the native
   input onto tape 0 plus `timed_rewind` (≈ 100 lines; precedent: the startup phases of
   `computesFunInTime_splitSolveWith`). No anchor visit before the seam.
5. *`hround`.* From `Cfg.ofWords anchor (stateWord K w)` with `Inv x w`: one step into
   `C₁.entry`; `C₁` to its first exit (`t₁ ≤ c₁ (T_acc(|w|) + 2|w| + 5)`), branch; accepting
   clause: `C₃` to its first exit emitting `out (pairSndD w)` and halt; advancing clause: `C₂`
   to its first exit installing `stepF x w`, one step to the anchor. Anchor exclusion inside
   the round is syntactic (the anchor is `inl ()`, entered only from the post-`C₂` branch
   state). Budget `T n := c (T_g(Q n) + T_acc(Q n) + T_out(Q n) + Q n + 8)` with
   `Q n := 2 n + 2 + P.eval n + 4` (length of the state word), a normal-form majorant by
   `eval_le`.
6. *Fuel.* `hF` from `computesFunInTime_polyBits` for a normal-form majorant of `R`, or
   `unaryPoly R` + `computesFunInTime_lengthBits` for exact `R` (the `find?` range must be
   exactly `R|x| + 1`: use the exact form).
7. *Conclusion.* `exists_loopFindTM` gives `E` within `c (T n + 1)(R n + 2)`; package as
   `PolyTimeComputable`. `iterate` threads a unary counter in the state
   (`acc := lenEq cnt 1^{R|x|}` against `unaryPoly R` of the retained input);
   `iterateEmit` threads an accumulator; the derived string functions are instances
   (REUSE-MAX §7.4, unchanged).

Estimated size 1 200–1 800 lines; private precedent for the module gluing: `satClean_install`,
`satStopTM`, `sat_run_agree` in `ClassNP/SAT.lean` (private copies, not edits). If the lemma is
not closed in run 4 it is the single named admission of D11.

### 2.7 `TCSlib/Cryptography/Asymptotic/Sampling.lean`

```lean
def StatClose {σ τ γ} [Fintype σ] [Fintype τ] (X : σ → γ) (Y : τ → γ) (δ : ℝ) : Prop :=
  ∀ T : γ → Prop, |uprob (fun s => T (X s)) - uprob (fun t => T (Y t))| ≤ δ
theorem distAdv_le_of_statClose … (h : StatClose X Y δ) (D : γ → ρ → Bool) : distAdv X Y D ≤ δ
theorem StatClose.prod … (h : StatClose X X' δ) (h' : StatClose Y Y' δ') :
    StatClose (fun z : σ × σ' => (X z.1, Y z.2)) (fun z : τ × τ' => (X' z.1, Y' z.2)) (δ + δ')
theorem StatClose.map … (h : StatClose X Y δ) (g : γ → γ') : StatClose (fun s => g (X s)) (fun t => g (Y t)) δ
def bitsToNat {k : ℕ} (b : Fin k → Bool) : ℕ
def uniformFromBits (m k : ℕ) (b : Fin k → Bool) : Option (Fin m)
def rejectionSample (m k T : ℕ) (b : Fin T → Fin k → Bool) : Option (Fin m)
theorem rejectionSample_uniform_of_some (m k T) (hm : 0 < m) (hk : m ≤ 2 ^ k) (i j : Fin m) :
    uprob (fun b => rejectionSample m k T b = some i) = uprob (fun b => rejectionSample m k T b = some j)
theorem uprob_rejectionSample_none (m k T) (hm) (hk) :
    uprob (fun b => rejectionSample m k T b = none) = (1 - (m : ℝ) / 2 ^ k) ^ T
theorem statClose_rejectionSample (m k T) (hm) (hk) (d : Fin m) :
    StatClose (fun b => (rejectionSample m k T b).getD d) (id : Fin m → Fin m) ((1 - (m : ℝ) / 2 ^ k) ^ T)
```

**Run-3 repair (audit P2-1, pack P2).** `uprob_permFromCoins_none_le` is stated with the
provable bound `n * (1 - 1/2^k)^T` (the frozen `n (1/2)^T` is false: the last position has
range `1` and fails with probability `(1 - 1/2^k)^T`). The permutation section moved to
`Asymptotic/Permutations.lean` (file-size limit), which also owns the campaign parameters and
the closed form:
```lean
def permBits (n : ℕ) : ℕ := Nat.size n            -- n ≤ 2^k ≤ 2n
def permTrials (n : ℕ) : ℕ := 2 * n * n
theorem statClose_permFromCoins (n k T) (hk : n ≤ 2 ^ k) (d : Equiv.Perm (Fin n)) :
    StatClose (fun b => (permFromCoins n k T b).getD d) id (n * (1 - 1 / 2 ^ k : ℝ) ^ T)
theorem uprob_permFromCoins_none_le_two_pow (n) :
    uprob (fun b => permFromCoins n (permBits n) (permTrials n) b = none) ≤ n * (2 : ℝ)⁻¹ ^ n
theorem statClose_permFromCoins_two_pow (n) (d) :
    StatClose (fun b => (permFromCoins n (permBits n) (permTrials n) b).getD d) id (n * (2 : ℝ)⁻¹ ^ n)
```
with the general `statClose_getD_of_uniform_of_some` (a sampler uniform conditioned on
success, made total by a default, is `StatClose` to uniform within its failure probability),
`StatClose.comp_pushesUniform` and `one_sub_inv_pow_le_half` (`(1 - 1/m)^m ≤ 1/2`, Bernoulli)
in `Sampling.lean`; all proved except `permFromCoins_uniform_of_some` (fill).

Proof sources: `distAdv_le_of_statClose` transposes `abs_sum_sub_le_statDist`'s argument
(average over the distinguisher's coins; each coin string is one test set; `uprob_prod`);
`StatClose.prod` by `uprob_prod` (Fubini) and the triangle inequality; the rejection lemmas by
`uprob_prod` over trials, `OneWay.uprob_pi_forall` for the all-fail event, and the bijection
`bitsToNat : (Fin k → Bool) ≃ Fin (2^k)` (`finFunctionFinEquiv`) for uniformity of one trial.
This file also hosts the ch. 2 concrete lemmas C4 (`first_hit_uniform` = `rejectionSample_uniform_of_some`),
C5 (`pushesUniform_of_card_fiber`) and C10 (statistical switch = `StatClose.map` + `distAdv_le_of_statClose`).

### 2.8 `TCSlib/Cryptography/Asymptotic/Adversary.lean`

```lean
def decodeFin (ℓ : ℕ) (w : List Bool) : Option (Fin ℓ → Bool)       -- wrong length = failure (D5)
def padFin (ℓ : ℕ) (w : List Bool) : Fin ℓ → Bool                   -- pad/truncate (samplers)
def Complexity.NUPPT.inverter (A : NUPPT) (n ℓ m : ℕ) : (Fin m → Bool) → A.Coins n → Option (Fin ℓ → Bool)
def Complexity.NUPPT.inverterLit (A : NUPPT) (ℓ m : ℕ) : (Fin m → Bool) → A.Coins m → Option (Fin ℓ → Bool)
def Complexity.NUPPT.distinguisher (A : NUPPT) (n m : ℕ) : (Fin m → Bool) → A.Coins n → Bool
def Complexity.NUPPT.distinguisherL (A : NUPPT) (n : ℕ) : List Bool → A.Coins n → Bool
def Complexity.NUPPT.predictor (A : NUPPT) (n m : ℕ) : (Fin m → Bool) → A.Coins n → Bool
noncomputable def invProbOpt {α β ρ} [Fintype α] [Fintype ρ] (f : α → β) (A : β → ρ → Option α) : ℝ
theorem invProbOpt_le_invProb [Inhabited α] (f) (A) : invProbOpt f A ≤ invProb f (fun y r => (A y r).getD default)  -- proved
theorem invProbOpt_some (f) (A : β → ρ → α) : invProbOpt f (fun y r => some (A y r)) = invProb f A           -- proved
```

### 2.9 `TCSlib/Cryptography/Asymptotic/OneWay.lean`

```lean
structure FunFamily where
  inLen : PolyExpr
  outLen : PolyExpr
  f : ∀ n, (Fin (inLen.eval n) → Bool) → (Fin (outLen.eval n) → Bool)

namespace FunFamily
def Easy (𝓕 : FunFamily) : Prop :=                                         -- [26.1(1), 27.3(1)]
  ∃ F, PolyTimeComputable F ∧ ∀ n (x : Fin (𝓕.inLen.eval n) → Bool), F (NUPPT.advInput n (List.ofFn x)) = List.ofFn (𝓕.f n x)
noncomputable def invProbAt (𝓕) (A : NUPPT) (n : ℕ) : ℝ := invProbOpt (𝓕.f n) (A.inverter n (𝓕.inLen.eval n) (𝓕.outLen.eval n))
structure StrongOneWay (𝓕 : FunFamily) : Prop where                        -- [PS10, Def 27.3]
  easy : 𝓕.Easy
  hard : ∀ A : NUPPT, Negligible fun n => 𝓕.invProbAt A n
structure WeakOneWay (𝓕 : FunFamily) : Prop where                          -- [PS10, Def 28.4]
  easy : 𝓕.Easy
  hard : ∃ q : PolyExpr, (∀ n, 0 < q.eval n) ∧ ∀ A : NUPPT, ∃ n₀, ∀ n ≥ n₀, 𝓕.invProbAt A n ≤ 1 - 1 / (q.eval n : ℝ)
structure WorstCaseOneWay (𝓕 : FunFamily) : Prop where                     -- [PS10, Def 26.1], 1^n form (headline; run-3 audit P3-2)
  easy : 𝓕.Easy
  hard : ¬ ∃ A : NUPPT, ∀ n (x : Fin (𝓕.inLen.eval n) → Bool),
    uprob (fun r : A.Coins n =>
      ∃ x', A.inverter n (𝓕.inLen.eval n) (𝓕.outLen.eval n) (𝓕.f n x) r = some x' ∧ 𝓕.f n x' = 𝓕.f n x) = 1
structure WorstCaseOneWayLit (𝓕 : FunFamily) : Prop where                  -- [PS10, Def 26.1], literal (A gets f(x) only)
  easy : 𝓕.Easy
  hard : ¬ ∃ A : NUPPT, ∀ n (x : Fin (𝓕.inLen.eval n) → Bool),
    uprob (fun r : A.Coins (𝓕.outLen.eval n) =>
      ∃ x', A.inverterLit (𝓕.inLen.eval n) (𝓕.outLen.eval n) (𝓕.f n x) r = some x' ∧ 𝓕.f n x' = 𝓕.f n x) = 1
theorem FunFamily.WorstCaseOneWay.toLit {𝓕} (h : 𝓕.WorstCaseOneWay) : 𝓕.WorstCaseOneWayLit          -- always (proved)
theorem FunFamily.WorstCaseOneWayLit.toParam {𝓕} (hinj : Function.Injective 𝓕.outLen.eval)
    (h : 𝓕.WorstCaseOneWayLit) : 𝓕.WorstCaseOneWay                                                 -- injective outLen (proved)
def strOutLen (f : List Bool → List Bool) (n : ℕ) : ℕ
def ofString (f : List Bool → List Bool) (p : PolyExpr) : FunFamily        -- inLen = var, outLen = p
def LengthRegular (f) (p : PolyExpr) : Prop := ∀ x, (f x).length = p.eval x.length
def blocks (q ℓ : ℕ) : (Fin (q * ℓ) → Bool) ≃ (Fin q → Fin ℓ → Bool)
def prod (𝓕 : FunFamily) (q : PolyExpr) : FunFamily                        -- inLen = q·inLen, f' = prodFun blockwise
end FunFamily

theorem weak_to_strong {𝓕} (h : FunFamily.WeakOneWay 𝓕) : ∃ q : PolyExpr, FunFamily.StrongOneWay (𝓕.prod q)   -- [35.1]
theorem strong_prod_two {𝓕} (h : FunFamily.StrongOneWay 𝓕) : FunFamily.StrongOneWay (𝓕.prod (.const 2))      -- [35.2]
theorem FunFamily.StrongOneWay.weak {𝓕} (h : 𝓕.StrongOneWay) : 𝓕.WeakOneWay                                   -- sanity
theorem not_strongOneWay_id : ¬ FunFamily.StrongOneWay (FunFamily.ofString id .var)                           -- non-vacuity

structure PermFamily where f : ∀ n, (Fin n → Bool) ≃ (Fin n → Bool)        -- the single OWP of 79.4/126.4
def PermFamily.toFunFamily (P : PermFamily) : FunFamily
def OneWayPermutation (P : PermFamily) : Prop := P.toFunFamily.StrongOneWay
```

Theorem 35.1 plan (REUSE-MAX §3.3 with the sampling repair). `q := mul (const 2) (mul var q_w)`
(the text's `m = 2nq(n)`, literal). The reduction machine `A*` hard-wires in its advice
`⟨A'.advice n, 1^{m n}, 1^{T n}, 1^{inLen n}, 1^{A'.coinLen n}⟩` (all `PolyExpr`, so advice is
optional and the reduction is in fact `Uniform`-preserving) and iterates
(`polyTimeComputable_iterateFind`, `T n := 2 n m(n) n^c` rounds) the step: cut a coin segment
(`pairTakePoly`), sample the position `i` by `rejectionSample (m n) k n` with `k := clog`-free
`k n := m n` bits (`2^{m n} ≥ m n`, failure `≤ 2^{-n}` per trial), evaluate `F` blockwise
(`blockMap inLen`), plant `y` (`blockSelect`), call `A'.output` on the re-paired layout, test
`F ⟨1^n, z_i⟩ = y` (`pairEq`), emit `z_i` (or `0^{inLen n}` on exhaustion so that the machine is
`yaoInverter` *including its default*). Functional identity: `A*.inverter n _ _ y r = some (yaoInverter (𝓕.f n) (B n) (T n) y (coinsEquiv n r))`
on the event that every position trial succeeds, which has probability `≥ 1 − T n · 2^{-n}`;
`StatClose.prod`/`distAdv_le_of_statClose` move `invProb` by at most that. Then
`yao_amplification_exp` with `α' := 1/q_w(n)`, `μ₀ := 1/n^c − T n 2^{-n}`, and
`not_negligible_iff` as in REUSE-MAX steps 8–9.

### 2.10 `TCSlib/Cryptography/Asymptotic/Collections.lean`

```lean
structure Collection where                      -- [PS10, Def 41.1]; Gen(1^n) = ⟨i, t⟩, t ignored by plain collections
  D : List Bool → Type
  [fintypeD : ∀ i, Fintype (D i)]  [inhabitedD : ∀ i, Inhabited (D i)]
  encD : ∀ i, D i → List Bool
  decD : ∀ i, List Bool → Option (D i)
  decD_encD : ∀ i x, decD i (encD i x) = some x
  encD_decD : ∀ i w x, decD i w = some x → encD i x = w                     -- canonical decoding; gate 03b, G3-1
  f : ∀ i, D i → List Bool
  gen : NUPPT     gen_uniform : gen.Uniform
  sample : NUPPT  sample_uniform : sample.Uniform
  eval : List Bool → List Bool   eval_poly : PolyTimeComputable eval
  eval_spec : ∀ i x, eval (pairEncode i (encD i x)) = f i x
  sample_spec : ∀ n (r : gen.Coins n) (s : sample.Coins n), ∃ x,          -- [41.1 (2), membership]; run-3 audit P3-1
    decD (pairFstD (gen.runAt n [] r)) (sample.runAt n (pairFstD (gen.runAt n [] r)) s) = some x ∧
    eval (pairEncode (pairFstD (gen.runAt n [] r)) (sample.runAt n (pairFstD (gen.runAt n [] r)) s)) = f (pairFstD (gen.runAt n [] r)) x
namespace Collection
def index (F) (n) (r : F.gen.Coins n) : List Bool := pairFstD (F.gen.runAt n [] r)
def trap  (F) (n) (r : F.gen.Coins n) : List Bool := pairSndD (F.gen.runAt n [] r)
def SampleClose (F) (δ : ℕ → ℝ) : Prop := ∀ n r, StatClose (fun s : F.sample.Coins n => F.decD (F.index n r) (F.sample.runAt n (F.index n r) s)) (fun x : F.D (F.index n r) => some x) (δ n)
noncomputable def invProbAt (F) (A : NUPPT) (n) : ℝ :=        -- i ← Gen; x ← D_i uniform (ideal); uexp over Gen's coins
  uexp fun r : F.gen.Coins n => uprob fun z : F.D (F.index n r) × A.Coins n =>
    ∃ x', F.decD _ (A.runAt n (pairEncode (F.index n r) (F.f _ z.1)) z.2) = some x' ∧ F.f _ x' = F.f _ z.1
structure OneWay (F : Collection) : Prop where
  sampleClose : ∃ δ, Negligible δ ∧ F.SampleClose δ
  hard : ∀ A : NUPPT, Negligible fun n => F.invProbAt A n
def HardCore (F : Collection) (h : ∀ i, F.D i → Bool) : Prop := …          -- Def 78.3 for collections (uexp/uprob form)
end Collection
structure PermCollection extends Collection where perm : ∀ i, D i ≃ D i; f_perm : ∀ i x, f i x = encD i (perm i x)   -- [55.1]
structure TrapdoorCollection extends PermCollection where                                                                -- [56.1]
  inv : NUPPT  inv_uniform : inv.Uniform
  inv_spec : ∀ n (r : gen.Coins n) (y : D (pairFstD (gen.runAt n [] r))) (s : inv.Coins n),
    decD _ (inv.runAt n (pairEncode (pairSndD (gen.runAt n [] r)) (encD _ y)) s) = some ((perm _).symm y)
theorem Collection.OneWay.exists_strongOneWay {F} (h : F.OneWay) : ∃ 𝓕 : FunFamily, 𝓕.StrongOneWay            -- [42.2 ⇒]
```

The dependent domain is handled by `uexp` over the generator's coins of the inner `uprob` on
`D i × ρ` (the uniform-on-`Σ` trap of the inventory is avoided). The (⇐) direction of Thm 42.2
(`StrongOneWay 𝓕 → (collection with Gen = 1^n).OneWay`) is stated alongside.

Run-3 audit (P3-1): the field `sample_spec` was added — without it Thm 42.2 (⇒) is unprovable
(nothing ties the sampler's outputs to `D_i` off the canonical encodings); `exists_strongOneWay`
is now proved from the explicit `owfFamily_strongOneWay` (sorried under its sketch), and every
instance discharges `sample_spec` (`FunFamily.toCollection`, `factoringCollection` by the
canonical default pair, `Collection.glPad m henc` — which now takes `henc` — by `F.sample_spec`,
the RSA/Rabin/Blum/exponentiation candidates by sorried `*Sampler_spec` stubs;
`expCollection H G hV` takes the validity bridge and its generator outputs `dlDefaultIndex`
below `n₀`). Run-3 audit (P3-5): the literal `Inv(1^n, ⟨⟨i, t⟩, y⟩)` form of Def 56.1 (6) was
not adopted; the Deviation is recorded on `TrapdoorCollection`, `rsaGen` and `blumGen`.

Gate 03b (finding 1, ruling G3-1): the field `encD_decD` (canonical decoding) was added. Without
it the sampler's and the trapdoor inverter's outputs were pinned only up to a possibly lenient
decoder, so `eval` and a hard-core evaluator (constrained on encodings) could misbehave on them.
Every instance discharges it by a decoder lemma (`ofFn_of_decodeFin_eq_some` for
`FunFamily.toCollection` and the padding of `Collection.glPad`; `expEnc_of_expDec`,
`encodeDistinctPrimes_of_decode`, `rsaEnc_of_rsaDec`; inline for `rabinCollection` and
`rabinBlumTrapdoor`). Derived: `Collection.decD_eq_some_iff`, `apply_of_decD`, `eval_of_decD`,
`sample_eq_encD`, `HardCore.evaluator`, `TrapdoorCollection.inv_eq_encD`, `eval_inv`,
`Collection.HardCore.nonempty_predEvaluator` and the evaluator-free
`TrapdoorCollection.OneWay.exists_glPad_singleBitSecure`. The helpers of Thm 42.2
(`NUPPT.withIndexParam`, `NUPPT.runLenPoly`, `splitCoins`, the marker padding) moved, names
unchanged, to `Asymptotic/CollectionsHelpers.lean`, which `Collections.lean` imports.

### 2.11 `TCSlib/Cryptography/Asymptotic/Ensembles.lean`

```lean
structure Ensemble (ℓ : PolyExpr) where                 -- [PS10, Def 69.3]
  σ : ℕ → Type
  [fintype : ∀ n, Fintype (σ n)]
  X : ∀ n, σ n → (Fin (ℓ.eval n) → Bool)
namespace Ensemble
def uniform (ℓ : PolyExpr) : Ensemble ℓ
def Samplable (X : Ensemble ℓ) : Prop :=                 -- distribution level, D6
  ∃ (s : PolyExpr) (S : List Bool → List Bool), PolyTimeComputable S ∧
    ∀ n, StatClose (fun r : Fin (s.eval n) → Bool => padFin (ℓ.eval n) (S (NUPPT.advInput n (List.ofFn r)))) (X.X n) 0
def Indist (X Y : Ensemble ℓ) : Prop :=                  -- [69.4], D receives 1^n (headline)
  ∀ D : NUPPT, Negligible fun n => distAdv (X.X n) (Y.X n) (D.distinguisher n (ℓ.eval n))
def IndistLit (X Y : Ensemble ℓ) : Prop :=               -- [69.4] literal: D receives t only
  ∀ D : NUPPT, Negligible fun n => distAdv (X.X n) (Y.X n) (D.distinguisher (ℓ.eval n) (ℓ.eval n))
def Pseudorandom (X : Ensemble ℓ) : Prop := Indist X (uniform ℓ)                                  -- [74.1]
def push (M : NUPPT) (ℓ' : PolyExpr) (X : Ensemble ℓ) : Ensemble ℓ'                               -- {M(X_n)}
def copies (t : PolyExpr) (X : Ensemble ℓ) : Ensemble (.mul t ℓ)
end Ensemble
theorem Ensemble.Indist.toLit (h : X.Indist Y) : X.IndistLit Y
theorem Ensemble.IndistLit.toIndist (hℓ : Function.Injective ℓ.eval) (h : X.IndistLit Y) : X.Indist Y
theorem Ensemble.Indist.refl (X) : X.Indist X                                                      -- non-vacuity
theorem Ensemble.Indist.symm (h : X.Indist Y) : Y.Indist X
theorem Ensemble.Indist.push {ℓ ℓ'} {X Y : Ensemble ℓ} (h : X.Indist Y) (M : NUPPT) : (X.push M ℓ').Indist (Y.push M ℓ')   -- [71.5]
theorem hybrid_lemma {m} (hm : 0 < m) (X : ℕ → σ → γ) (D) : ∃ i < m, distAdv (X 0) (X m) D / m ≤ distAdv (X i) (X (i+1)) D  -- [71.6], proved
theorem Ensemble.Indist.trans (h₁ : X.Indist Y) (h₂ : Y.Indist Z) : X.Indist Z
theorem Ensemble.Indist.copies (h : X.Indist Y) (hX : X.Samplable) (hY : Y.Samplable) (t : PolyExpr) : (X.copies t).Indist (Y.copies t)
def mixEnsemble (X₀ X₁ : Ensemble ℓ) (n) : Bool × (X₀.σ n × X₁.σ n) → Bool × (Fin (ℓ.eval n) → Bool)
theorem predict_eq … : uprob (fun z => D (if z.1.1 then X₁ z.1.2.2 else X₀ z.1.2.1) z.2 = z.1.1) = 1/2 + (acceptProb X₁ D - acceptProb X₀ D)/2   -- Claim 73.a
theorem prediction_lemma (X₀ X₁ : Ensemble ℓ) (D : NUPPT) (μ) (h : ∀ n₀, ∃ n ≥ n₀, μ n < distAdv …) :
    ∃ A : NUPPT, ∀ n₀, ∃ n ≥ n₀, 1/2 + μ n/2 < uprob fun z => A.predictor n (ℓ.eval n) (mixEnsemble X₀ X₁ n z.1).2 z.2 = (mixEnsemble X₀ X₁ n z.1).1   -- [73.8]
```

**Run-3 repair (audit P2-2, pack P2).** `Ensemble` has the additional instance field
`[nonempty : ∀ n, Nonempty (σ n)]` (an empty seed type is not a distribution; without it
`NextBitUnpredictable` was vacuous for an empty-seed ensemble and `prediction_lemma`,
`NextBitUnpredictable.pseudorandom` were unprovable as frozen). Every ensemble of the
campaign fills it by instance resolution (including `ddhReal`/`ddhRandom` of
`Candidates/ElGamal.lean`, whose seeds are products of coin types since the run-3 repair
P8-1). `prediction_lemma` and
`NextBitUnpredictable.pseudorandom` have exactly the frozen shapes above (the run-2 ad hoc
hypotheses `h₀ h₁`, `hσ` were dropped); `predict_eq` carries `[Nonempty σ₀] [Nonempty σ₁]
[Nonempty ρ]`, discharged automatically for ensemble seeds and machine coins.

Proof plans: 71.5 — `D' := exists_seq M D` (coins `M.coins + D.coins`), then
`distAdv_sunglassRed` with `P t c := padFin (ℓ' n) (M.runAt n (ofFn t) c)` gives equal advantages
after `acceptProb_comp_equiv` on the coin split (`Fin.appendEquiv`-style equivalence
`(Fin (a+b) → Bool) ≃ (Fin a → Bool) × (Fin b → Bool)`); `ℓ' : PolyExpr` makes the padding
computable (`unaryPoly ℓ'`). `toLit`: a literal distinguisher at length `ℓ n` is a `1^n`
distinguisher via `exists_reparam_advice ℓ.eval ℓ` with the advice carrying `α(ℓ n)` and
ignoring `1^n`; `toIndist` (injective `ℓ`): a `1^n` distinguisher `D` becomes a literal one with
advice `⟨1^n, D.advice n⟩` at length `ℓ n` (`Classical.choose` of the preimage; `[]` off the
image), coins `D.coins` evaluated at `ℓ n ≥ n` (`eval_mono`) and cut to `D.coinLen n`
(`exists_reparam_advice` with `φ := ℓ⁻¹`). `copies`: for every `n` take a maximising hybrid
index `k_n` (`exists_multicopyRed_ge`, `Finset.exists_max_image`) into the advice, sample the
other coordinates with the `Samplable` evaluators (`iterateEmit` over `t n` positions,
`StatClose … 0` lifts to the product law by `StatClose.prod`), plant the challenge; then
`Negligible.mul_pow`. `prediction_lemma`: `A := D` or `D` negated (`exists_comp` with
`computesFunInTime_ifEq`), chosen by pigeonhole on the infinite set; `predict_eq` is proved
once with `uprob_bool_prod`.

### 2.12 `Asymptotic/{Pseudorandom,NextBit,HardCore}.lean` — definition shapes

(The collection form of Thm 87.3, `Collection.glPad` … `goldreich_levin_coll`, moved unchanged to
`Asymptotic/HardCoreCollection.lean`, which `HardCore.lean` imports; gate 03c, finding 11.)

```lean
structure PRG where                                           -- [PS10, Def 77.1], length-regular
  stretch : PolyExpr
  G : ∀ n, (Fin n → Bool) → (Fin (stretch.eval n) → Bool)
  expands : ∀ n, n < stretch.eval n                           -- every n, n = 0 included: 2n, n^c excluded (§5.25; gate 03c, G3-2)
def PRG.Easy (P : PRG) : Prop := ∃ F, PolyTimeComputable F ∧ ∀ n (s : Fin n → Bool), F (List.ofFn s) = List.ofFn (P.G n s)
def PRG.ensemble (P : PRG) : Ensemble P.stretch               -- seeds Fin n → Bool
def PRG.Secure (P : PRG) : Prop := P.Easy ∧ P.ensemble.Pseudorandom

noncomputable def nextBitProb {ℓ} (X : σ → Fin ℓ → Bool) (i : Fin ℓ) (A : (Fin i → Bool) → ρ → Bool) : ℝ :=
  uprob fun z : σ × ρ => A (fun j => X z.1 (Fin.castLE i.isLt.le j)) z.2 = X z.1 i
def Ensemble.NextBitUnpredictable (X : Ensemble ℓ) : Prop :=   -- [PS10, Def 75.2], i < ℓ n, A gets 1^n and the prefix
  ∀ A : NUPPT, ∃ ε, Negligible ε ∧ ∀ n (i : Fin (ℓ.eval n)), nextBitProb (X.X n) i (A.predictor n i) ≤ 1/2 + ε n
theorem Ensemble.NextBitUnpredictable.pseudorandom (h : X.NextBitUnpredictable) : X.Pseudorandom   -- [75.4]; the source's statement (hℓ : ∀ n, 0 < ℓ.eval n dropped at gate 03c, G3-7b)

def HardCore (𝓕 : FunFamily) (h : ∀ n, (Fin (𝓕.inLen.eval n) → Bool) → Bool) : Prop :=   -- [PS10, Def 78.3]
  (∃ H, PolyTimeComputable H ∧ ∀ n x, H (NUPPT.advInput n (List.ofFn x)) = [h n x]) ∧
  ∀ A : NUPPT, ∃ ε, Negligible ε ∧ ∀ n, predProb (𝓕.f n) (h n) (A.predictor n (𝓕.outLen.eval n)) ≤ 1/2 + ε n
```

Theorem shapes of the HardCore file (statement phase): `owp_hardcore_prg (P : PermFamily) (h) : OneWayPermutation P → HardCore P.toFunFamily h → (PRG with G n s = f n s ‖ h n s).Secure`
(79.4, via `exists_owpPredictorBits`); `prg_expand (P : PRG) (ℓ : PolyExpr) : P.Secure → (prgExtBits-based PRG of stretch ℓ).Secure`
(80.5, via `exists_prgExtBitsRed_ge`, hybrid index as advice, `iterate` for the evaluator; **as shipped**
(gate 03c, finding 4): `prg_expand (G : ∀ n, (Fin n → Bool) → (Fin (n + 1) → Bool)) (ℓ : PolyExpr)
(hℓ : ∀ n, n < ℓ.eval n) (h : (PRG.oneBit G).Secure) : (PRG.expand G ℓ hℓ).Secure`, the one-bit input of the
text's Lemma 80.5 ("Let `G : {0,1}^n → {0,1}^{n+1}` be a PRG"); a general secure `P : PRG` reaches it through
`PRG.truncate` with `PRG.Secure.truncate : (PRG.oneBit P.truncate).Secure` in `Asymptotic/PRF.lean`, and `hℓ`
carries the cost of §5.25);
`cor_81_7` (closed form `prgExt_succ`); `goldreich_levin (𝓕) : StrongOneWay 𝓕 → StrongOneWay (glPad 𝓕) ∧ HardCore (glPad 𝓕) glBit`
(87.3, via `invProb_guessInverter`, `k(n) := ⌈log₂(2n^{2c+1}+1)⌉` hard-wired, `iterateFind`
for the `n(2^k−1)` calls, `majority`, `pairXor`); `goldreich_levin_coll (F : Collection) …`
(87.3.coll, `half_le_uprob_threshold` over `i`).

### 2.13 Encryption shapes — `Asymptotic/Encryption.lean`, `Asymptotic/PublicKey.lean`, `ZeroKnowledge/Encryption.lean`

```lean
structure PrivateKeyScheme where                               -- [PS10, Def 24.7]
  gen enc dec : NUPPT
  gen_uniform : gen.Uniform   enc_uniform : enc.Uniform   dec_uniform : dec.Uniform
  correct : ∀ n (m : Fin n → Bool) (rg : gen.Coins n) (re : enc.Coins n) (rd : dec.Coins n),
    decodeFin n (dec.runAt n (pairEncode (gen.runAt n [] rg) (enc.runAt n (pairEncode (gen.runAt n [] rg) (List.ofFn m)) re)) rd) = some m
def PrivateKeyScheme.encDist (S) (n) (m : Fin n → Bool) : S.gen.Coins n × S.enc.Coins n → List Bool
def PrivateKeyScheme.SingleMessageSecure (S) : Prop :=        -- [91.1]
  ∀ D : NUPPT, ∃ ε, Negligible ε ∧ ∀ n (m₀ m₁ : Fin n → Bool), distAdv (S.encDist n m₀) (S.encDist n m₁) (D.distinguisherL n) ≤ ε n
def PrivateKeyScheme.multiEncDist (S) (n q : ℕ) (m : Fin (q+1) → Fin n → Bool) : S.gen.Coins n × (Fin (q+1) → S.enc.Coins n) → List Bool
def PrivateKeyScheme.MultiMessageSecure (S) : Prop :=         -- [93.1], q n + 1 messages
  ∀ (D : NUPPT) (q : PolyExpr), ∃ ε, Negligible ε ∧ ∀ n (m m' : Fin (q.eval n + 1) → Fin n → Bool),
    distAdv (S.multiEncDist n (q.eval n) m) (S.multiEncDist n (q.eval n) m') (D.distinguisherL n) ≤ ε n
def PrivateKeyScheme.ZeroKnowledge (S) : Prop :=               -- [111.1]
  ∃ Sim : NUPPT, Sim.Uniform ∧ ∀ D : NUPPT, ∃ ε, Negligible ε ∧ ∀ n (m : Fin n → Bool),
    distAdv (S.encDist n m) (Sim.runAt n []) (D.distinguisherL n) ≤ ε n
theorem PrivateKeyScheme.singleMessageSecure_iff_zeroKnowledge (S) : S.SingleMessageSecure ↔ S.ZeroKnowledge   -- [112.2]

structure PublicKeyScheme where                                -- [PS10, Def 102.1]; clause (4) dropped (Deviation)
  gen enc : NUPPT   dec : List Bool → List Bool
  gen_uniform : gen.Uniform   enc_uniform : enc.Uniform   dec_poly : PolyTimeComputable dec
  correct : ∀ n (m : Fin n → Bool) (rg : gen.Coins n) (re : enc.Coins n),
    decodeFin n (dec (pairEncode (pairSndD (gen.runAt n [] rg)) (enc.runAt n (pairEncode (pairFstD (gen.runAt n [] rg)) (List.ofFn m)) re))) = some m
def PublicKeyScheme.pkEncDist (S) (n) (m) : S.gen.Coins n × S.enc.Coins n → List Bool    -- ⟨pk, Enc_pk(m)⟩
def PublicKeyScheme.Secure (S) : Prop := ∀ D : NUPPT, ∃ ε, Negligible ε ∧ ∀ n m₀ m₁, distAdv (S.pkEncDist n m₀) (S.pkEncDist n m₁) (D.distinguisherL n) ≤ ε n   -- [102.2]
```

`MultiMessageSecure` for PKE, `SingleBitSecure` (message space `Bool`, encoded as `[b]`), the
bitwise scheme (103.f) and Alg 104.3 (`gen := TDP gen`, `enc := ⟨f_i(r), b_i(r) ⊕ m⟩`) follow the
same shapes in `PublicKey.lean`. Alg 92.1 and Alg 99.1 are `PrivateKeyScheme` values built with
`ofPolyTimeUniform` of FP functions (`pairXor` for the one-time pad).

### 2.14 `TCSlib/Cryptography/Asymptotic/PRF.lean`

```lean
structure OracleEnsemble (ℓ₁ ℓ₂ : PolyExpr) where              -- [PS10, Def 96.1]
  σ : ℕ → Type   [fintype : ∀ n, Fintype (σ n)]
  O : ∀ n, σ n → (Fin (ℓ₁.eval n) → Bool) → (Fin (ℓ₂.eval n) → Bool)
def OracleEnsemble.random (ℓ₁ ℓ₂ : PolyExpr) : OracleEnsemble ℓ₁ ℓ₂            -- RF_n, seed = table
def OracleEnsemble.keyed {ℓ₁ ℓ₂} (F : ∀ n, (Fin n → Bool) → (Fin (ℓ₁.eval n) → Bool) → (Fin (ℓ₂.eval n) → Bool)) : OracleEnsemble ℓ₁ ℓ₂
inductive OracleMove (ℓ₁ : ℕ) | query (x : Fin ℓ₁ → Bool) | ret (b : Bool)
def decodeOracleMove (ℓ₁ : ℕ) (w : List Bool) : OracleMove ℓ₁                 -- ⟨[false], x⟩ query; [true, b] verdict
def encodeHist {ℓ₁ ℓ₂} (h : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool))) : List Bool
def buildTree {ℓ₁ ℓ₂} (next : List (…) → OracleMove ℓ₁) : ℕ → List (…) → QueryTree (Fin ℓ₁ → Bool) (Fin ℓ₂ → Bool) Bool
def Complexity.NUPPT.toOracleAdversary (D : NUPPT) (n ℓ₁ ℓ₂ q : ℕ) : OracleAdversary (D.Coins n) (Fin ℓ₁ → Bool) (Fin ℓ₂ → Bool)
theorem Complexity.NUPPT.toOracleAdversary_boundedBy (D) (n ℓ₁ ℓ₂ q) : (D.toOracleAdversary n ℓ₁ ℓ₂ q).BoundedBy q
def OracleEnsemble.Indist (O O' : OracleEnsemble ℓ₁ ℓ₂) : Prop :=               -- ∀ D, ∀ q
  ∀ (D : NUPPT) (q : PolyExpr), Negligible fun n => distAdv (O.O n) (O'.O n) (oracleDist (D.toOracleAdversary n (ℓ₁.eval n) (ℓ₂.eval n) (q.eval n)))
theorem OracleEnsemble.Indist.refl (O) : O.Indist O                                                     -- non-vacuity
structure PRF (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool)) : Prop where                 -- [PS10, Def 96.2]
  easy : ∃ E, PolyTimeComputable E ∧ ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (F n s x)
  pseudorandom : (OracleEnsemble.keyed (ℓ₁ := .var) (ℓ₂ := .var) F).Indist (OracleEnsemble.random .var .var)
theorem prfAdv_toOracleAdversary (F) (D : NUPPT) (n q : ℕ) :
    distAdv ((keyed F).O n) ((random .var .var).O n) (oracleDist (D.toOracleAdversary n n n q)) = prfAdv (F n) (D.toOracleAdversary n n n q) := rfl
```

Theorem 97.3 plan: REUSE-MAX §5 unchanged (the hybrid indices `(i_n, j_n)` from
`exists_ggmBits_dist` into the advice; the PRG distinguisher hosts `D`'s next-query function
in an `iterateFind` loop over at most `q n + 1` activations with the lazily sampled table in the
state; functional identity with `evalLazy`/`noteQuery` by induction on the tree;
`Negligible.mul_pow` for `n · q n`). Theorem 99.2's oracle adversary is a chain of `q n + 1`
`query` nodes built by `buildTree` from an FP next-query function with the messages as advice.

### 2.15 Chapter 4 — `ZeroKnowledge/{Interaction,InteractiveProofs,Defs,Commitment,GraphIsomorphism}.lean`

```lean
structure Strategy where
  next : List Bool → List Bool → List Bool → List (List Bool) → List Bool     -- x z r received ↦ message / output
  coins : PolyExpr
namespace Strategy
def coinLen (S) (n) : ℕ := S.coins.eval n
abbrev Coins (S) (n) : Type := Fin (S.coinLen n) → Bool
def encodeMsgs (h : List (List Bool)) : List Bool := h.foldr pairEncode []
def ofNUPPT (A : NUPPT) : Strategy :=   -- one activation at parameter |x| on ⟨⟨x, z⟩, messages⟩, whole random tape
  { next := fun x z r hist => A.runAtL x.length (pairEncode (pairEncode x z) (encodeMsgs hist)) r, coins := A.coins }
def Efficient (S : Strategy) : Prop := ∃ A : NUPPT, A.Uniform ∧ S.coins = A.coins ∧ ∀ x z r hist, S.next x z r hist = (ofNUPPT A).next x z r hist
end Strategy

def moverIsV (vFirst : Bool) (k : ℕ) : Bool := if vFirst then decide (k % 2 = 0) else decide (k % 2 = 1)
/-- Messages received by (P, V) after k moves. -/
def exec (P V : Strategy) (vFirst : Bool) (x zP zV rP rV : List Bool) : ℕ → List (List Bool) × List (List Bool)
  | 0 => ([], [])
  | k + 1 => let e := exec P V vFirst x zP zV rP rV k
             if moverIsV vFirst k then (e.1 ++ [V.next x zV rV e.2], e.2) else (e.1, e.2 ++ [P.next x zP rP e.1])
structure View where (x z r : List Bool) (received : List (List Bool))
def View.encode (v : View) : List Bool := pairEncode (pairEncode v.x v.z) (pairEncode v.r (Strategy.encodeMsgs v.received))
structure Protocol where (P V : Strategy) (rounds : PolyExpr) (verifierFirst : Bool)    -- rounds = number of messages
namespace Protocol
abbrev ExecCoins (π) (P' : Strategy) (x) : Type := P'.Coins x.length × π.V.Coins x.length
def withV (π) (V' : Strategy) : Protocol := { π with V := V' }
def transcriptWith (π) (P') (x y z) (r : π.ExecCoins P' x) : List (List Bool) × List (List Bool) :=
  exec P' π.V π.verifierFirst x y z (List.ofFn r.1) (List.ofFn r.2) (π.rounds.eval x.length)
def outV (π) (P') (x y z) (r) : List Bool := π.V.next x z (List.ofFn r.2) (π.transcriptWith P' x y z r).2
def outP (π) (x y z) (r) : List Bool
def viewV (π) (x y z) (r : π.ExecCoins π.P x) : View := ⟨x, z, List.ofFn r.2, (π.transcriptWith π.P x y z r).2⟩
def viewP (π) (x y z) (r) : View
end Protocol

structure InteractiveProof (π : Protocol) (L : Language Bool) : Prop where            -- [PS10, Def 116.1]
  efficientV : π.V.Efficient
  complete : ∀ x ∈ L, ∃ y, ∀ z, uprob (fun r : π.ExecCoins π.P x => π.outV π.P x y z r = [true]) = 1
  sound : ∃ ε, Negligible ε ∧ ∀ x ∉ L, ∀ (P' : Strategy) z, 1 - ε x.length < uprob (fun r : π.ExecCoins P' x => π.outV P' x [] z r = [false])
structure InteractiveProofErr (π) (L) (s : ℕ → ℝ) : Prop where                        -- soundness error s
  efficientV …  complete …
  sound : ∀ x ∉ L, ∀ P' z, 1 - s x.length ≤ uprob (fun r => π.outV P' x [] z r = [false])
structure WitnessRelation (L : Language Bool) (R : List Bool → List Bool → Prop) : Prop where   -- Appendix B
  mem_iff : ∀ x, x ∈ L ↔ ∃ y, R x y
  bounded : ∃ p : PolyExpr, ∀ x y, R x y → y.length ≤ p.eval x.length
  decidable : ∃ T : List Bool → Bool, PolyTimeComputable (fun z => [T z]) ∧ ∀ x y, T (pairEncode x y) = true ↔ R x y
structure EfficientProverProof (π) (L) (R) : Prop extends InteractiveProof π L where    -- [PS10, Def 119.5]
  efficientP : π.P.Efficient
  completeWitness : ∀ x y, R x y → ∀ z, uprob (fun r => π.outV π.P x y z r = [true]) = 1
structure EfficientProverProofErr (π) (L) (R) (s) : Prop extends InteractiveProofErr π L s where …

def Complexity.NUPPT.simulate (S : NUPPT) (x z : List Bool) (r : S.Coins x.length) : List Bool := S.runAt x.length (pairEncode x z) r
def HVZK (π) (R) : Prop :=                                                               -- [121.1]
  ∃ S : NUPPT, S.Uniform ∧ ∀ (Lz : PolyExpr) (D : NUPPT), ∃ ε, Negligible ε ∧ ∀ x y z, R x y → z.length ≤ Lz.eval x.length →
    distAdv (fun r => (π.viewV x y z r).encode) (S.simulate x z) (D.distinguisherL x.length) ≤ ε x.length
def ZK (π) (R) : Prop :=                                                                 -- [121.2]
  ∀ V' : Strategy, V'.Efficient → ∃ S : NUPPT, S.Uniform ∧ ∀ (Lz : PolyExpr) (D : NUPPT), ∃ ε, Negligible ε ∧
    ∀ x y z, R x y → z.length ≤ Lz.eval x.length →
      distAdv (fun r => ((π.withV V').viewV x y z r).encode) (S.simulate x z) (D.distinguisherL x.length) ≤ ε x.length
def StatZK (π) (R) (δ : ℕ → ℝ) : Prop :=
  ∀ V', V'.Efficient → ∃ S : NUPPT, S.Uniform ∧ ∀ x y z, R x y → StatClose (fun r => ((π.withV V').viewV x y z r).encode) (S.simulate x z) (δ x.length)
def PerfectZK (π) (R) : Prop := StatZK π R (fun _ => 0)
def PerfectZKAbort (π) (R) : Prop :=                                                     -- Goldreich Def 4.3.1, ⊥ = []
  ∀ V', V'.Efficient → ∃ S : NUPPT, S.Uniform ∧ ∀ x y z, R x y →
    uprob (fun r : S.Coins x.length => S.simulate x z r = []) ≤ 1/2 ∧
    ∀ T : List Bool → Prop, uprob (fun r => T (view r)) * uprob (fun r => S.simulate x z r ≠ []) = uprob (fun r => S.simulate x z r ≠ [] ∧ T (S.simulate x z r))
theorem StatZK.zk (hδ : Negligible δ) (h : StatZK π R δ) : ZK π R
theorem StatZK.hvzk (hδ : Negligible δ) (hV : π.V.Efficient) (h : StatZK π R δ) : HVZK π R

structure Commitment (Com : List Bool → List Bool) (ℓ : PolyExpr) : Prop where          -- [PS10, Def 126.3], binding repaired
  easy : PolyTimeComputable Com
  binding : ∀ n v₀ v₁ r₀ r₁, v₀.length = n → v₁.length = n → r₀.length = ℓ.eval n → r₁.length = ℓ.eval n → v₀ ≠ v₁ →
    Com (pairEncode v₀ r₀) ≠ Com (pairEncode v₁ r₁)
  hides : ∀ D : NUPPT, ∃ ε, Negligible ε ∧ ∀ n (v₀ v₁ : Fin n → Bool),
    distAdv (fun r : Fin (ℓ.eval n) → Bool => Com (pairEncode (List.ofFn v₀) (List.ofFn r)))
            (fun r : Fin (ℓ.eval n) → Bool => Com (pairEncode (List.ofFn v₁) (List.ofFn r))) (D.distinguisherL n) ≤ ε n
```

Graph isomorphism (compiled expressibility check): `Graph n := Fin n → Fin n → Bool`,
`permGraph G π u v := G (π.symm u) (π.symm v)`, `encGraph`/`decGraph` (adjacency matrix, `n²`
bits, `Nat.sqrt`), `encPerm`/`decPerm` (relation matrix, `Fin.find`, `Equiv.ofBijective`),
`fisherYates n c`, `permFromCoins n k T : (Fin n → Fin T → Fin k → Bool) → Option (Equiv.Perm (Fin n))`
with `permFromCoins_uniform_of_some` and `uprob_permFromCoins_none_le (hk : n ≤ 2^k) : … ≤ n (1/2)^T`;
`giProver` (coins `normal 1 2`; `π` by `permFromCoins n n n`, identity on failure; message 1
`encGraph (π(G₀))`, message 3 `encPerm (if b then π * σ⁻¹ else π)`), `giVerifier` (coins
`const 1`; on `[H]` sends `[b]`, on `[H, γ]` outputs `[decide (encGraph (permGraph G_b (decPerm n γ)) = H)]`),
`giProtocol := ⟨giProver, giVerifier, const 3, false⟩` (three messages, prover first; the
verdict is the fourth activation), `Liso`, `Riso`, `Riso_witnessRelation`,
`gi_sim_H_dist`/`gi_sim_half` (Lemma 123.5, exact over `Equiv.Perm (Fin n)`),
`gi_efficientProverProofErr : EfficientProverProofErr giProtocol Liso Riso (fun _ => 1/2)` (Prop 120.7,
one iteration), `gi_statZK : ∃ δ, Negligible δ ∧ StatZK giProtocol Riso δ` (Theorem 122.3,
`δ n = 2^{-n} + 2 n (1/2)^n` from the truncated simulator and the rejection sampler),
`giProtocolRep := ⟨giProverRep, giVerifierRep, mul (const 3) var, false⟩` with
`InteractiveProof giProtocolRep Liso` (Lemma 120.d), and the sanity
`npProtocol_interactiveProof : EfficientProverProof (npProtocol T) L R` (P sends `y`).

**Run-3 repair (audit P2-1, pack P2).** The permutation-sampler parameters above are
superseded: the honest parties sample by
`samplePerm n r := (permFromCoins n (permBits n) (permTrials n) (coinTable n (permTrials n) (permBits n) r)).getD 1`
(`permBits n = Nat.size n`, `permTrials n = 2n²`, `Asymptotic/Permutations.lean`) with
`permCoinLen n := n * permTrials n * permBits n ≤ (N + 1)²` whenever `2n² ≤ N`
(`permCoinLen_le`; every encoded instance has length `3n² + 2`, so the coin polynomials
`normal 1 2` are kept), `permFailBound n := n * (2 : ℝ)⁻¹ ^ n` (`statClose_samplePerm` and
`negligible_mul_permFailBound` proved from the shared lemmas; the run-2 `permFailBound_le_exp`
removed), and `polyTimeComputable_encPermFromCoins` (`ZeroKnowledge/Encoding.lean`) is stated
at the same parameters, GI's private `polyTimeComputable_encSamplePerm` being derived from
it. `gi_statZK`'s planned error becomes `δ n = 2^{-n} + (n + 1) · n · 2^{-n}`.

**Run-3 repair (audit P10-1/P10-2, pack P10).** The exact-probability engines of the
adaptive-prover bounds, `uprob_adaptive_guess` (Lem-119.c) and `uprob_gni_rep_cheat`
(Lem-119.b), assume the auxiliary coin type nonempty (`[Nonempty W]`, `[Nonempty ρ]`): `uprob`
on an empty type is `0`, so the run-2 statements specialised to `Empty` at `m = 0` read
`0 = 1`. Every consumer instantiates the coin type with a tape `Fin k → Bool`, so no
downstream statement changes; `uprob_gi_rep_cheat_le` (Lem-120.d, an inequality) keeps its
statement and is reproved by a case split on `ρ`. Audit P10-3 (divergent sampler copies) is
resolved by the P2-1 repair above: `polyTimeComputable_encSamplePerm` is derived from the
shared `polyTimeComputable_encPermFromCoins` at the one set of parameters.

---

## 3. Disposition of every panel refutation

| # | Refutation (judge) | Disposition |
| --- | --- | --- |
| 1 | REUSE-MAX `iterateFind`: `Inv x s := ∃ i ≤ R|x|, s = g^[i] x` not closed under `stepF` (J1-7, J2-15, J3-5) | **Fixed** (§2.6): length-guarded step on a state word carrying the input, `Inv x w := pairFstD w = x ∧ |pairSndD w| ≤ P|x|`; `horbit` shows the guard is inactive on the orbit. The statement is unchanged. |
| 2 | REUSE-MAX anchor exclusion / `entry = exit` and overriding the module table at `exit` (J2-16, J3-6) | **Fixed** (§2.6 step 3): fresh anchor state `inl ()` stepping into `C₁.entry`; transitions *into* `exit` are redirected to fresh branch states, the module table at `exit` is never overridden. |
| 3 | REUSE-MAX `Indist.push` without `hℓ'` (J1-8, J2-17, J3-7) | **Fixed**: `ℓ' : PolyExpr`; the bound is intrinsic (`eval_le`) and `1^{ℓ' n}` is computed (`unaryPoly`). |
| 4 | REUSE-MAX `Indist.copies` without `Samplable` (J1-8, J3-7) | **Fixed**: hypotheses `hX : X.Samplable`, `hY : Y.Samplable` (§2.11). |
| 5 | REUSE-MAX `Samplable` as a seed bijection is unsatisfiable for `U_n` and pushed ensembles (J2-14) | **Fixed**: distribution-level `Samplable` (`StatClose … 0` from `s.eval n` bits, `s : PolyExpr`); `U_n` has `s = var`, `S = pairSndD`. |
| 6 | REUSE-MAX GI `rounds = 3` leaves `outB = none`; `CR(n+1)^cR ≠ 3` (J1-9); FAITHFUL `rounds = 1` gives the coin bit (J1-14, J3-?) | **Fixed**: `rounds : PolyExpr := const 3` counts messages; the verdict is `V.next` on the complete history (fourth activation), always defined. |
| 7 | REUSE-MAX abstract `ℕ → ℕ` lengths (`inLen/outLen`, `Ensemble ℓ`, `push ℓ'`, `copies t`) against the brief (J1-10, J3-8) | **Fixed**: all are `PolyExpr`; `InLenPoly` and `Lin` disappear (`polyTimeComputable_unaryPoly`). |
| 8 | REUSE-MAX `1^n` given to Def 26.1 / 69.4 adversaries (J1-10, graft from FAITHFUL) | **Fixed**: `WorstCaseOneWayLit` literal (`inverterLit`), `IndistLit` literal; `WorstCaseOneWay`/`Indist` (headline, `1^n` form) related by `toLit`/`toParam`, `toLit`/`toIndist` (D5; run-3 audit P3-2 made the `1^n` form the headline of Def 26.1 as well). |
| 9 | REUSE-MAX power-of-two block count in 35.1 (J2 graft `pow2log`, J1 fallback R2) | **Rebutted/replaced**: no `pow2log` constructor; the text's `m = 2nq(n)` is literal and the uniform position is rejection-sampled with the D10 device (statistical term `T·2^{-n}` absorbed in `μ₀`). |
| 10 | REUSE-MAX `Samplable` claims and `prediction_lemma` advice (J1 critique) | `prediction_lemma` uses no advice (pigeonhole, `exists_comp`); `copies` uses advice for `k_n`. |
| 11 | ABSTRACT `WeakOWF` vacuous, `weak_to_strong` false (J1, J2, J3) | **Guarded**: `WeakOneWay.hard` carries `∀ n, 0 < q.eval n`; `weak_to_strong` stated for the guarded notion. |
| 12 | ABSTRACT `iterate`/`mem_iter` unsatisfiable without a growth bound (J1, J2, J3) | **Avoided**: every iteration lemma carries `horbit`; no interface fields. |
| 13 | ABSTRACT don't-care runs outside the declared coin length (`oracleAdv`, `coinsP/coinsV` at `z = []`, `PRF` unsatisfiable) (J1, J2, J3) | **Not applicable**: `NUPPT` is total; `runAt n` fixes one coin type per `n`; strategies use the whole tape at parameter `|x|`; oracle adversaries use `runAt n` on the growing history. |
| 14 | ABSTRACT `gi_sim_statDist` ill-typed (`FinDist` needs `Fintype`) (J2, J3) | **Avoided**: `StatClose` sup-over-test-sets form; `distAdv_le_of_statClose`. |
| 15 | ABSTRACT `exec` hardcodes verifier-first (J1) | **Fixed**: `Protocol.verifierFirst`, `moverIsV`. |
| 16 | ABSTRACT `exists_stepCallTM` extends private Loop.lean machinery (J1, J2) | **Avoided**: `iterateFind` uses only the public `exists_loopFindTM`, `exists_installCallTM`, `exists_emitCallTM`. |
| 17 | FAITHFUL `runCoins_eq_of_take` false at `t = 0` (J2) | **Not applicable** (no coin tape); the "extra coins unread" device is the `r.take` clause of `exists_reparam_advice`, a statement about FP functions. |
| 18 | FAITHFUL `Poly.eval = C(n+1)^c` cannot express `n`, `2n` (J1, J2) | **Fixed by `PolyExpr`** (`var`, `mul (const 2) var`). |
| 19 | FAITHFUL `FunFamily.str` conflates parameter and input length (J1, J2) | **Avoided**: `Easy` evaluates on `⟨1^n, x⟩`. |
| 20 | FAITHFUL `∃ N` after `∀ x y z` in `HVZK`/`ZK`/`hide` (J1, J2, J3) | **Avoided**: no coin budget variable; distinguisher at parameter `|x|`, `Lz` universally quantified before `ε`. |
| 21 | FAITHFUL `nuppt_seq_iff_advice` conditional on `PolyBound canonizerTime`; `one_work_tape_binary` not at the seam (J1, J2, J3) | **Off the critical path**: `NUPPTSeq` optional module with one named admission (D4, D11). |
| 22 | FAITHFUL `Strategy.IsPPT` run cut at the deadline; `encodeView` sorried (J3) | **Not applicable**: total machines; `View.encode` is defined. |
| 23 | FAITHFUL `exists_handlerSim` possibly prohibitive (J1) | **Not needed**: D7 next-query machines; GGM's reduction hosts the adversary's next-query function in `iterateFind`. |
| 24 | FAITHFUL `forall_of_uprob_eq_one` namespace (J1, J3) | Recorded: `TCSlib.Cryptography.HardcoreBit.forall_of_uprob_eq_one` (HardcoreBit/Basic.lean:107), `uprob_eq_one_of_forall` (:120). |
| 25 | FAITHFUL/J2: `distAdv_sunglassRed` is at Indistinguishability.lean:130 | Recorded. |
| 26 | J3: `1^n` vs `|x|` indexing, time in machine-input length, totality must be in the decision log | **Recorded** in D3 with the interdefinability argument. |

Issues found in this synthesis and resolved here (not raised by the panel):

* The text's "a round ends with the active machine halting — in which case the protocol ends"
  makes the literal `Pr[out_V = 0]` unsatisfiable against the immediately-halting prover
  (the verifier never outputs). The fixed-alternation model with the verdict on the complete
  history is the reading under which the literal `[false]` soundness clause is satisfiable
  (D8, Deviation recorded).
* With total machines, a verifier `V*` and a distinguisher `D` read all of an unbounded `z`,
  so the non-uniform reduction of Prop 128.8 (which hard-wires the worst `(x, y, z)`) needs
  `|z|` polynomially bounded; hence the `∀ Lz` clause (D8). The text's own model (time `t(|x|)`)
  implies the same bound implicitly.
* `exists_reparam_advice` is the one place an abstract `φ : ℕ → ℕ` appears; it is a theorem
  hypothesis with a `PolyExpr` majorant (needed by Lemma 64.3's `m(n) = n − ⌊log₂ n⌋` and by
  `IndistLit.toIndist`), consistent with the brief.

## 4. Grafts adopted (source → where)

| Graft | From | Where it lands |
| --- | --- | --- |
| Syntactic `PolyExpr` for every length/budget | ABSTRACT | `Randomized/PolyExpr.lean`; all structures |
| `∀ q : PolyExpr` oracle budget | ABSTRACT | `OracleEnsemble.Indist` |
| First-mover field; padded/explicit per-parameter coin types | ABSTRACT | `Protocol.verifierFirst`; coins at parameter `|x|` |
| Non-vacuity theorems | ABSTRACT, FAITHFUL | `NUPPT.nonempty`, `not_strongOneWay_id`, `StrongOneWay.weak`, `Indist.refl`, `OracleEnsemble.Indist.refl`, `npProtocol_interactiveProof` + `Checks.lean` prints |
| Power-of-two index discipline for exact uniformity; definable `NESubset k ≃ Fin (2^k − 1)` | ABSTRACT | GL inverter packaging (HardCore workstream) |
| Literal Def 26.1 and Def 69.4 forms, never unified silently | FAITHFUL, J1–J3 | `WorstCaseOneWay`, `IndistLit`, `toLit`/`toIndist` |
| `advice_length ≤` | FAITHFUL | `NUPPT.advice_length` |
| Literal `[false]` soundness; `∃ ε` before `∀ x P' z`; arbitrary provers | FAITHFUL | `InteractiveProof.sound` |
| Abort-form perfect ZK; non-dyadic permutation finding | FAITHFUL, J2 | `PerfectZKAbort`; `permFromCoins`; `gi_statZK` |
| "Extra coins unread" transport instead of Σ-types | FAITHFUL | `exists_reparam_advice`'s `r.take`; `StatClose.prod` |
| `NUPPTSeq`, `exists_queryTree`, `ofPartial` as optional modules with named admissions | FAITHFUL, J1 | D4, D7, D11 |
| Statistical-switch device for non-dyadic samplers (Q3), shared by Thm 35.1, candidates and ch. 4 | inventory-ch2 F4/C10, J2 | `Asymptotic/Sampling.lean` (D10) |
| Distribution-level `Samplable` | J2 | `Ensemble.Samplable` |
| Closure lemmas preserve `Uniform` | J2, ABSTRACT | `exists_reparam`, `exists_seq`, `ofPolyTimeUniform` |
| Repaired `iterateFind` construction (guarded step, carried input, fresh anchor) | J1–J3 | §2.6 |

## 5. Deviations register (docstring text, one line each)

1. `NUPPT`: totality on all inputs (behaviour class unchanged via clocking); time in the
   machine-input length; advice and coins indexed by the parameter `n` read from `1^n`.
2. `NUPPT`: Def 26.8's machine-sequence formulation not formalized in the core (optional module).
3. `FunFamily.Easy`: deterministic polynomial-time evaluator on `⟨1^n, x⟩` instead of a PPT
   computing with probability one (equivalent by `Computes` + `ofPolyTimeUniform`).
4. `inverter`: wrong-length output = failure (D5); verdict `= [true]` (normalisable by `ifEq`).
5. `Ensemble`: dyadic samplable distributions; `Indist` gives `D` the input `1^n` (literal form
   `IndistLit`, equivalent for every `PolyExpr ℓ`: proved for injective `ℓ`, the constant case
   by point tests, not formalized; gate 03a, note 14).
6. `WeakOneWay`: `0 < q n` made explicit; Theorem 35.1 with the text's `m = 2nq(n)` and a
   rejection-sampled position (statistical term absorbed).
7. `OracleEnsemble.Indist`: next-query machines with an explicit universally quantified
   budget; no oracle tapes; forced verdict `false` after `q n` queries.
8. `Protocol`: fixed number of messages `rounds.eval |x|`, verdict on the complete history
   (halting = sending `[]`); `Efficient` time polynomial in the total input length. The honest
   messages are polynomially bounded in `|x|` (`Protocol.ProverBounded`, in
   `InteractiveProof(Err).complete` and the field `EfficientProverProof(Err).boundedP`): the
   source's p.p.t. prover writes at most `t(|x|)` bits. Against a cheating prover the verifier's
   work is polynomial in the message length, not in `|x|` (gate 03e, finding 1; ruling G3-3).
9. Soundness `1 − ε < Pr[out = [false]]` literal; provers have polynomial coin tapes (no loss by
   averaging); completeness `uprob = 1` (every coin pair).
10. `ZK`/`HVZK`: strict PPT simulators; auxiliary inputs bounded by `∀ Lz : PolyExpr`;
    simulator and distinguisher at parameter `|x|`; views encoded as `⟨⟨x, z⟩, ⟨r, msgs⟩⟩`.
11. GI/3COL: statistical ZK (truncated simulators, rejection-sampled permutations / edges /
    colour permutations); one-iteration ZK, `n`-fold protocols get soundness only (sequential
    composition is §7.2.1, out of scope). `PerfectZK` and `PerfectZKAbort` are stated, but no
    source protocol attains them under D8/D10; GI is `StatZK` with negligible δ, and
    `PerfectZKAbort.statZK` turns the abort form into statistical ZK with error `2^{-|x|}`
    (gate 03e, finding 2; ruling G3-4).
12. `Commitment`: binding clause with `v₀ ≠ v₁` (source error); `n` an explicit argument,
    colours padded to `n` bits (DQ4).
13. `PublicKeyScheme`: clause (4) (message enumerator) dropped; `0^n` is the canonical message.
14. `Collection`: `Gen(1^n) = ⟨i, t⟩`; domain samplers within negligible statistical distance of
    uniform (`SampleClose`), hardness on the ideal uniform `x ← D_i` (`uexp` over `Gen`'s coins).
15. Candidates: `A` receives `1^n` in Assumptions 30.1/52.2/53.1; `Π_n` throughout; `p ≠ q`
    (odd / Blum) in RSA and Rabin; expected time replaced by strict PPT with `2^{-n}` failure.
16. `WorstCaseOneWayLit` (run-3 audit P3-2; reworded at gate 03b, finding 9): when `outLen` is
    constant, so that `|f(x)|` does not determine `n`, the literal form can hold for families
    that are trivially invertible given `1^n` (e.g. the constant family, or `f n b = b ⊕ [n odd]`
    on one bit), an artefact of D5's typed inverse; the `1^n` form `WorstCaseOneWay` is the
    headline, and `toParam` applies whenever `outLen` is non-constant (for `PolyExpr`,
    injective ⇔ non-constant).
17. `TrapdoorCollection.inv_spec` (run-3 audit P3-5): the inverter receives `⟨t, y⟩` without the
    index. The classes coincide (gate 03b, finding 6): a text TDP becomes one of this shape with
    `t' := ⟨i, t⟩` (`Gen'` outputs `⟨i, ⟨i, t⟩⟩`; the trapdoor never reaches the adversary), and
    this shape is a text TDP whose `Inv` ignores `i`. RSA's trapdoor is `⟨N, d⟩` (text: `d`) and
    Rabin's inverter recomputes `N = pq`.
18. `Collection.glPad m henc`, `expCollection H G hV` (run-3 audit P3-1): the encoding-length
    hypothesis resp. the validity bridge are arguments of the definitions; `expGen` outputs the
    fixed valid instance `dlDefaultIndex` below the instance generator's threshold `n₀`. Cost of
    `henc` (gate 03c, finding 3; ruling G3-7c): a non-constant `PolyExpr` is strictly
    increasing, so an index generated at two parameters forces `m` constant, and no candidate of
    the library satisfies `henc` as parametrized (`rsaTrapdoor`: `2·max(n, 2)`-bit elements,
    `rabinBlumTrapdoor`: `2·max(n, 3)`, `expCollection`: `dlDefaultIndex` below `n₀`); Thm 104.4's
    reading "from trapdoor permutations" (`glPad_hardCore`, `exists_glPad_singleBitSecure`) holds
    for TDPs whose generated indices encode elements in exactly `m(n)` bits. A per-index form
    (`|encD_i x| = |encD_i default| ≤ m(n)`) would admit the candidates; not formalized.
19. Theorem 63.1 (run-3 audit P3-4): `theorem_63_1`, `fUniversal_*` are conditional on an
    encoding scheme with `CanonizerExp c`; no instance proved (`exists_canonizerExp`).
20. `ddhReal`/`ddhRandom` (run-3 audit P8-1): the DDH exponents `a, b, z` are read from
    `n · n`-bit seed blocks by rejection (`ddhExpo`, within `2^{-n}` of uniform, D10) — product
    seeds, never a dependent sum (uniform-on-`Σ` tilts the instance law by the fibre sizes).
21. `ExpGroupGen.FullLengthExcept δ` (run-3 audit P8-2): full-length primes except on a set of
    the generator's coins of probability `δ n`; `fullDLCollection_hardCore` and `elGamal_secure`
    take `∃ δ, Negligible δ ∧ G.FullLengthExcept δ` (full length on every coin string is not
    known to be achievable in polynomial time).
22. `uprob_adaptive_guess`, `uprob_gni_rep_cheat` (run-3 audit P10-1/P10-2): the auxiliary coin
    type (`W`, `ρ`) is assumed nonempty — `uprob` on an empty type is `0`, so the exact `2^{-m}`
    fails for `Empty`; every consumer passes a tape type `Fin k → Bool`.
23. Thms 35.1, 35.2 and Claim 38.2 (gate 03b, finding 8): the direct products are families at
    parameter `n` whose adversaries receive `1^n` (the text: `1^{n·m(n)}`, `1^{2n}`;
    interderivable, so negligibility in `n` and in `n·m(n)` coincide); Claim 38.2 runs
    `T(n) + 1 = 2n·m(n)·n^c + 1` rounds with Garg's threshold `μ₀/(2m)` (the text: `2nm²p(n)`
    rounds, threshold `1/(2m²p(n))`), with the margin `(T + 1)·2^{-n}` for the rejection-sampled
    positions.
24. `Collection.encD_decD` (gate 03b, finding 1; ruling G3-1): decoders are canonical — a string
    decodes only if it is the encoding of its value — so the outputs of the sampler and of the
    trapdoor inverter are encodings ([PS10, Defs 41.1 (2), 56.1 (6)]: "an element of `D_i`",
    "computes `f_i^{-1}(y)`"); every decoder of the library is canonical.
25. `PRG.expands` (gate 03c, finding 1; ruling G3-2): expansion at every seed length, `n = 0`
    included (Def 77.1 (2)'s `|G(x)| > |x|` read literally at `x = ε`). A `PolyExpr` stretch has
    coefficients in ℕ, so stretches with `ℓ(0) = 0` (exactly `2n`) or `ℓ(1) = 1` (`n^c`) are not
    `PRG`s, although the text uses them (the length-doubling `G` of Alg 92.1 and Thm 97.3; Lem 80.5's
    "for any polynomial `ℓ`"); `PRG.expand`/`prg_expand` take the same `hℓ : ∀ n, n < ℓ(n)`. Thm 97.3
    uses the separate predicate `DoublingPRG`, produced from any secure `PRG` by `PRG.doubling`
    (`PRG.Secure.doubling`, `Asymptotic/PRF.lean`); elsewhere `2n + 1`, `n^c + 1` are reached by
    `prg_expand` from the one-bit truncation `PRG.truncate`, and shorter outputs by truncation
    (`PRG.Secure.truncateTo_easy`/`_negligible`). Alg 92.1 needs only `n ≤ ℓ(n)`. "PRGs exist" has the
    same meaning under every reading (truncate to `n + 1` bits, change below `n₀`), and no statement
    of ch. 2–8 is vacuous by it.

---

## 6. Workstreams, ownership, coverage, build order

Every **core** item of the three inventories appears exactly once (68 + 82 + 69 = 219 ids).
Optional/deferred items are listed in §6.2 for information. Paths are relative to the
worktree. New files not in the plan's layout are marked (new).

| WS | Name | Owned files | Inventory ids covered | Depends on |
| --- | --- | --- | --- | --- |
| M1 | machine-core | `TCSlib/Complexity/Randomized/PolyExpr.lean` (new), `TCSlib/Complexity/Randomized/PPT.lean`, `TCSlib/Complexity/Randomized/NonUniform.lean`, `TCSlib/Complexity/Randomized.lean` (facade), `TCSlib/Cryptography/Asymptotic/Adversary.lean` (new) | Def-23.4, Def-23.5, Def-24.6, Def-26.8 | — |
| M2 | machine-primitives-closure | `TCSlib/Complexity/Randomized/Primitives.lean` (new), `TCSlib/Complexity/Randomized/Closure.lean` | Claim-26.3 | M1 |
| M3 | machine-repetition | `TCSlib/Complexity/Randomized/Repetition.lean` | Inf-4.3 | M1, M2 |
| S | sampling | `TCSlib/Cryptography/Asymptotic/Sampling.lean` (new) | (concrete lemmas C4, C5, C10 of inventory-ch2 §4; DQ1-A) | M1 |
| C2a | onewayfunctions | `TCSlib/Cryptography/Asymptotic/OneWay.lean` | Def-26.1, Def-27.3, Def-28.4, Thm-35.1, Thm-35.2, Claim-38.2 | M1, M2, M3, S |
| C2b | collections | `TCSlib/Cryptography/Asymptotic/Collections.lean` | Def-41.1, Thm-42.2, Def-55.1, Def-56.1, Def-78.3.coll | C2a, S |
| C2c | universal-owf | `TCSlib/Cryptography/Asymptotic/Universal.lean` | Thm-63.1, Alg-64.2, Lem-64.3, Claim-65.1, Claim-65.2 | C2a, M2, M3 |
| NT | number-theory | `TCSlib/Cryptography/NumberTheory.lean` (facade), `TCSlib/Cryptography/NumberTheory/Chebyshev.lean`, `…/Euclid.lean`, `…/ModExp.lean`, `…/Units.lean`, `…/Primality.lean`, `…/QuadraticResidues.lean` | Def-29.3, Thm-31.3, Claim-33.1, Alg-43.2, Claim-43.3, Claim-44.5, Alg-45.5, Claim-47.2, Cor-48.12, Thm-54.3, Def-49.1, Alg-49.13, Thm-49.14, Lem-50.15a, Alg-50.16, Lem-51.17, Def-57.0, Lem-57.1, Thm-58.2, Def-59.3, Thm-59.4, Thm-60.5, Cor-60.6, Claim-60.7, Claim-62.1, Claim-63.1 | S (Lem-51.17 closeness), M3 (Lem-51.17(iii) only) |
| Cand1 | candidates-factoring | `TCSlib/Cryptography/Candidates.lean` (facade), `TCSlib/Cryptography/Candidates/Arithmetic.lean` (new), `…/Concrete.lean` (new), `…/Factoring.lean` | Def-29.1, Asm-30.1, Thm-33.5, Alg-33.6, Claim-34.1, Thm-36.3, Claim-36.2, Alg-37.4, Thm-51.1 | C2a, C2b, NT, S |
| Cand2 | candidates-rsa-rabin | `TCSlib/Cryptography/Candidates/RSA.lean`, `…/Rabin.lean` | Asm-53.1, Thm-53.2, Thm-55.2, Alg-55.3, Thm-57.2, Thm-61.7, Thm-61.8, Alg-62.9, Claim-62.2, Thm-63.10 | Cand1, NT, C2b |
| Cand3 | candidates-dl-elgamal | `TCSlib/Cryptography/Candidates/DiscreteLog.lean`, `…/DiscreteLogHardcore.lean` (new), `…/ElGamal.lean` (new) | Asm-52.2, Thm-52.3, Lem-84.1, Lem-84.1.0, Lem-84.1.1, Alg-84.2, Alg-85.a, Lem-84.1.3, Lem-84.1.4, Lem-84.1.5, Asm-105.1, NT-105.a, Alg-106.2, Claim-107.a, Thm-107.3 | C2b, NT, C3a, C3f, M3 |
| C3a | ensembles | `TCSlib/Cryptography/Asymptotic.lean` (facade), `TCSlib/Cryptography/Asymptotic/Ensembles.lean` | Def-69.3, Def-69.4, Lem-71.5, Lem-71.6, Claim-73.a, Lem-73.8, Claim-73.b, Ineq-189.a | M1, M2, M3, S |
| C3b | pseudorandom-nextbit | `TCSlib/Cryptography/Asymptotic/Pseudorandom.lean`, `TCSlib/Cryptography/Asymptotic/NextBit.lean` (new) | Def-74.1, Def-75.2, Rem-75.3, Thm-75.4, Thm-75.4.c, Thm-75.4.1, Thm-75.4.2, Alg-76.5, Def-77.1 | C3a |
| C3c | hardcore | `TCSlib/Cryptography/Asymptotic/HardCore.lean` | Def-78.3, Thm-79.4, Lem-80.5, Cor-81.7, Thm-87.3, Thm-87.3.a, Thm-87.3.b, Thm-87.3.c, Thm-87.3.1, Thm-87.3.2, Thm-87.3.3, Fact-88.4, Alg-88.5, Alg-89.6, Thm-87.3.6, Thm-87.3.7, Thm-87.3.8, Thm-87.3.9, Thm-87.3.coll | C3b, C2a, C2b, M3 |
| C3d | encryption | `TCSlib/Cryptography/Asymptotic/Encryption.lean`, `TCSlib/Cryptography/ZeroKnowledge/Encryption.lean` | Def-24.7, Def-91.1, Alg-92.1, Claim-92.a, Thm-92.2, Def-93.1, Thm-94.2, Def-111.1, Thm-112.2, Thm-112.2.i, Thm-112.2.ii | C3b, M2 |
| C3e | prf-multimessage | `TCSlib/Cryptography/Asymptotic/PRF.lean`, `TCSlib/Cryptography/Asymptotic/MultiMessage.lean` (new) | Def-95.a, Claim-95.b, Def-96.1, Claim-96.b, Def-96.2, Cor-97.a, Constr-97.b, Claim-97.c, Thm-97.3, Thm-97.3.1, Thm-97.3.2, Thm-97.3.3, Alg-99.1, Thm-99.2, Thm-99.2.1, Thm-99.2.2, Thm-99.2.3 | C3c, C3d, M3 |
| C3f | publickey | `TCSlib/Cryptography/Asymptotic/PublicKey.lean` | Def-102.1, Def-102.2, Def-103.c, Thm-103.d, Def-103.e, Thm-103.f, Alg-104.3, Lem-104.a, Thm-104.4 | C2b, C3c, C3a |
| C4a | zk-model | `TCSlib/Cryptography/ZeroKnowledge.lean` (facade), `TCSlib/Cryptography/ZeroKnowledge/Interaction.lean`, `…/InteractiveProofs.lean`, `…/Defs.lean`, `…/Encoding.lean` (new) | Def-114.a, Def-114.b, Def-115.a, Def-115.b, Def-115.c, Def-115.d, Def-116.a, Def-116.b, Def-116.1, Def-117.a, Def-119.5, Def-121.1, Def-121.2, Def-122.a, Def-191.11, Inf-4.1, Inf-4.2, Inf-4.4 | M1, M2, S |
| C4b | zk-graph-isomorphism | `TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean`, `…/GraphIsomorphismZK.lean` | Def-117.e, Def-118.a, Prot-118.3, Lem-119.a, Lem-119.b, Lem-119.c, Lem-119.d, Prop-118.4, Prot-120.6, Lem-120.a, Lem-120.b, Lem-120.c, Lem-120.d, Prop-120.7, Thm-122.3, Thm-122.3.hv, Thm-122.3.trunc, Alg-123.4, Lem-123.5, Claim-123.b, Claim-123.d | C4a, M3, S |
| C4c | zk-commitment | `TCSlib/Cryptography/ZeroKnowledge/Commitment.lean` | Def-126.3, Claim-126.a, Thm-126.4, Alg-127.a, Claim-127.b, Claim-127.c, Claim-127.d | C4a, C3c, C3a |
| C4d | zk-3col-np | `TCSlib/Cryptography/ZeroKnowledge/ThreeColoring.lean` (split into `ThreeColoring/Protocol.lean` and `ThreeColoring/Simulator.lean` if > 600 lines), `TCSlib/Cryptography/ZeroKnowledge/NP.lean` | Def-124.f, Claim-125.a, Prot-127.5, Claim-127.e, Lem-127.f, Lem-127.g, Claim-127.h, Prop-127.6, Alg-128.7, Claim-128.a, Prop-128.8, Claim-129.a, Lem-129.b, Claim-129.c, Claim-129.d, Thm-124.1, Def-124.a, Claim-124.d | C4c, C4a, M3, S |
| A | audit-integration | `audits/pass-shelat/Checks.lean` (append only), facade registration in `TCSlib.lean`/`TCSlib/ComputationalModels.lean` (integrator) | — (sanity prints: `NUPPT.nonempty`, `not_strongOneWay_id`, `StrongOneWay.weak`, `Indist.refl`, `OracleEnsemble.Indist.refl`, `npProtocol_interactiveProof`, and every headline theorem) | all |

### 6.1 Build order (run 2 statement phase)

1. **M1** (serial; everything imports it) — then **M2 and M3 statements** (serial; their fills
   are the machine agent's run-4 work and may lag).
2. **S** (small; concrete) in parallel with the statement skeletons of **C2a, C3a, C4a, NT**.
3. **C2b, C3b, C4b, Cand1, C2c**.
4. **C3c, C3d, C4c, Cand2**.
5. **C3e, C3f, Cand3, C4d**.
6. **A** after each workstream lands (append its `#print axioms` lines) and at closure.

Fill-phase critical path: `pairSplitAt` → `unaryMul` → `Closure.lean` → `iterateFind`
→ {Thm 35.1, `Indist.copies`, GL, GGM, GI/3COL simulators} in parallel.

### 6.2 Optional / deferred items (not counted; for information)

Ch. 2: Def-21.x, Rem-22.1, Def-27.2, Rem-28.1, Claim-32.4, Claim-44.4, Thm-45.6, Def-46.x,
Thm-46.8, Claim-47.1, Thm-47.10, Cor-48.11, Ex-*, Def-52.1, Rem-52.2, Claim-53.1, Claim-53.2,
Claim-58.1, Thm-58.3, Claim-59.1, App-A.*, Thm-189.9, Def-191.10, Def-191.11 (ch. 2 copy);
deferred: Rem-24.2, Rem-26.2 (optional module `Randomized/Sequence.lean`), Rem-27.1, Rem-29.2,
Rem-33.2 (hypothesis in `Candidates/Arithmetic.lean`), Rem-43.6, Rem-48.2, Lem-50.15b,
Rem-49.3, Rem-50.2, Ex-58.3, Thm-188.7, Lem-189.8, Def-192.12.
Ch. 3: optional Claim-67.a, Rem-72.7, Claim-72.a, Ex-72.b, Thm-75.4.conv, Constr-77.a,
Claim-78.a, Claim-78.b, Claim-79.a, Claim-96.a, Claim-96.c, Claim-103.a, Claim-103.b,
Constr-104.a, Claim-106.a, Claim-106.b, Def-107.b, Claim-107.c, Thm-188.7, Lem-189.8;
deferred Claim-78.c, Constr-82.a/b, Constr-83.a/b, Claim-83.c, Claim-107.d.
Ch. 4: optional Def-111.a, Def-111.b, Claim-112.a, Claim-112.b, Def-117.b, Claim-117.c,
Claim-118.b, Def-119.e, Claim-122.b, Def-191.10, Def-192.12; deferred Claim-117.d,
Claim-118.c, Claim-119.f, Def-121.a, Claim-122.c, Claim-123.a, Claim-123.c, Claim-124.b,
Claim-124.c, Claim-124.e.

---

## 7. Consolidated errors and gaps in the source text

Outright errors (to replace the plan's seeded list):

**Chapter 2.**
1. Algorithm 64.2 / Theorem 63.1: `f_universal(⟨M, x⟩) = M(x)` omits the machine description
   from the output; the proof is invalid. Corrected definition outputs `⟨M, M(x)⟩`.
2. §2.6.5, `L_N`: "`N = u2^j`" should be `N − 1 = u·2^j`; the condition stated with `i = j`
   only is vacuous; intended `∀ i < j, α^{u2^{i+1}} = 1 → α^{u2^i} = ±1`.
3. Claim 32.4 is false as a strict inequality (`x = 1, p = 2`); correct form
   `p^{ν_p(C(2x,x))} ≤ 2x` (`Nat.pow_factorization_choose_le`).
4. §2.6.6 (p. 50): prime probability "exceeds `1/n`"; Theorem 31.3 gives `1/(2n)`.
5. Theorems 60.5, 61.7, 61.8, 63.10 and Corollary 60.6 need `p ≠ q` odd primes (`Π_n` contains
   2 and allows `p = q`); `Φ(pq) = (p−1)(q−1)` (p. 47) and Assumption 53.1 need `p ≠ q`.
6. Theorem 61.8 (⇐) needs square roots modulo arbitrary primes; only `p ≡ 3 (mod 4)` is proved
   (Theorem 58.2); Theorem 63.10's `Gen` needs the density of primes `≡ 3 (mod 4)` (not in
   Mathlib; explicit hypothesis).
7. Theorem 59.4: "`zinQRq`" typo; the `⇒`/`⇐` labels of the proof are swapped.
8. Theorem 52.3: `R_i = G_p`, `f_{p,g}` should be `G_q`, `f_{q,g}`; Assumption 52.2 gives `A`
   only `g^x` (needs `q, g`); `G_q` unspecified.
9. Theorem 53.2's proof samples `e ← Z_N^*` (should be `Z*_{Φ(N)}`).
10. Definition 56.1(5): `≤ e(k)` should be `e(n)`.
11. Definition 41.1(4): "p.p.t. `A`" contradicts the nuPPT convention; `f(A(1^n, i, y)) = y`
    should read `f_i`; `R_i` unconstrained; `D_i` must be finite.
12. Theorem 42.2 proof idea: "`I = {0}`, `D_0 = ℕ`" — the domain must depend on `n`.
13. §2.4.3 proof: "for each `j ∈ [1, n]`" should be `[1, m]`; the bound chain with the extra
    factor `m` is garbled.
14. Algorithm 33.6 line 7: `A(1^n, z′)` should be `A(1^{2n}, z′)`; Algorithm 37.4 must output a
    verified factor.
15. Lemma 189.8 garbled ("`1 − 2??`"), proof unfinished; Theorem 188.7's threshold `ε` should be `εn`.
16. §2.3 attack `A(z) = (2, z/2)` returns a preimage of a different input length.
17. Claim 43.3 case 2: "`b > 2^n`" should be `b ≥ 2^n`; the precondition allows `b = 0`.
18. p. 61 example `N = 77`: numbers garbled.
19. Theorem 63.1 proof: "hardness amplification from §2.3" should be §2.4; budget `|y|^3`
    becomes `(|y|+1)^3`.
20. Theorem 49.14: "with probability `1 − 2^{−t}`" should be "at least"; Lemma 50.15: "`N > 2`
    composite" should be odd composite.
21. p. 27: "NP ⊄ BPP ⟺ worst-case OWFs exist" mixes uniform BPP with non-uniform inverters.
22. Theorem 45.6 / p. 46: the remark that Euler's theorem "removes the restriction `x < N`"
    refers to a restriction Algorithm 45.5 does not have.
23. Theorem 31.3 proof: "each term is greater than 2" — the term `(x+x)/x` equals 2.
24. Theorems 61.8 / 55.2 mix `n` and `k`; Theorem 61.7 writes `Z_n^*`; Theorem 51.1's `D_i`
    uses exactly-`i/2`-bit primes while Assumption 30.1 uses `Π_n`.
25. Theorem 35.1's `m = 2nq(n)` is kept, but the uniform position of Algorithm 38.5 is not
    exactly samplable by a bit-coin PPT unless `m` is a power of two (D10).

**Chapter 3.**
26. Theorem 87.3 says `⟨x, r⟩` is hard-core "for `f`"; it is for `g(x, r) = (f(x), r)`.
27. Lemma 84.1 vs Assumption 52.2: the assumption is for prime-order `G_q`, the lemma and
    Algorithm 84.2 use `Z_p^*` (even order); `x ← Z_p` should be `x ← Z_{p−1}`; "`ε = s(n)`"
    should be `1/s(n)`; the range reduction "as we will show later" is never shown; the
    good-instance averaging over `(p, g)` is missing; the p. 86 analysis bounds
    `Pr[noinc | low]` by `1/2 − ε/2`, the complementary event of its own increment rule (`lo`
    counts disagreements `b_i ≠ half(r_i)`). (Run-3 audit P8-3: line 11's root selection is
    consistent with `half`'s convention, and the strict `half_m(x) := [2x < m]` of the
    formalization is a harmless variant, not needed by the halving invariant.)
28. Theorem 107.3 / Algorithm 106.2: El Gamal with `m ∈ Z_p^*` is insecure under DDH on `G_q`
    (Legendre symbol of `c_2`); correct with message space `G_q`; `Gen` draws `g ∈ Z_p` (may be
    `0, ±1`); the square-vs-generator sampling term `1/q` is missing.
29. Definition 75.2 quantifies `i ∈ [0, ℓ(n)]` (bit `t_{ℓ(n)+1}` does not exist).
30. Definition 78.3 mixes `k` and `n`.
31. Definition 96.1: `{O'_n} ≈ {O'_n}` typo.
32. Theorem 104.4 omits the hard-core bit from its hypothesis; its proof writes `D` for `A`.
33. Algorithm 76.5 draws `U_{ℓ(n)−1}` (should be `U_{ℓ(n)−i}`); Theorem 75.4's proof defines
    `H̃^i` with a stray `u_{l(m)}`, mixes 0/1-indexing, and its last display has `A(t) = 1` for
    `A(t) = b`.
34. Lemma 80.5's proof: `m(n)`/`ℓ(n)` interchanged; hybrids must start at `i = 0`; `M(y)` reads
    bit-then-seed against the construction's seed-then-bit.
35. Theorem 99.2's collision bound `C(q(n), 2) 2^{−n}` should be `C(q(n)+1, 2) 2^{−n}`.
36. Theorem 92.2's proof: hybrid `H²` mislabelled ("`m_1`"); gap `1/(3p(n))`, not `1/(4p(n))`.
37. Theorem 87.3's final constant: text `ε^3/(32n)` (with `ε' = ε/2`) versus the concrete
    layer's stronger `ε^3/(16n)` (the plan's seeded `ε^3/(4n)` note compares `ε'` with `ε`).
38. Lemma 71.6: the proof gives `ε/(m−1)`, the statement `ε/m` (harmless); Corollary 81.7 lists
    `ℓ(n)+1` bits.

**Chapter 4.**
39. Proposition 120.7 says "for `L_niso`"; it is for `L_iso`; its proof reverses the maps
    (`π(H) = G1`, `σ(π(H))`) and renames the graphs.
40. Definition 126.3, binding: omits `v₀ ≠ v₁`; as printed unsatisfiable.
41. Proposition 127.6's proof: "repeated `|E|^2` times" vs the protocol's `n|E|`.
42. Protocol 127.5: witness listed as `c_0 … c_m` (should be `c_1 … c_n`); Simulator 128.7:
    "`k ∈ [m] \ {i', j'}`" should be `[n]`.
43. Protocol 127.5's verifier "accepts iff `c'_i ≠ c'_j`" without checking the openings — unsound;
    undefined for `E = ∅`; `Com` on 2-bit colours has security parameter 2 (pad to `n`).
44. Theorem 122.3 claims perfect ZK for the `n`-iteration protocol; the proof covers one
    iteration and relies on §7.2.1; with bit-coin parties perfect completeness and perfect ZK
    cannot both be literal (`n!` is not dyadic); same for Protocol 118.3's `σ` and 127.5's
    colour permutation.
45. Definitions 121.1/121.2 and Proposition 128.8 bound by `e(n)` with `n` undefined
    (`n = |x|`); Definition 121.2 relies on expected polynomial time.
46. Proposition 128.8's proof: hybrid count `2n|E|` vs `n|E|` attempts; "`S̃_{e+1}` … `S̃_{e+1}`"
    typo; the `6|E|` sub-hybrid is unnecessary.
47. §4.7 step 2: "Cook's reduction applied to the witness" needs a Levin reduction (never
    defined); "execute `(P, V)` on `x'`" should be `(P', V')`; Theorem 126.4 needs a hard-core
    predicate (Theorem 87.3) and uses a single OWP, not Definition 55.1's collection.
48. Appendix B, Definition 191.11: "`R_L(x) = {y : (x, y) ∈ L}`" should be `∈ R_L`.
49. Proposition 118.4's proof uses `G1, G2` for `G0, G1`; "the prover runs in exponential time"
    is only an upper bound; the adaptive-prover argument is hidden.
50. §4.4: a round ends when the active machine *halts* ("the protocol ends"), which makes the
    literal `Pr[out_V = 0]` of Definition 116.1 unsatisfiable against a prover that halts at
    once; time complexity `t(|x|)` "regardless of messages" leaves the simulator's call to `V*`
    on long `z` ill-defined (D8 reading).
51. Definition 121.2 read literally (`∀ z ∈ {0,1}*`, the distinguisher polynomial-time in its
    input) fails for every protocol whose hiding is only computational: with `|z| ≥ 2^n` the
    distinguisher, whose input (the view) contains `z`, may run in time `2^n`, invert the OWP on
    `n`-bit inputs and open the unopened commitments. So the bound `∀ Lz : PolyExpr` on `|z|`, and
    indexing the distinguisher's advice by `|x|` rather than by its input length, are necessary,
    not only convenient (gate 03e, finding 9; `ZeroKnowledge/Defs.lean`'s module docstring).

Gaps the formalization fills (not errors): Theorem 42.2 (⇒) and Theorem 57.2 ("exercises");
the PKE single ⇒ multi-message theorem and the bitwise theorem (p. 103); Theorem 107.3
("exercise") with the `1/q` term; Lemma 84.1's range reduction and averaging; the square-root
algorithm for `p ≡ 1 (mod 4)` (restricted to `3 (mod 4)` instead); Miller–Rabin's composite
case (deferred); Chernoff (replaced by Chebyshev for pairwise independence); Theorem 112.2's
message sampler (`0^n`); Theorem 124.1's string-level Levin reduction to 3COL (hypothesis).

---

## 8. Open questions for the maintainer (everything else is decided above)

1. **Conditional candidates.** Every number-theoretic candidate theorem (Thms 33.5, 36.3, 51.1,
   52.3, 53.2, 55.2, 57.2, 61.7, 61.8, 63.10, 107.3, Lem 84.1) is stated with the hypothesis
   bundle `Candidates/Arithmetic.lean` (polynomial-time machines for binary `mul`, `add`,
   `sub`, `divMod`, `xgcd`, `modExp`, comparison, bit length, primality — the three fields
   `add`, `sub`, `size` added by the run-3 audit repair P7-1, since the generators and
   reductions of §2.9–§2.12 decrement, add, subtract modulo `N` and read bit lengths) because
   the library has no binary-arithmetic
   machines (inventory F1/F6). `#print axioms` stays clean but the theorems are conditional.
   Confirm this is acceptable as the campaign's headline form, or fund the arithmetic machines
   (research-level, ≥ 5k lines).
2. **Theorem 124.1 ("ZK for NP").** Core form (A): every `(L, R_L)` with a Levin reduction to
   3COL, the reduction being an explicit hypothesis; the "every `L ∈ NP`" form needs a
   string-level Levin reduction `SAT3 → 3COL` (the repository's is graph-level with a private
   witness map). Confirm form (A) as the headline or fund the string reduction.
3. **Rabin/RSA scope.** Rabin results restricted to Blum integers (`p ≠ q`, `p ≡ q ≡ 3 (mod 4)`)
   with the density of primes `≡ 3 (mod 4)` as an explicit hypothesis of Theorem 63.10's `Gen`
   clause; RSA and factoring assumptions restricted to `p ≠ q`. Lemma 84.1's asymptotic form
   restricts `Gen_DL` to `p ≡ 3 (mod 4)` (square roots). Confirm these restrictions.
4. **Lemma 84.1 deliverable.** The concrete statement (Classical roots, `p ≡ 3 (mod 4)`) is
   core; is the asymptotic wrapper (the hardest ch. 3 fill) mandatory for closure, or may it
   remain sorried under its sketch if the fill stalls?
5. **Optional literal modules.** `NUPPTSeq` (Def 26.8 verbatim), `exists_queryTree`
   (`OracleTM` bridge) and `NUPPT.ofPartial` are specified as optional modules with one named
   admission each; confirm they are out of the mandatory core (they are not needed by any
   chapter 2–4 theorem). **Ruled** (decision log 2026-10-27): outside the mandatory core.
   The one admission in this area is the optional bridge
   `NUPPT.decides_of_decidesWithAdviceInTime` (decision log 2026-10-28; see D11).
6. **Encoding scheme for Theorem 63.1 (run-3 audit P3-4).** `theorem_63_1` and `fUniversal_*`
   are stated for schemes with an at most exponential canonizer (`CanonizerExp c`); the only
   scheme in the library (`Turing.exists_effectiveMachineCode`) has no bound on its canonizer,
   so the headlines are conditional. Ratified as an explicit hypothesis like `ArithmeticFP`
   (D11); the open problem `exists_canonizerExp` (a `Build/`-style parser-and-reserializer
   canonizer) is stated and sorried. Confirm, or fund the canonizer construction.

---

## 9. Appendix — the 53 statement stubs of the compiled scratch (owner workstream)

M1: `polyTimeComputable_unaryPoly` (needs M2's `unaryMul`), `NUPPT.decides_of_decidesWithAdviceInTime` (optional).
M2: `computesFunInTime_pairSplitAt`, `computesFunInTime_unaryMul`, `polyTimeComputable_pairTakePoly`,
`polyTimeComputable_pairDropPoly`, `NUPPT.exists_comp`, `exists_reparam`, `exists_reparam_advice`,
`exists_withAdvice`, `exists_split`, `exists_seq`.
M3: `polyTimeComputable_iterateFind`, `iterate`, `iterateEmit`, `majority`, `pairXor`, `pairEq`, `blockMap`.
S: `distAdv_le_of_statClose`, `StatClose.prod`, `StatClose.map`, `rejectionSample_uniform_of_some`,
`uprob_rejectionSample_none`, `statClose_rejectionSample`, `permFromCoins_uniform_of_some`,
`uprob_permFromCoins_none_le` (the last two may move to C4a/Encoding).
C2a: `weak_to_strong`, `strong_prod_two`, `StrongOneWay.weak`, `not_strongOneWay_id`.
C2b: `Collection.OneWay.exists_strongOneWay`.
C3a: `Indist.toLit`, `IndistLit.toIndist`, `Indist.refl`, `Indist.symm`, `Indist.push`, `Indist.trans`,
`Indist.copies`, `predict_eq`, `prediction_lemma`.
C3b: `NextBitUnpredictable.pseudorandom`.
C3d: `singleMessageSecure_iff_zeroKnowledge`.
C3e: `toOracleAdversary_boundedBy`, `OracleEnsemble.Indist.refl`.
C4a: `StatZK.zk`, `StatZK.hvzk`, `npProtocol_interactiveProof`.
C4b: `Riso_witnessRelation`, `gi_sim_H_dist`, `gi_sim_half`, `gi_efficientProverProofErr`, `gi_statZK`.

Compile command and outcome: `lake env lean briefs/pass-shelat/DESIGN-freeze-scratch.lean`
→ exit 0, 0 errors, 53 sorry warnings (2026-10-27).

## ===== briefs/pass-shelat-ch5-8/duplication-ledger.md =====

# Duplication ledger: Pass–shelat ch. 5–8

Accepted debt, each entry acknowledged by the user, with its scheduled resolution.

| ID | New declaration (where) | Existing copy (where) | Status | Resolution |
|---|---|---|---|---|
| DL-1 | `TCSlib.InformationTheory.abs_probTrue_sub_le_statDist` (#183, `InformationTheory/Extractors.lean`, for `main`) | `TCSlib.Cryptography.abs_sum_sub_le_statDist` (`Foundations/Experiments.lean`, Garg's concrete layer, on `cryptography/pass-shelat-ch2-4` and `cryptography/garg-ch1-3`; not on `main`) | accepted 2026-11-04 (user) | No copy on `main` today. When the concrete layer lands on `main`, its lemma becomes a one-line corollary of #183's (a `Finset` test is the `Bool` test `(· ∈ T)`) or is removed. Gate 01 pack erratum E1. |

## Inherited with ch. 2–4 (found 2026-11-05; acknowledged 2026-11-05 by the user: clean up now)

This campaign owns ch. 2–4 since 2026-11-05 (plan, decision log). These duplicates predate it.

| ID | Copies (where) | Status | Proposed resolution |
|---|---|---|---|
| DL-2 | XOR of encodings is the encoding of the Boolean sum, `zipWith xor (ofFn a) (ofFn b) = ofFn (a + b)`, stated three times: `TCSlib.Cryptography.zipWith_xor_ofFn_add` (`Asymptotic/HardCoreLoops.lean`; it was `zipWith_xor_ofFn`, renamed by the base repair to end the name clash with `Encryption.lean`'s different lemma); `TCSlib.Cryptography.zipWith_xor_ofFn_eq_add` (`Asymptotic/MultiMessage.lean`); `TCSlib.Cryptography.MultiMsg.zipWith_xor_ofFn_eq_add` (`Asymptotic/MultiMessageLemmas.lean`) | accepted; scheduled now | Keep the most upstream copy (`HardCoreLoops`) and point the other two at it, in a ch. 2–4 cleanup PR. |
| DL-3 | `pairEncode a b ≠ []`, stated four times: `GGMRed.pairEncode_ne_nil` (`Asymptotic/GGMReduction.lean`), `GI.pairEncode_ne_nil` (`ZeroKnowledge/GraphIsomorphism/Proofs.lean`), `ColMachines.pairEncode_ne_nil` (`ZeroKnowledge/ThreeColoring/Machines.lean`); and, on `main`, `Complexity.pairEncode_ne_nil` (`Complexity/SpaceComplexity/Logspace/InputAccess.lean`), the copy that made the merge's ambiguity | accepted; scheduled now | `main` is merged (#186). Remove the three local copies in favour of `Complexity.pairEncode_ne_nil`, in the same cleanup PR. |
| DL-4 | Not a copy (different carriers): the sampler-based `StatClose` (`Asymptotic/Sampling.lean`) and `main`'s `EpsClose` on `FinDist` (`InformationTheory/Extractors.lean`, #183) | accepted; scheduled now | A bridge lemma, in the same cleanup PR (user, 2026-11-05). |
| DL-5 | Not a copy (different carriers; found by the gate 02 round 2 review): `Games.guessAdv_eq_half_advantage` and `Games.accept_guessGame` (games) and the concrete layer's `predict_eq` (`Asymptotic/Ensembles.lean`, on `uprob` over seed spaces), both the identity behind [PS10, Lemma 73.8] | disclosed in the docstring (gate 02 closing commit) | Derive one from the other through bridge B2 when ch. 2–4 lands on `main`. |

## Found in the ch. 5–8 statement phase (2026-11-05)

| # | Statement | Copies | Status | Resolution |
|---|---|---|---|---|
| DL-6 | The `j`-th block of `c` bits of a coin string, `(r.drop (j * c)).take c`, stated three times: `coinSlice` (`ZeroKnowledge/GraphIsomorphism.lean`, ch. 2–4), `Authentication.coinBlock` (`Authentication/Lamport.lean`, prong A), `Protocol.phaseSlice` (`Composability/SequentialZK.lean`, prong C) | found by the Lamport worker and the maintainer | Before the ch. 5–8 statement gate: one copy in a shared upstream module, with its length lemma, used by all three. |
| DL-7 | `List.ofFn (padFin ℓ w) = w` for `|w| = ℓ`: `Authentication.ofFn_padFin_of_length` (`Lamport.lean`) is the equal-length case of ch. 2–4's `ofFn_padFin_of_le` (`Asymptotic/Collections.lean`); `Composability.length_eval_of_length` (`CCA2Scheme.lean`) repeats the step inline | found by the Lamport worker | Before the ch. 5–8 statement gate: use `ofFn_padFin_of_le (le_of_eq h)`. |
| DL-8 | `SecureComputation.PRFOut ℓ₂` (prong B, `SpecialEncryptionSecurity.lean`): ch. 2–4's `PRF` with `ℓ₂(n)`-bit outputs; `PRF` is its case `ℓ₂ = n` | resolved 2026-11-05 | `prfOut_var_iff : PRFOut .var F ↔ PRF F` proved beside `PRFOut` (prong B). The ch. 2–4 layer is unchanged. |


## Found by gate 03 (2026-11-05; rulings G3-5 and R-03l-1: clean up in the gate 03 clean-up PR, after #195)

Most copies trace to helpers that are `private` in pack 03a's and 03l's files. The clean-up makes
one copy public in the most upstream file and re-points the rest.

| Id | Copies | Status | Payback |
|---|---|---|---|
| DL-9 | The coin-block bijection `blocks` (`Fin (m · c) → Bool ≃ Fin m → Fin c → Bool`) and its lemmas, six copies plus an inverse: `FunFamily.blocks`, `OneWayYao.blocksE`, `blocksEquiv`, `blocksEquivX`, `EnsembleLemmas.blocks`, `SoundnessRep.blocksEquiv`; with S2b's public duplicate `take_drop_ofFn_blocks` of `EnsembleLemmas.take_drop_ofFn_blocks` (gate 04 N4) | accepted; scheduled (G3-5) | One `FunFamily.blocks` in a low file; re-point 03h, 03i, 03k's statements and S2b's copy. |
| DL-10 | `ptc_comp` (composition of polynomial-time functions in a convenient form), six private or public copies (`Closure`/`Repetition` helpers, `Universal*`, `ThreeColoring/Machines`, …) | accepted; scheduled (G3-5) | Public once in 03a's `Closure.lean`; delete the copies. |
| DL-11 | The state loop `stateFind` (private in `Repetition.lean`) and its copies `GI.stateFind`, `EncodingMachines.polyTimeComputable_stateFind`, `GGMRed.stateLoopFun`, and the variant `stateIterate` | accepted; scheduled (G3-5) | `polyTimeComputable_stateFind` public in `Repetition.lean`; re-point; update the prose that calls it private (`StringLoops.lean:36–38`, `HardCoreLoops.lean:68`). |
| DL-12 | `abs_uexp_sub_le`, two copies (`PublicKeyLemmas` and a private one) | accepted; scheduled (G3-5) | One public copy. |
| DL-13 | `negligible_zero` (`Foundations/Negligible.lean` since G3-7a) and `negligible_const_zero` (`ZeroKnowledge/Defs.lean`) | accepted; scheduled (G3-5) | Delete `negligible_const_zero` (2 uses). |
| DL-14 | `forall_of_uprob_eq_one`, two copies | accepted; scheduled (G3-5) | One public copy. |
| DL-15 | `decodeFin_eq_some_iff`, a private copy in `Collections.lean` and a public one in `GGMReductionEval.lean` (`GGMRed.decodeFin_eq_some_iff`; making the `Collections.lean` copy public must avoid the namespace clash, gate 03b review #12c), and the new forward lemma `ofFn_of_decodeFin_eq_some` (`CollectionsHelpers.lean`, #198); S2b's private `eq_ofFn_of_decodeFin` | accepted; scheduled (G3-5) | One public `decodeFin_eq_some_iff` in `Asymptotic/Adversary.lean`; the forward lemma derived from it. |
| DL-16 | `IterateFindHost` (03l) copies 26 declarations of `main`'s private module layer in `Complexity/ClassNP/SAT.lean` (ten now public); the new host is missing from the policy's host registry (§14) | accepted; scheduled (R-03l-1: clean up in gate 03's PR) | Make `SAT.lean`'s layer public on the ch. 2–4 branch and re-point `IterateFindHost`; register the host. |
| DL-17 | `StateLoop` (03l) restates five `main` lemmas, plus `tail_poly` and `xor_poly` (arrived with the `main` merge, #186) | accepted; scheduled (R-03l-1) | Use `main`'s lemmas. |
| DL-18 | `UnaryMul` (03l) privately copies `PairSplit`'s parser | accepted; scheduled (R-03l-1) | Use `PairSplit`'s. |
| DL-19 | Not a copy yet: a latent name clash between `StateLoop.BlockLoop` and `main`'s `Complexity.BlockLoop` (nothing uses it) | noted | Rename or merge in the same PR. |
