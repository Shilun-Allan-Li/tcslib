# Pass–shelat, *A Course in Cryptography*, Chapters 5–8

Status: **draft for planning, 2026-11-04.** Nothing is started; no Lean was written. It was drafted
by the maintainer agent of the Arora–Barak ch. 3–4 campaign, at the user's (Seyoon Ragavan's)
request, to be picked up by a later session. The ch. 2–4 campaign on this branch
(`PassShelatChapter2-4Plan.md`) is Frederick Dehmel's and stays his; this plan builds on its
definitions and does not modify its files.

Companion documents, all in `briefs/pass-shelat-ch5-8/`:
- `README.md`: start here;
- `inventory-ch5-8.md`: every item of ch. 5–8, with its dependencies, prong, scope and difficulty;
- `SPINE-DESIGN.md`: the shared design (base, oracle games, two-party execution, model bridges,
  the statement phase) and the open decisions;
- `WORKFLOW.md`: how the ch. 3–4 campaign is run (roles, lifecycle, gates, replays, the local
  `exchange/` folder, overnight routines), and what carries over.

## Objective and source

Formalize Chapters 5–8 of [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes,
3rd edition, January 2010 (book pp. 133–184; Cornell CS 4830 course page):
- **ch. 5, Authentication:** MACs from PRFs; digital signatures; Lamport one-time signatures from
  OWFs; collision-resistant hash families and the discrete-log construction; hash-and-sign. The
  many-message constructions are optional.
- **ch. 6, Computing on secret inputs:** Shamir secret sharing; honest-but-curious two-party
  security; oblivious transfer from trapdoor permutations; Yao's garbled circuits. GMW is
  statement-only.
- **ch. 7, Composability:** CPA/CCA security; the CPA/CCA1 analysis of the §3.9 scheme and its
  CCA2 failure; the encrypt-then-tag CCA2 scheme; non-malleability and its relation-based form;
  sequential composition of zero knowledge.
- **ch. 8, More on randomness:** PRFs make some concepts unlearnable; PRGs derandomize BPP into
  `DTIME(2^{n^ε})`; extractors, entropy and min-entropy, the impossibility of extraction from
  efficient sources, and the leftover hash lemma (already on `main`).

Out of scope: [PS10] ch. 1 (classical ciphers, Shannon secrecy) and the appendices, which are not
requested; and the sections the notes leave as outlines (§5.9; §7.2.3–7.3).

## What ch. 5–8 need from ch. 2–4

They need ch. 2–4's **definitions**, almost never its **proofs**. The ch. 2–4 layer's 63 open
sorries (as of its last commit, 2026-10-28) block no statement here. They reach our axiom prints
only through the few results cited:
- the DL candidate, in Thm 142.3;
- the §3.9 scheme's analysis, in Thm 168.2.

The cited declarations are listed in `SPINE-DESIGN.md` §S1 and are to be frozen by agreement with
the ch. 2–4 owner.

Two facts about the base matter:
- **The ch. 2–4 head does not build.** Two duplicate public names (`zipWith_xor_ofFn`,
  `zipWith_xor_ofFn_eq_add`) are each declared twice.
- **It forked from `main` on 2026-10-08.** `main` has since gained ch7's `ClassP/BinaryArith`
  (poly-time `+ − × div mod`, modular exponentiation, gcd, Jacobi) and randomized classes. The
  first is relevant to ch. 2–4's conditional candidates; the second to Thm 180.1 here.

## Architecture: a spine, then prongs

The prongs are independent at statement level: no prong cites another prong's theorem. In
particular Thm 170.4 (CCA2) is proved from PRFs directly, not from ch. 5's MAC. They share
infrastructure, which the **spine** builds once (`SPINE-DESIGN.md`).

| Step | What | Start condition |
|---|---|---|
| **P0** (prong zero) | Shamir secret sharing (§6.1) and extractor basics (§8.3: closeness, extractors, entropy, min-entropy, `k`-sources, the leftover hash bridge) | **now**: needs nothing from ch. 2–4; lands on `main` |
| **S1** base | a building ch. 2–4 commit (ideally merged up to `main`), the frozen interface list, new directories only | the ch. 2–4 owner's fix or agreement |
| **S2** game layer | one oracle-game design: search games (forgery, collisions) and two-phase distinguishing games (CPA/CCA, non-malleability), generalizing `OracleEnsemble` | S1 |
| **S3** shared layers | two-party execution with private inputs and outputs on his `View`; `DAGCircuit.runWith` for garbling; the NUPPT ↔ BPP bridge; the learning game | S1 |
| **S4** statement phase | every core item stated with a sketch; pre-ship probes; **one external statement gate** for ch. 5–8 | S2, S3 |
| **A** authentication (ch. 5) | MAC, signatures, Lamport, CRH from DL, hash-and-sign | S4 |
| **B** secure computation (§6.2–6.3) | special encryption, garbling, OT, Yao; GMW statement-only | S4 |
| **C** composability (ch. 7) | CPA/CCA, Thm 168.2, `π′`, non-malleability, ZK sequential composition | S4 |
| **D** randomness (§8.1–8.2, Thm 183.6) | the learning lower bound, derandomization, extraction impossibility | S4 |

**Pacing.** Run two fill prongs at a time: **B** (Yao, Thm 163.7, is the longest pole) with **A**;
then **C** and **D**. A or B stalling is the cue to start C or D early. The limits are the user's
dispatch and merge attention, review capacity, and the local Lean throttle, not dependencies.

**Sizes (ESTIMATE).** There are 50 core items. ch. 2–4 averaged about 240 landed lines per
inventory item (53k lines, 219 items), heavier in machines; that density suggests 10–20k lines for
ch. 5–8.

| Part | Lines |
|---|---|
| P0 | 0.5–1.5k |
| S2–S3 | 1–2k |
| A | 2–4k |
| B | 4–8k |
| C | 2–4k |
| D | 2–4k (Thm 180.1 is machine-level) |

## Errors and gaps in the source

The inventory's notes column records each; the main ones:
- **typos:**
  - Shamir's degree should be `k − 1`, not `n`;
  - the special encryption scheme has `x` for `m`;
  - OT sends `(z₁, z₂)`, not four values;
  - `π′`'s tag covers the whole ciphertext `(r, c₁)` (the box's `c` is undefined; tagging `c₁` alone
    is insecure; erratum 2026-11-05);
  - "`c + 1`" in the CCA2 attack means a fixed XOR;
- **left as exercises:**
  - Shamir's security (Prop 154.5);
  - the OT receiver's simulator (in Prop 161.5);
  - the many-message signatures (§5.7);
- **proof sketches only:**
  - Thm 135.4, Thm 168.2, Thm 170.4, Thm 175.9 and Thm 179.1;
  - Thm 163.7 needs a composition step for the OT simulators that the notes do not state;
- **cited without proof:** Thm 165.2 (GMW) and the two-party fairness impossibility;
- **implicit assumptions:**
  - Thm 183.6 needs the extractor to be efficient;
  - Thm 175.1 assumes expected-polynomial-time simulators, while ch. 2–4's simulators are strict
    or truncated (its D8);
  - Thm 142.3's domain needs exponents below `p − 1`;
- **outline only:** §7.2.3–7.3, §5.9.

Second sources for the gaps, cited per `policy.md`: [Gol04] O. Goldreich, *Foundations of
Cryptography*, vol. 2; [KL] J. Katz, Y. Lindell, *Introduction to Modern Cryptography*.

## Coordination with the ch. 2–4 owner

These need agreement before S1 completes. Suggested points:
1. **A building commit to stack on:** the duplicate-name fix, ideally merged up to `main`.
2. **The interface list:** frozen; changes announced, especially after ch. 2–4's own external
   gate.
3. **New directories only:** requests go to him for anything missing in his layer.
4. **S2's relation to his `OracleEnsemble`** (decision D-2).
5. **The landing order:** ch. 2–4 reaches `main` first, or ch. 5–8 lands stacked behind it.

## Phasing

1. **Run 0:** P0, in parallel with arranging S1.
2. **Run 1, the spine:** S1, then S2 and S3 designed and probed. Decisions D-1…D-7
   (`SPINE-DESIGN.md`) taken.
3. **Run 2, the statement phase (S4):** every core item stated, compiling. Pre-ship probes, then
   one external statement gate; blockers and majors repaired.
4. **Run 3, the fills:** prongs A–D in two waves, each delivery reviewed and landed through a fill
   gate and a replay.
5. **Run 4, closure:**
   - a census and axiom prints;
   - lint and screens;
   - a completion record;
   - the optional and deferred items revisited.

## Risks

- **The base moves:** the ch. 2–4 statements are only internally audited, and its external gate may
  change them. Mitigation: cite few declarations, freeze them by agreement, and re-sync once.
- **The randomized-model split** (his `NUPPT` vs ch7's model on `main`) touches Thm 180.1 and,
  later, the library as a whole. Mitigation: a bridge lemma now (D-6); unification is a separate
  decision.
- **Thm 163.7 (Yao)** is the largest proof, and the notes skip its composition step.
  Mitigation: route probe before the gate, and [Gol04] §7.3 as the second source.
- **Bandwidth:** this is a third active line beside the ch. 3–4 campaign and ch. 2–4.

## Decision log

| Date | Decision | Status |
|---|---|---|
| 2026-11-04 | ch. 2–4 stays with Frederick Dehmel; the user pursues ch. 5–8 in parallel (user) | active |
| 2026-11-04 | Shape: P0 now; a short sequential spine (S1–S4) with one statement gate; then four prongs, two at a time (proposal; user asked for the inventory and spine design) | proposed |
| 2026-11-04 | Decisions D-1…D-7 open (`SPINE-DESIGN.md`) | **Superseded** by the rulings below |
| 2026-11-04 | Maintainer session picks up the line. Preflight passed: 4 CPUs, 15 GiB, about 25 GiB free; `leanprover/lean4:v4.25.0` installs; the narrowed Mathlib cache (12 roots, 2,230 files) fetches with no failure; `scripts/lean_check_tree.sh` elaborates the `InformationTheory` and `SecretSharing` chains (`briefs/pass-shelat-ch5-8/evidence/preflight-2026-11-04.log`) | record |
| 2026-11-04 | Finding: Shamir secret sharing is already proved on `main` (`TCSlib/Cryptography/SecretSharing/`, 2026-09-30): correctness, perfect privacy and the counting form, over any field with every nonzero element a party. [PS10] §6.1 is a special case. The spine design had listed it as new | record |
| 2026-11-04 | Finding: of the two "duplicate names" of the base, only `TCSlib.Cryptography.zipWith_xor_ofFn` clashes (`Asymptotic/Encryption` and `Asymptotic/HardCoreLoops`, joined by the `Asymptotic` facade). The two `zipWith_xor_ofFn_eq_add` are in different namespaces (`TCSlib.Cryptography` and `TCSlib.Cryptography.MultiMsg`): a duplicated statement, not a clash. To be confirmed by Lean in S1 | record (static) |
| 2026-11-04 | Source of record: the user uploaded the notes to this branch (`Pass–Shelat.pdf`, 3rd ed., January 2010, 204 pages, SHA-256 `7624556077a7a272ba0b3ddb7cd47b96574fb0b4b4947a25467d1f91bb61bda8`) in commit `52457d2d1b45f690d00b23f04797e7b76dcc6285`. The course host is denied by the cloud session's network policy. No text extract is committed | record |
| 2026-11-04 | **D-0** (user): ch. 5–8 records and Lean PR bases stay on `cryptography/pass-shelat-ch2-4`; records are pushed directly | active |
| 2026-11-04 | **D-0b** (user): an orphan branch `exchange/pass-shelat-ch5-8` holds the hand-off folders `outbox/`, `inbox/`, `archive/` | active |
| 2026-11-04 | **D-1** (user): P0 lands on `main` by its own PR | active |
| 2026-11-04 | **P0, §6.1** (user): main's Shamir is cited in place: docstring-only [PS10] tags and deviation notes on `SecretSharing/Defs.lean` and `Shamir.lean`, no new declarations, in the P0 PR; Frederick is told as a courtesy. P0's new Lean is the extractor basics of §8.3 | active |
| 2026-11-04 | **D-2** (user): the S2 game layer becomes a common base, and Frederick's `OracleEnsemble` is restated over it. This edits his PRF files, so it needs his agreement (S1 note) | active, needs Frederick |
| 2026-11-04 | **D-3** (user): Thm 144.1 is core for messages of length `≤ p(n)`; the unbounded form is optional | active |
| 2026-11-04 | **D-4** (user): optional, deferred and statement-only items as in the inventory | active |
| 2026-11-04 | **D-5** (user): the learning game of Def 179.a and Thm 179.1 is built as PAC learning in `TCSlib/LearningTheory`, not a crypto-style game | active |
| 2026-11-04 | **D-6** (user): a one-way bridge lemma (a `polyTimeModel` BPP verifier gives a NUPPT running it, input hard-wired as advice); Thm 180.1 is stated against main's `InBPP` and `DTIME`. Prong D needs a base that includes `main` | active |
| 2026-11-04 | **D-7** (user): Claude for all fills | active |
| 2026-11-04 | P0 opened as [Shilun-Allan-Li/tcslib#183](https://github.com/Shilun-Allan-Li/tcslib/pull/183) (branch `cryptography/pass-shelat-ch5-8-p0`, head `789cf450527ff6b8c779161e555f04093080b88d`): `InformationTheory/Entropy.lean`, `Extractors.lean`, and [PS10] docstring citations on `SecretSharing/Defs.lean` and `Shamir.lean`. Maintainer checks: an 18-module replay into a fresh olean tree (0 errors, 0 warnings, 0 sorries); axioms standard for all 25 printed; style lint clean on the new files. Its gate is pending | active |
| 2026-11-04 | Duplication note: `EpsClose` (on `FinDist`, #183) parallels Frederick's sampler-based `StatClose` (`Asymptotic/Sampling.lean`, ch. 2–4 only). Not a copy (different carriers); a bridge lemma is owed at the integration of ch. 2–4 with `main` | record |
| 2026-11-04 | S1 note to Frederick drafted (`briefs/pass-shelat-ch5-8/S1-note-frederick.md`); for Seyoon to forward | **Superseded** by the next row |
| 2026-11-04 | The S1 note approved as drafted; Seyoon forwards it (user) | active, awaiting Frederick |
| 2026-11-04 | P0's gate: one combined external gate (statements and proofs together), since #183 has no sorry (user) | active |
| 2026-11-04 | Gate 01 staged: pack and evidence at `briefs/pass-shelat-ch5-8/gates/01-p0/` (`f2653ee20ff0b915fbe40f12fbf90b3af481bc5b`); bundle `exchange/pass-shelat-ch5-8:outbox/gates/01-p0-gate/gate01-p0-bundle.md` (19 sections, SHA-256 `97042aee164fa0e11a0ac1c2bd2f28a5398349a76934f7eee0bd30bb138bf74b`); the auditor also gets the PDF. Replay on #183's head: 18/18 | **dispatched** 2026-11-04 (user); findings awaited as `gate01-p0-findings.md` |
| 2026-11-04 | Security games reviewed (user asked). Finding: ch. 2–4 expresses each notion by hand (fixed functionals `invProb`/`predProb`/`acceptProb`/`distAdv`, one deterministic oracle with a Boolean output, a decoder per notion), which does not reach ch. 5–8's randomized and stateful oracles, oracle families, phases and transcript predicates. A general framework is proposed for S2; its form is under discussion | open |
| 2026-11-04 | **Protocols unified** (user): the S2 framework also carries two-party protocols (secure computation, ZK composition), each party an oracle computation whose oracle is the other's next-message function. This touches how Frederick's ZK layer (`Strategy`, `View`) is read, so it joins D-2 in the S1 agreement | active, needs Frederick |
| 2026-11-04 | **Duplicate DL-1 accepted as debt** (user): `abs_probTrue_sub_le_statDist` (#183) and the concrete layer's `abs_sum_sub_le_statDist`; resolved when that layer reaches `main` (`briefs/pass-shelat-ch5-8/duplication-ledger.md`) | active |
| 2026-11-04 | External code examined for comparison only (nothing taken): VCVio (github.com/dtumad/VCV-io) at `9054989327a7185ff19ef9ff0f119cccea479501`, Apache-2.0; Lean 4.35.0 with Mathlib v4.35.0. If S2's design is adapted from it, `policy.md`'s design-adaptation citation applies | record |
| 2026-11-04 | **S2 framework** (user): home-built at TCSlib's pins, **adapting VCVio's design**: indexed oracle specs, a free monad of oracle computations, stateful logging handlers. VCVio **must be cited** (user) per `policy.md` §2, in every S2 module's `## References` and in design documents: the block is fixed in `briefs/pass-shelat-ch5-8/design/CITATION-VCVio.md`. Kept from TCSlib: `NUPPT` efficiency, finite-seed `uprob` probability, Garg's `QueryTree`/`simulate`/lazy sampling. Not a dependency: Lean 4.35 vs 4.25, a cost-model PPT, measure-valued probability | active |
| 2026-11-04 | S2 design note drafted (`briefs/pass-shelat-ch5-8/design/S2-game-framework.md`); S3b's Yao route probed (`design/S3b-yao-runWith.md`); S3a folded into S2 | record |
| 2026-11-04 | **R-1** (user): sampling is an oracle inside the monad (`unifSpec`, after VCVio), with `Pr` a finite sum; a bridge proves `Pr` equals `uprob` for fixed-shape games | active |
| 2026-11-04 | **R-2** (user): S2's generic lemmas reuse Garg's concrete-layer results through bridges B1/B2 where they fit; only what has no counterpart is proved fresh | active |
| 2026-11-04 | S2 probes: P-S2-1 passed (monad, sampling oracle, finite-sum `Pr`, `invProb` = Pr of a one-line game); P-S2-3 passed in part (stateful fresh-coin oracles, `simulate`, logging proved conservative, IND-CPA for Alg 99.1 as a program, the bad event as a log predicate; the hop itself waits for §5's lemmas) | record |
| 2026-11-04 | S3c: a scratch merge of `main` into Frederick's last Lean commit (never pushed) gives two trivial textual conflicts (`Complexity/Randomized.lean` and `ComputationalModels.lean`) and no new full-name clash. **Correction to the S1 note's point 5**, which named one file. The bridge's statement shape is in `design/S3c-bpp-bridge.md` | record |
| 2026-11-04 | S3d PAC design drafted (`design/S3d-pac-learning.md`); S2 probe P-S2-4 passed in part (two-party execution; an exchange answers `Option`, `none` once the other party has returned); S1 addendum drafted (`S1-note-frederick-addendum.md`) | record |
| 2026-11-04 | **R-3** (user): the information-theoretic PAC layer (`TCSlib/LearningTheory/PAC/`) lands on `main` by its own PR with its own gate, written after S2 settles; its efficient part and Thm 179.1 stay with prong D | active |
| 2026-11-04 | **Gate 01 closed** (#183): round 1 reported 0/0/7/3 (`gates/01-p0/gate01-p0-findings.md`); a review sub-agent confirmed 8 findings, partly confirmed 2, moved #5 to note, and added M1–M4; every minor and the optional items swept in the closing commit `16e2bd02fac1a4656a736b3f0de128e148e60e8c` (docstrings, plus six `rfl` interface lemmas); re-verified on that head: replay 18/18, 31 standard axiom prints, docstring-only on the Shamir files, lint clean. Errata E1 and E2; backlog in `gates/01-p0/resolutions.md` | closed |
| 2026-11-04 | **Spine revisited** (user asked whether spine-then-prongs still fits). Maintainer's assessment: the shape holds (prongs independent at statement level; shared infrastructure real; P0 worked), but S2 is now the largest piece and the main risk, one gate for 50 items is too coarse, and Thm 180.1 is a second long pole that barely uses S2 | record |
| 2026-11-04 | **S2 placement** (user, against the recommendation to put the core on `main`): **all of S2 stays on `cryptography/pass-shelat-ch2-4`**. Consequence: the PAC basics on `main` (R-3) do not use S2; the bridge from PAC's prediction game to S2's example-oracle game moves to prong D on the branch | active |
| 2026-11-04 | **Gating** (user): the single statement gate is **superseded**. S2a (the framework core) and S2b (bridges B1–B5, machine layer) each get an API gate (definitions plus proved lemmas); then each prong gets its own statement gate before its fills | active |
| 2026-11-04 | **Prong order** (user): Yao (B) and Thm 180.1 (D) first; Thm 180.1 starts once `main` is merged into the ch. 2–4 base, independently of S2. Then A with C; Thms 179.1 and 183.6 whenever convenient. **Supersedes** the plan's "A with B, then C with D" | active |
| 2026-11-04 | **S2a written and opened** as [Shilun-Allan-Li/tcslib#185](https://github.com/Shilun-Allan-Li/tcslib/pull/185) into this branch (head `597eef43ccd3c8bfafe0c0c16a2444b12adc1644`): `TCSlib/Cryptography/Games/` (six modules and a facade, 1,325 lines). Every lemma is proved, including identical-until-bad and simulation composition; replay 8/8; 68 standard axiom prints; lint clean. `Games.distAdv` renamed `Games.advantage` (ambiguous with the concrete layer's `distAdv`). Gate 02 (API) staged: bundle `eb9c1c44a45363a793325ad5f5aa69c2cb78b5972c4e6e0aa96e0172733adf05` | **dispatched** 2026-11-04 (user); findings awaited as `gate02-s2a-findings.md` |
| 2026-11-04 | **S2b in progress** on `cryptography/pass-shelat-ch5-8-s2b` (stacked on #185, head `063c2fb975e405ac49207c4dd1e00002f1c96fe2`). B1 (`QueryTree` ≃ one-oracle computations) and B2 (the concrete experiments as games) are proved; the B3 decoder (`NUPPT.toComp`; `toOracleAdversary` is its one-oracle instance) is proved. 18 theorems, all with standard axioms. The PRF closure (90 of Frederick's modules) was bootstrapped on the VM; one of his modules (`NonUniform`) carries an open sorry that nothing of ours reaches. The efficiency route is in `design/S2b-efficiency.md` (iteration via `polyTimeComputable_iterate`) | in progress |
| 2026-11-05 | **Efficiency result** (user asked to look for a relative first): Frederick's GGM reduction machine (`Asymptotic/GGMReduction*.lean`) already runs a next-query machine under a stateful polynomial-time handler in a state loop; its `stateLoopFun`, `stateLoopFun_poly` and `stateLoopFun_eval` are generic. `exists_queryChain_nuppt` is a non-adaptive special case; `main`'s `POracle_eq_P_of_mem_P` is a different machine model. **Ruled (user):** a Claude fill brief on GGM's pattern (reuse the loop lemmas verbatim, abstract the answer step, add log replay for reductions that are oracle machines), staged after gate 02 closes. GGM becomes an instance at integration (new coordination point F-4); the near-duplication goes in the ledger until then | active |
| 2026-11-05 | **Gate 02 round 1** (#185): 1 blocker, 3 majors, 6 minors, 2 notes (`gates/02-s2a/gate02-s2a-findings.md`). The review sub-agent found 11 true and 1 partly true, with no severity change (`gates/02-s2a/review/subagent-review.md`). The gate does not close; repairs, then round 2 | open |
| 2026-11-05 | **G02-#1 execution semantics** (user): D8's reading. The waiting party gets one final activation, may draw coins, and a send after the end is reported (`sentAfterEnd`), not hidden; the outcome has three cases; early returns are allowed; fuel counts messages. To be confirmed with Frederick under F-2 (B4 must match his `Protocol.exec`) | active |
| 2026-11-05 | **G02-#4 simulators for Thm 175.1** (user): strict or truncated simulators, a declared deviation carrying D8 into ch. 7: ZK ⇒ ZK; statistical δ ⇒ Qδ; `PerfectZKAbort` ⇒ statistical with error Q·2^-k. No framework change. The debt was recorded in `inventory-ch5-8.md` (Thm 175.1 row) | active |
| 2026-11-05 | **G02-#10** (user): `advantage_hybrid` becomes a corollary of Frederick's `abs_sub_le_sum_hybrids` (importing `Foundations/Probability.lean`), with the existential form of [PS10, Lemma 71.6] added. No debt | active |
| 2026-11-05 | **Merge `main` into `cryptography/pass-shelat-ch2-4`** (user, ruled: prepare the PR and merge now, without waiting for Frederick, who reconciles any local work himself). It unblocks prong B (uniform circuits) and Thm 180.1 (randomized classes); see `design/bridges-to-complexity.md` | active |
| 2026-11-05 | **Merge, refined** (user): replay first, then the PR. If something breaks, the maintainer reports exactly what, and the fix goes to Frederick | active |
| 2026-11-05 | **Merge replay** (`evidence/merge-main-2026-11-05/`): the merge `87b5b37c6f21fcea58f9274a519b1d530d83c257`, 418 modules, 406 pass and 12 fail. Three fail on the known `zipWith_xor_ofFn` clash. Nine are merge-caused: main's `Complexity.pairEncode_ne_nil` makes 7 bare uses in Frederick's `ThreeColoring/ProtocolProofs.lean` ambiguous (it opens `Complexity` and `ColMachines`). A scratch probe, reverted, shows that qualifying them leaves only the pre-existing clash. Fix request F-5 to Frederick (`S1-note-frederick-addendum-2.md`, superseded: F-5 is now this campaign's, in the base repair) | active |
| 2026-11-05 | **Finding: policy-lint debt in ch. 2–4.** `scripts/style_lint.py` over the 93 files of the asymptotic layer reports 20 findings, all in `ZeroKnowledge/ThreeColoring/`: 13 proofs without a **Proof sketch.**, 4 public theorems without a docstring, 3 module docstrings missing `## Main definitions`. Frederick's run-2 record said the lint was clean; the findings came with the later fills. They are to be swept with the 3-colouring fills (pack 03g), before the `main` landing. The gate 03 staging script reports them per pack | active |
| 2026-11-05 | **Gate 02 closed** (#185). Round 2 reported 0 blockers, 0 majors, 6 minors and 2 notes. A review sub-agent confirmed all of them and added 4 small items, all swept in the closing commit `a120c71567cda016ab1b8e0d35f8b99eca0082dc`. #185 then merged the current base, giving `cdf78da1acc2f5814147b358dec9bf5325999d52`, which was re-verified there: replay 9/9, all 75 public theorems on standard axioms, lints clean, name screen clean. The [Sho04] location is the auditor's direct reading, not re-verified from this session. The trace invariants (note 5) are scheduled with B4. Records: `gates/02-s2a/resolutions-r2.md` | closed |
| 2026-11-05 | **Landing order: ch. 2–4 first** (user; S1 note, point 6). Once gate 03 closes, one integration PR to `main` carries Garg's concrete layer, the ch. 2–4 asymptotic layer and the `Games` framework, with any unfilled `sorry`s as named admissions under their sketches (as policy allows). The ch. 5–8 prongs follow, in batches as their gates close | active |
| 2026-11-05 | **[PS10]'s text: follow `policy.md` §2** (user). This lifts the brief's "do not commit the source's text" rule for [PS10]. The PDF moves under `blueprint/src/references/`, and the dataset pipeline (`scripts/dataset_pipeline.py`, `scripts/sources.py`) ingests it as a reference pair (`.raw.md` + `.md`) covering ch. 2–8. That pair replaces Frederick's partial ch. 2–4 extracts, and the blueprint can then cite it with `\statementsource` **When** (follow-up ruling, user): at the ch. 2–4 → `main` integration. The references stage includes a paid model clean-up (`scripts/sources.py add PS10=<pdf>`, references stage only, never the pipeline's `--build`); until then the branch keeps Frederick's partial extracts | active |
| 2026-11-05 | **Protocols: his strategies define, the framework proves** (user; item F-2; narrows "protocols: unify too"). The definitions stay Frederick's: `Strategy`, `View`, `Protocol` and `exec` (D8) define IP and ZK, and ch. 5–8's protocol notions (Def 155.1, Thm 175.1) are stated over them. `Party` is the proof calculus. Bridge B4 proves that a strategy's execution equals the `Party` execution of its embedding, where the embedded party samples its full tape first (round 2 findings 1–2). Gate packs 03e, 03g and 03k audit the definitions that stay | active |
| 2026-11-05 | **Oracle adversaries, restated at the root** (user; refines D-2, item F-1). There is one notion of oracle computation: the concrete layer's `QueryTree` becomes the one-oracle `Games.OracleComp` (an abbreviation, its constructors kept as definitions), and `OracleEnsemble.Indist` is stated with the framework's adversaries, with `NUPPT.toOracleAdversary` as an instance of the generic decoder `NUPPT.toComp`. Bridges B1 and B3 become the proofs that the meaning is unchanged. About 9 files (`OracleAdversary`, `LazySampling`, `SubHybrids`, `GGM`, `PRF`, `GGMReduction*`, `MultiMessage*`); `QueryTree` moves to universe 0. **When:** after gate 02 closes, before gate pack 03d is dispatched. 03d waits; the other packs go | active |
| 2026-11-05 | **Ch. 2–4 completion, rulings** (user). **Order: interleave.** The base repair and the `main` merge go first; the ch. 2–4 statement gate next; the fills of the 63 `sorry`s as Claude fill briefs (D-7), alongside the ch. 5–8 prongs. **Gate: full, interface first.** An external statement gate in several packs: first what ch. 5–8 cites (the S1 note's interface list), then the sorried statements before their fills, then the rest. **Candidates: fill them.** All 57, scope unchanged (under the arithmetic-hypothesis bundle), each after its audit pack closes, discrete log first (ch. 5–8 cites it in Thm 142.3) | active |
| 2026-11-05 | **Ch. 2–4 ownership** (user): Frederick Dehmel no longer works on `cryptography/pass-shelat-ch2-4`. This campaign is responsible for its fixes and its outstanding content. It supersedes the rule "never edit his files": his files are edited through PRs the user merges, like any other `.lean` change. The S1 note and both addenda are superseded, never sent. Their requests (point 1, the build; F-1 to F-5) become this campaign's work items. His frozen decisions D1–D11 (`briefs/pass-shelat/DESIGN.md`) are inherited and are changed only by ruling | active |
| 2026-11-04 | **#183 merged** into `main` (user) at `7d36bbc27dfabd4988ee1702bc342049a1f3e006`: P0's extractor basics and the [PS10] citations on Shamir are on `main` | done |
| 2026-11-05 | **Dedup PR opened**: [Shilun-Allan-Li/tcslib#192](https://github.com/Shilun-Allan-Li/tcslib/pull/192), `c7d5a6e22dfd48b603e57fc2def3b470ba170249` (DL-2, DL-3, DL-4). Replay 756/756; all 170 ch. 2–4 closure modules confirmed; the closure's `sorry` census is 80 (the 63 inherited, plus 17 in `main`'s machine layer). The 291 headline axiom prints are identical to the pre-merge print, so `main`'s machine-layer sorries reach no ch. 2–4 headline (`evidence/dedup-2026-11-05/`) | active |
| 2026-11-05 | **Finding and fix: Algorithm 99.1's `Dec` read malformed ciphertexts through `E` off its domain**, where `E` is unconstrained, so Thm 168.2's CCA1 half was false for some evaluators (found while stating prong C). The fix, [Shilun-Allan-Li/tcslib#193](https://github.com/Shilun-Allan-Li/tcslib/pull/193) (`2f8ac2114c3c8feecfeef7a4e8d3519e3a9c9ad7`, stacked on #192): `Dec` refuses ciphertexts that are not pairs of `n`-bit strings. Headline prints unchanged (`evidence/dec-guard-2026-11-05/`). Maintainer's call, as the faithful reading of the source's domain | active |
| 2026-11-05 | **Erratum: `π′`'s tag covers `(r, c₁)`**, not `c₁` (inventory Alg-169.3 corrected). Tagging `c₁` alone is not CCA2-secure: `Dec′(r*, f(r₁), t₁)`, built from the challenge and an encryption of `0^n`, reveals `f(r*)`. The source's proof tags the whole §3.9 ciphertext; with a length-preserving family, its `2n`-bit input takes a `2n`-bit key. Prong C states `π′` this way | active |
| 2026-11-05 | **Public-key games: pad to a fixed length** (user). The oracle codec stays fixed-length, as T1 needs. A generic wrapper pads any scheme's ciphertexts, with an end marker, to a polynomial bound taken from the machines' time bounds; the padding is invertible and correctness is proved. Claim 172.a is stated for padded Algorithm 104.3. S2b and gate 04 are untouched (rejected: bounded-length oracles, which would change the codec and T1; a fixed-length hypothesis on the trapdoor collection) | active |
| 2026-11-05 | **Non-malleability (§7.1.5–7.1.6): follow [PSV06]** (user). Finding: Theorem 174.8 is not true as written. Definition 173.7's simulator gets no public key, so an adversary that outputs a fresh `Enc_pk(0^n)` hits `R(m) = {0^n}` with probability ≈ 1, which a simulator without `pk` cannot match; and the quantifiers of Definitions 172.6 and 173.7 do not line up (adaptive `m₀, m₁` against a fixed `m`, with `ε` uniform over `m` and `z`). Definition 173.7 and Theorem 174.8 take the forms of Pass, shelat, Vaikuntanathan (CRYPTO 2006), cited as a second source. Definition 172.6 keeps the source's adaptive form, without its stray "for all `m₀, m₁`" | active |
| 2026-11-05 | **Prong C statements so far** (branch `cryptography/pass-shelat-ch5-8-prong-c`, head `61c06756ec62a2057fbee8f8a4a183f2b7befecd`): Def 168.1; Thm 168.2 (CPA, CCA1); Claim 169.a (an adversary with advantage 1; "not CCA2" proved from it); `π′` with correctness, and Thm 170.4; Def 171.5 by canonical padding, and Claim 172.a (proved from a stated single-bit ⇒ CPA lemma and Thm 104.4); Def 172.6 and Thm 175.9; the sequential repetition `seqRep` and Thm 175.1 (by a worker). Def 173.7 and Thm 174.8 wait for [PSV06]: the session's network policy refused `shelat.khoury.northeastern.edu` and `www.iacr.org` | record |
| 2026-11-05 | **Finding (Thm 175.1, by the worker; checked by the maintainer):** under D8, `Strategy.Efficient` bounds each activation by its own input, so a cheating verifier can double its messages every phase. With an honest prover that echoes it (ZK for one run), the composed views grow like `2^Q`, so ZK of the repetition is false as worded. The ch. 2–4 docstring already records the weakness (run-3 audit P9-1). Repair: the statements assume `Protocol.ProverBounded R B` (honest prover messages of at most `B(|x|)` bits), which keeps the views polynomial. Soundness of the repetition needs `1 ≤ Q(n)` | active |
| 2026-11-05 | **Finding and repair (prong A, Def 140.1's encoding):** with fixed-length domains, Thm 142.3 was false: `n`-bit exponents give the trivial collisions `x`, `x + (p − 1)`. `CRH` now carries membership tests for `D_i` and `R_i`; compression `|R_i| < |D_i|` becomes the property `CRH.Compresses` that Thm 142.3 asserts (from a threshold on, D10); the collision game requires `x, x' ∈ D_i` | active |
| 2026-11-05 | **Lamport (prong A, by a worker):** Prot 137.1 with correctness proved, and Thm 137.2 stated over `FunFamily.StrongOneWay` (commit `f25247675cb52e2101013de491bb9e47c11d2465`). `Ver` checks lengths before evaluating `f`, so the evaluator is never run off its domain. Minor source notes for the inventory: p. 137's `Ver_pk(σ, m)` argument order; `Ver_sk` for `Ver_pk`; p. 138's "greater than" for "at least". Duplication-ledger items DL-6 and DL-7 opened | record |
| 2026-11-05 | **Overnight progress (maintainer):**<br>• **Prong A core statements complete** (`cryptography/pass-shelat-ch5-8-prong-a`, `2d7b5441`): Defs, Thm 135.4, Lamport and Thm 137.2, the DL hash and Thm 142.3 (with the `CRH` domain repair), hash-and-sign and Thm 144.1 (with its existential corollary, proved).<br>• **T2 stated on S2b** (`afe5982f`; the interactive handler).<br>• **The PAC layer's PR to `main`**, [Shilun-Allan-Li/tcslib#194](https://github.com/Shilun-Allan-Li/tcslib/pull/194).<br>• **Prong B started:** Def 155.1 and the OT functionality, `1f8d0c1b`.<br>• **Prong D started:** Thm 183.6, `2d8652d7`.<br>• **Replays running:** gate 03 at the merged head `a3c5fa8b`, and S2b after its base merge.<br>• **Hash-and-sign finding:** Thm 144.1 needs a full-domain CRH. The CRH game counts only in-domain collisions, so a CRH constant off a small domain would break it | record |
| 2026-11-05 | **Prong B, OT** (by a worker, `d631ea8586483153883b88b5540d44501dc91121`): Prot 160.4 with five messages (D8's output convention needs two trailing empty moves), correctness proved (Bob outputs `[a_b]`, Alice `[]`), both simulators built as NUPPTs, Prop 161.5 stated. **Finding:** Prop 161.5 needs the collection's sampler to output canonical encodings (`SamplerCanonical`). The decoder is total and may accept non-canonical strings, and from those Alice could tell Bob's raw `y_{1−b}` from his canonical `y_b`. **Note:** `HBCSecure` does not require the honest parties to be efficient (a protocol of the course is PPT); to be decided before Yao's theorem (a `Protocol.Efficient` side condition) | active |
| 2026-11-05 | **Prong B, garbling** (by a worker; `f6c8b752`, `3066d813` on `…-prong-b`):<br>• **Alg 157.2 on strings, correctness proved.** `Dec` checks lengths before evaluating `E`.<br>• **Construction 158.a over an abstract multi-key encryption,** with `runWith_sim` ported from the S3b probe.<br>• **Claim 159.a:** its deterministic part is proved (a good garbling evaluates to the key of `C(x)`); its probabilistic part is stated (`Pr[¬Good] ≤ 12·|gates|·δ`, using `IsFaninTwo`).<br>• **The nested special encryption** as the garbling's encryption, correct.<br>• **Deviation:** `Good` asks for correct opening under every assignment, which the union bound needs.<br>• **Still to compile:** Claim 157.a and the security wrapper. Their upstream build hit the background time limit; the maintainer resumed it | record |
| 2026-11-05 | **Prong D, derandomization** (by a worker; `8c09cc00ee6df9d224bc1010046b8771759094a0`):<br>• **The S3c bridge, proved:** `verifier_toNUPPT` (a `main` BPP verifier, input hard-wired as advice, is a NUPPT); `randProb_eq_uprob`; `polyLenExpr`.<br>• **Thm 180.1 stated** (`bpp_subset_dtime_subexp`): `(∃ G, G.Secure) → 0 < ε → BPP ⊆ DTIME(⌈2^{n^ε}⌉)` over `main`'s `InBPP polyTimeModel` and `DTIME`, with real `ε`; checked true as written.<br>• **Clean tree:** prong D's olean tree was rebuilt from scratch (326 modules, all pass).<br>• **Thm 179.1 merged into prong D** (with the PAC layer); its closure is building there | record |
| 2026-11-05 | **Q-1 ruled (user): keep D8; Thm 175.1 assumes `Protocol.ProverBounded`.** No ch. 2–4 change. Gate 03e's pack (already staged, bundle `a01c936f…`) still calls the point "queued as Q-1"; its question to the auditor stays as an advisory check, so the bundle is not restaged | ruling |
| 2026-11-05 | **Q-3 (user): not yet.** The merged-away branches `…-prong-c-seqcomp` and `…-prong-d-learn` stay | ruling |
| 2026-11-05 | **Q-4 ruled (user): the PAC layer (#194) is gated before it lands on `main`.** Gate 05 staged: the pack is ready, and the maintainer's lint rerun at `44d27f39` gives 0 findings (`gates/05-pac/evidence/lint.log`) | ruling |
| 2026-11-05 | **[PSV06] and [PSV07] received (user uploads; not committed, being publisher copies).** [PSV06] = Pass, shelat, Vaikuntanathan, *Construction of a non-malleable encryption scheme from any semantically secure one*, CRYPTO 2006, LNCS 4117, pp. 271–289 (SHA-256 `7b470f4e3f26a56dbfd8956d4f07201ac163cbf716d4c0830b375ac022db8c49`). [PSV07] = the same authors, *Relations among notions of non-malleability for encryption*, ASIACRYPT 2007, LNCS 4833, pp. 519–535 (SHA-256 `c899bf7cff4c8144ac28c31f703d567178f96e31ec9b28d6f4bddf4f337ea57d`).<br>• **Correction to the PSV06 row above:** [PSV06] has only the indistinguishability form (its Def 3; Def 4 and Thm 1 are many-message). The simulation form that Def 173.7 needs, and Thm 174.8's equivalence, are in [PSV07].<br>• **Def 172.6 checked against [PSV06, Def 3]:** our `nmGame` at CPA is that definition (the adversary picks `m₀, m₁` after `pk`; `D` sees only the decryptions; a copy of the challenge and an invalid ciphertext are both `⊥`; `ℓ` is any polynomial). [PSV07, Def 3] (IND-NME′) is its many-message form.<br>• **[PSV07]'s results that bear on Thm 174.8:** SIM-NME′ (Def 1; invalid outputs allowed; the simulator gets `pk`; the adversary outputs a message sampler; a history function `h`) equals IND-NME′ **under CPA** (Thm 3), and is **strictly stronger under CCA1 and CCA2**, even for a single message (Thm 4). It always implies IND-NME′ (Cor 1). The proofs of Thm 3 and Cor 1 are deferred to the paper's full version, which we do not have.<br>• **Consequence (within the ruling):** Def 173.7 takes [PSV07, Def 1]'s form at one message (`ℓ = 1`, the source's single `m`). Thm 174.8 is stated as the CPA equivalence, plus the direction SIM ⇒ IND for every attack. Its proof sketches are the maintainer's, flagged for gate 06 | finding |
| 2026-11-05 | **Prong C complete in the statement phase** (`cryptography/pass-shelat-ch5-8-prong-c`, head `aa71d0e784a84c68172895fd5db79a253fba79c9`). New `Composability/SimNonMalleable.lean`: `MsgSampler`, the real and ideal experiments `snmReal`/`snmIdeal`, `SimNMSecure` (Def 173.7 as [PSV07, Def 1] at one message), `nmSecure_of_simNMSecure` (every attack; `sorry`), `simNMSecure_of_nmSecure_cpa` (`sorry`), and `simNMSecure_cpa_iff_nmSecure_cpa` (Thm 174.8 under CPA, from the two). **Declared deviation:** [PSV07]'s `A₁` outputs a sampler machine; here a sampler is quantified with `A` and `A₁` outputs its parameter (with a universal clocked sampler, [PSV07]'s form). `NonMalleable.lean`'s source notes now cite [PSV06, Def 3] for Def 172.6. Checks: both modules pass `lean_check_tree.sh` (tree `seqcomp-oleans`, from identical sources at `61c06756`, now prong C's tree); lint 0 findings | record |
| 2026-11-05 | **Q-5 ruled (user): option 1, the OT-hybrid model first.** Yao (Prot 162.6) is stated with an ideal OT for Bob's keys, Thm 163.7 in that model (garbling simulator, Claims 157.a and 159.a); separately, [Gol04] §7.3's composition theorem for honest-but-curious protocols, from which the real protocol's security (bitwise OT of Prot 160.4 per key bit) is a corollary | ruling |
| 2026-11-05 | **Efficiency of honest-but-curious protocols ruled (user): insist on polynomial time, in the definition.** `HBCSecure` requires both parties `Strategy.Efficient` and every message of every honest execution at most `B(n)` bits for a polynomial `B` (the style of Thm 175.1's `ProverBounded`). Rejected: the textbook `ReadsPrefix` machines (OT's strategies would need rewriting to truncate), and efficiency in the theorems only | ruling |
| 2026-11-05 | **Gate 03: packs 03a, 03b, 03c and 03e dispatched by the user** (the interface packs). Gate 04 was dispatched earlier the same day | record |
| 2026-11-05 | **Prong B, Yao under way** (design `design/S3b-yao-hybrid.md`). Maintainer: the efficiency ruling in `HBCSecure` (`Functionality.PolyTime`; `otProtocol_polyTime` stated; prong B `e6bc92ed`), and `SecureComputation/Hybrid.lean`, the hybrid model with ideal calls first (`1cf007d1`). Both pass `lean_check_tree.sh`; lint 0. Two workers in parallel, on separate worktrees and olean trees: `Compose.lean` (the composition operator and [Gol04, Thm 7.3.3]) and `Yao.lean` (Prot 162.6 and Thm 163.7 in the OT-hybrid model; row order by a random XOR-shift, a declared deviation). The real protocol's theorem follows by term once both land | record |
