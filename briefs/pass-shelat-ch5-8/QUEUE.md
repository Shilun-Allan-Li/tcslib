# Queue for the user (overnight, 2026-11-05)

Items that need you, newest last. Work that does not depend on them continues meanwhile. Each
question gives the options, with the recommended one first.

## Q-1. Thm 175.1 and the efficiency of verifiers — **ruled: option 1** (2026-11-05)

**Context.** Frederick's `Strategy.Efficient` (D8) bounds each activation's time by its own input,
received messages included. His own docstring (run-3 audit P9-1) notes that this does not bound a
party's work in `|x|`. The consequence:
- a cheating verifier can double its message length in every phase of a sequential repetition;
- with an honest prover that echoes it (zero-knowledge for a single run), the views of the
  `Q`-fold repetition grow like `2^Q`, so no strict-PPT simulator exists;
- so Thm 175.1 is false as worded. The worker's repair, which I checked, assumes
  `Protocol.ProverBounded R B`: the honest prover's messages have at most `B(|x|)` bits.

**Options.**
1. **Keep D8; Thm 175.1 assumes `ProverBounded` (recommended).** No ch. 2–4 change. Every
   concrete protocol of ch. 2–4 has bounded honest messages. The gate 03 pack for D8 (03e) flags
   the point for its auditor.
2. **Strengthen D8:** require verifiers in `ZK` to read only a polynomial prefix of each message
   (`ReadsPrefix`, as `IP` already does). Closer to the source's p.p.t. verifier, but it changes
   ch. 2–4's ZK definitions and their proofs, and pack 03e audits the new form.

## Q-2. PSV06 for Def 173.7 and Thm 174.8 — **done:** [PSV06] and [PSV07] uploaded (2026-11-05)

The ruling is to follow [PSV06]. The session's network policy refused
`shelat.khoury.northeastern.edu` and `www.iacr.org`. Either add a host under Allowed domains
(cloud environment menu → Edit → Network access;
https://code.claude.com/docs/en/cloud-environments#network-access), or put the PDF on the records
branch as for [PS10].

**Outcome.** Both papers are uploaded. They are not committed, since they are publisher copies; their
SHA-256s are in the decision log. The simulation-based form is in [PSV07], not [PSV06], and it
shows Thm 174.8 holds only under CPA (decision log, 2026-11-05). For gate 06, attach both PDFs.

## Q-3. A merged-away remote branch — **deferred** (user: not yet)

Two merged-away branches. **Recommended: delete both.** I have not deleted them, because deleting
a remote branch is yours to approve.
- `cryptography/pass-shelat-ch5-8-prong-c-seqcomp` (Thm 175.1's worker branch) is fully contained
  in `cryptography/pass-shelat-ch5-8-prong-c` (fast-forwarded).
- `cryptography/pass-shelat-ch5-8-prong-d-learn` (Thm 179.1's side branch) is merged into
  `cryptography/pass-shelat-ch5-8-prong-d`.

## Q-4. The PAC layer's PR to `main` — **ruled: gate it** (gate 05 staged)

[Shilun-Allan-Li/tcslib#194](https://github.com/Shilun-Allan-Li/tcslib/pull/194) adds S3d layer 1
(per ruling R-3). It is 646 lines, sorry-free, with standard axioms only, and was checked by the
maintainer (`evidence/pac-2026-11-05/`).

**Options.**
1. **An external gate, as P0 had (gate 01) (recommended).** It lands on `main` and defines notions
   that Thm 179.1 will rest on. I would stage a small pack (the three files, S3d, and [PS10]
   §8.1) for you to dispatch.
2. **Merge on the maintainer's checks.** Faster, since it is information-theoretic and fully proved.
   But nothing outside the campaign has read the definitions.

## Q-5. How to state Yao's protocol and Thm 163.7 — **ruled: option 1**; efficiency **ruled: in the definition, `Efficient` + bounded honest messages** (2026-11-05)

**Context.** Prong B now has Def 155.1, OT (Prot 160.4, Prop 161.5), the special encryption
(Alg 157.2, Claim 157.a) and garbling (Constr 158.a, Claim 159.a). Two points remain open.
- **Yao needs OT of `n`-bit keys.** The OT of Prot 160.4 transfers bits; the source says the
  generalization to `n` bits is "straightforward".
- **The security proof composes.** It runs the OT simulators inside the larger protocol, a
  composition step the notes never state (inventory: use [Gol04] §7.3). D8's protocols have no
  composition operator yet.

**Options.**
1. **The OT-hybrid model first (recommended).** State Yao with an ideal OT for the key transfer,
   and Thm 163.7 in that model (garbling simulator plus Claims 157.a and 159.a). Separately, state
   [Gol04] §7.3's composition theorem for honest-but-curious protocols, which yields the real
   protocol with the bitwise OT of Prot 160.4, run per key bit. This is the standard modular
   route; each piece stays small and auditable.
2. **The real protocol directly.** Build the sequential composition of D8 protocols (like Thm
   175.1's `seqRep`, but for different sub-protocols), then state Thm 163.7 for Yao with the real
   OT. Closer to the source's single statement, but larger, and the composition argument hides
   inside the theorem.
3. **Defer Thm 163.7.** State Prot 162.6 only, and leave the security theorem for after the
   statement gate.

Also: `HBCSecure` does not require the honest parties to be efficient. **Recommended:** add a
`Protocol.Efficient` side condition to the protocols' theorems (OT, Yao), not to the definition.

## Dispatches and merges

- **Gate 03 (ch. 2–4): 03a, 03b, 03c, 03e dispatched and returned (2026-11-05); the other seven: Not yet clear to dispatch — the interface packs' repairs first.** 03b, 03c and 03e have four majors between them (the `Collection` interface, `PRG` expansion at `n = 0`, the proof systems' efficiency, perfect ZK); their repairs change what 03d, 03f1, 03f2, 03g, 03i, 03j and 03k audit. Reviews are in progress; rulings follow as questions. (11 packs.) They are pinned to
  `a3c5fa8b72e50939822f22364647dc844a3914a0`, after a fresh replay of their closure there (415
  modules with `Checks.lean`, all pass; `gates/03-ch2-4/evidence/replay/`). The records are at
  `fed6c2fb9dd35fcceda878ab36f3dc2a34cd3a5c`. Each folder on `exchange/pass-shelat-ch5-8`
  (commit `d3dc9633db52e95e4fb5ff8a80e97dc29bff7400`), `outbox/gates/03<pack>-ch2-4-gate/`, has the
  bundle, its SHA-256 and the dispatch prompt in `README.md`. Order (PLAN.md): the interface
  packs first, which may run in parallel.
  - **Interface:** 03a (`024b285f…`), 03b (`cbc2550b…`), 03c (`4747cbdc…`), 03e (`a01c936f…`);
  - **sorried statements:** 03f1 (`76cae3ff…`), 03f2 (`3357df40…`), 03g (`c0e37b33…`), 03h
    (`976b7d72…`);
  - **the rest:** 03i (`fb94694c…`), 03k (`2fb353c2…`), 03l (`d43f8e31…`).

  Each pack attaches its bundle and the PDF (`Pass–Shelat.pdf`, SHA-256 `76245560…`).
- **Gate 04 (S2b): dispatched by the user (2026-11-05).** It audits PR
  [Shilun-Allan-Li/tcslib#195](https://github.com/Shilun-Allan-Li/tcslib/pull/195) at
  `afe5982f612081bba2fbcec9ab41adcbbc118b13`. Its replay passes (772 modules); axioms are standard
  except T1 and T2; lint is clean. The folder is `outbox/gates/04-s2b-gate/` on
  `exchange/pass-shelat-ch5-8` (commit `9e3305b2f47352f279f642526c3bf25fcc7c9b0f`), with the
  bundle (SHA-256 `d64276ef…`) and the dispatch prompt in `README.md`.
- **#195 (S2b): Not yet clear to merge — gate 04 first.** After it merges, gate 03's packs 03d and
  03j pin to the merged head, and the prongs (all stacked on S2b) can be integrated for gate 06.
- **Gate 05 (PAC layer, #194): dispatched by the user (2026-11-05).** The folder is `outbox/gates/05-pac-gate/` on
  `exchange/pass-shelat-ch5-8` (commit `34f3f1202146babb64b3bdccf8859ddc030bb8f4`), with the
  bundle (SHA-256 `451a101b…`, 11 sections) and the dispatch prompt in `README.md`.
- **#194 (PAC layer, to `main`): Not yet clear to merge — gate 05 first.**
- **Lean branches (no PRs; for the ch. 5–8 statement gate later):** prong A
  `cryptography/pass-shelat-ch5-8-prong-a`, prong B `…-prong-b`, prong C `…-prong-c`, prong D
  `…-prong-d`.

## Gate 03 (interface packs) and prong B: rulings requested (2026-11-05)

From the reviews of the findings (`gates/03-ch2-4/review/`). Options are listed with the recommended one first.

- **G3-1 — ruled (A), 2026-11-05.** The `Collection` interface (03b major).** (A) add the field `encD_decD`: decoding is canonical. Every ch. 2–4 decoder already is, so each instance gets a short lemma and no proof changes; it makes `PredEvaluator`, `SamplerCanonical` and OT's `hspec` derivable. `Collections.lean` is split first. 03d, 03f1 and 03f2 wait for it. (B) canonical outputs: restate `sample_spec` and `inv_spec` as string equalities. (C) a named hypothesis `Collection.Canonical` carried by the consumers. (D) keep it, and acknowledge the debt.
- **G3-2 — ruled (A), 2026-11-05.** `PRG` expansion at `n = 0` (03c major).** (A) keep `∀ n, n < ℓ(n)` and declare the cost; length-doubling is already handled by `DoublingPRG` and `PRG.doubling` in `PRF.lean`, and "PRGs exist" means the same under every option. (B) `0 < n →` (admits `2n`). (C) `2 ≤ n →` (admits every polynomial stretch); 03d, 03i and 03j would wait under B or C.
- **G3-3 — ruled (A), 2026-11-05.** Efficiency in the proof systems (03e major 1; reopens Q-1 from the ch. 2–4 side).** (A) apply ch. 6's convention: `Efficient` plus bounded honest messages, in `InteractiveProof`'s completeness and as a field of `EfficientProverProof`. `ProverBounded` moves into ch. 2–4 and Thm 175.1's hypothesis becomes derivable. It costs about five bound lemmas, no statement text changes, and excludes undecidable languages. (B) docstrings only, and you acknowledge that the structures admit languages outside IP (the auditor's HALT example). (C) the auditor's `ReadsPrefix` caps: the most rework, mostly in 3-colouring.
- **G3-4 — ruled (A), 2026-11-05.** Perfect ZK (03e major 2).** (A) keep both definitions and state the cost. Prove `PerfectZKAbort.statZK` (error `2^{-|x|}`); ch. 7 cites `StatZK.seqRep` with negligible error for the source's perfect case. (B) docstrings only, and drop the perfect forms from ch. 5–8. (C) change the model to exact sampling or expected time (months).
- **G3-5 — ruled (A), 2026-11-05.** Duplication rooted in `private` helpers (03a, raised to major; 03b).** (A) ledger it as DL-9 onward and clean it up in the gate 03 repair PR: make `stateFind`, `ptc_comp` and `abs_uexp_sub_le` public, and keep one `blocks` and one `decodeFin_eq_some_iff`. 03h, 03i and 03k wait for that PR. (B) ledger it now and pay it back at the `main` landing. (C) accept it permanently.
- **G3-6 — ruled (A), 2026-11-05.** Unapproved `@[simp]` attributes (03a, 03b, 03c, 03e).** (A) approve all the listed ones in one ruling. (B) pack by pack. (C) drop them all, which needs a full replay.
- **G3-7 — ruled (A), 2026-11-05.** Smaller items.** (a) `negligible_zero`: move it to `Foundations/Negligible.lean`, overriding D2's freeze for one lemma (recommended), or put it in a new helper file. (b) Thm 75.4's extra `0 < ℓ(n)`: drop it (recommended), or declare it. (c) `glPad`'s `henc`, which no library candidate satisfies: state the cost now (recommended), or weaken it after G3-1. (d) Thm 124.1's soundness amplification: add `InteractiveProofErr.seqRep` to prong C (recommended), or record the debt.
- **G3-8 — ruled (A), 2026-11-05.** Prop 161.5 cannot be proved as stated (03b review, missed by the auditor).** If the sampler draws `f(u)` from a random `u`, Bob's coins reveal `a_{1−b}`: the enhanced-trapdoor gap. (A) add an enhanced hard-core hypothesis in prong B (Goldreich vol. 2, App. C.1), declared. (B) restrict to samplers that return their coins (excludes RSA and Rabin). (C) put the enhanced predicate into the ch. 2–4 interface (reopens 03b).

**Dispatch under the recommended options:** 03l now; 03d and 03j after #195; 03f1 and 03f2 after G3-1's repair; 03g and 03k after G3-3's; 03h, 03i and 03k after G3-5's cleanup.

## Gate 04 and 05 rulings — all ruled (A), 2026-11-05

R-04-1 strict unary; R-04-2 all equation lemmas in #195; R-04-3 extend T0–T2 before the fill; G5-1 remove `PACLearnable`; G5-2 `probTrue` later (queued below).

## Queued follow-ups

- **`FinDist.probTrue` into `FinDist.lean`** (G5-2): a small PR to `main` after #194 lands.
- **Gate 03, 03l: dispatched by the user (2026-11-05)** (folder `outbox/gates/03l-ch2-4-gate/`; its one stale prose line, `StringLoops.lean:36–38` calling `stateFind` private, changes in the G3-5 clean-up).
- **Gate 05 round 2 (closing; #194 at `6b781240`): dispatched by the user (2026-11-05).** The folder is `outbox/gates/05-pac-r2-gate/` on `exchange/pass-shelat-ch5-8` (commit `984ba6b82644d8fe81b9cf450fb0b9e2bdddeb57`), with the bundle (SHA-256 `3e5dd418…`, 11 sections) and the prompt in `README.md`.
- **Prong D** carries the old PAC files (from `44d27f39`); it merges #194's branch again before gate 06.
- **#198 (gate 03b repairs): merged by the user.** Maintainer checks recorded in the decision log; 03b's closing round audits the delta after the merge, as for #193. After it merges, 03f1 and 03f2 pin to the new head and dispatch.
- **#199 (gate 03e repairs): merged by the user.** After it merges, 03g and 03k pin and dispatch (03k also waits for the G3-5 clean-up).
- **Gate 04 round 2 (closing; #195 at `243598b7`): dispatched by the user (2026-11-05).** Folder `outbox/gates/04-s2b-r2-gate/` on `exchange/pass-shelat-ch5-8` (commit `ffefb8f97b0a7ff507f5a47e96a142cf5643261e`); bundle SHA-256 `82bf3e91…`, 32 sections; prompt in `README.md`.
- **03f1, 03f2, 03g:** pinned once the 03a and 03c repair PRs land (03a changes `DiscreteLog`'s imports); the replay at `af91d53a` is their base tree.
- **G3-5 clean-up PR to-do** (after #195): `NUPPT.coinLen_eq`; `decodeOracleMove`'s case lemmas; `negligible_const_zero` removed; `ThreeColoring/SimulatorMachine` imports `NonUniform` itself; `ofFn_of_decodeFin_eq_some` folded into the single `decodeFin_eq_some_iff`; the private-helper families (`stateFind`, `ptc_comp`, `blocks`, `abs_uexp_sub_le`, `forall_of_uprob_eq_one`) made public once.
- **Gate 05 round 3 (#194 at `f0385dac`, docstring repair of round 2): dispatched by the user (2026-11-05).** Folder `outbox/gates/05-pac-r3-gate/` (exchange `a36de8a5`); bundle SHA-256 `d91f950f…`, 10 sections.
