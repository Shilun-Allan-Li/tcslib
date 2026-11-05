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
