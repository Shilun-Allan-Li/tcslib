# Queue for the user (overnight, 2026-11-05)

Items that need you, newest last. Work that does not depend on them continues meanwhile. Each
question gives the options, with the recommended one first.

## Q-1. Thm 175.1 and the efficiency of verifiers (decision)

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

## Q-2. PSV06 for Def 173.7 and Thm 174.8 (action)

The ruling is to follow [PSV06]. The session's network policy refused
`shelat.khoury.northeastern.edu` and `www.iacr.org`. Either add a host under Allowed domains
(cloud environment menu → Edit → Network access;
https://code.claude.com/docs/en/cloud-environments#network-access), or put the PDF on the records
branch as for [PS10].

## Q-3. A merged-away remote branch (yes/no)

`cryptography/pass-shelat-ch5-8-prong-c-seqcomp` (Thm 175.1's worker branch) is fully contained in
`cryptography/pass-shelat-ch5-8-prong-c` (fast-forwarded). **Recommended: delete it.** I have not
deleted it, because deleting a remote branch is yours to approve.

## Q-4. The PAC layer's PR to `main`: gate or not (decision)

[Shilun-Allan-Li/tcslib#194](https://github.com/Shilun-Allan-Li/tcslib/pull/194) adds S3d layer 1
(per ruling R-3). It is 646 lines, sorry-free, with standard axioms only, and was checked by the
maintainer (`evidence/pac-2026-11-05/`).

**Options.**
1. **An external gate, as P0 had (gate 01) (recommended).** It lands on `main` and defines notions
   that Thm 179.1 will rest on. I would stage a small pack (the three files, S3d, and [PS10]
   §8.1) for you to dispatch.
2. **Merge on the maintainer's checks.** Faster, since it is information-theoretic and fully proved.
   But nothing outside the campaign has read the definitions.

## Dispatches and merges

- **Gate 03 (ch. 2–4): Ready to dispatch** (11 packs). They are pinned to
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
- **S2b PR and gate 04:** after S2b's post-merge replay (running). S2b now also carries T2, and
  gate 04's pack covers it.
- **#194 (PAC layer, to `main`):** see Q-4.
- **Lean branches (no PRs; for the ch. 5–8 statement gate later):** prong A
  `cryptography/pass-shelat-ch5-8-prong-a`, prong B `…-prong-b`, prong C `…-prong-c`, prong D
  `…-prong-d`.
