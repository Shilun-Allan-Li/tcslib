# Codex audit · Gate 28 round 2 · derand host (#312, statement)

Re-audit draft PR #312 at 0c04d1eb1e5450372632a23f3e94f3b7bfc37606 using pack-r2.md. Campaign records are pinned at 50416ccc67b9a28fea74177c2cb2ecf562cc6b29.

Round 1 was HOLD (0/2/1/1). Its findings are in findings/, and resolutions-r1.md answers them. The round-1 pack is
outbox/gates/28-derand-host-gate/ at exchange 2776272b61fcc7a1adf3f743c735c7e45be5045c; pack.md here is its pack.

- landing-r1/: the H17 draft row and the two round-2 evidence builds, each a ZIP with its manifest and PROVENANCE:
  stmt-derand-r2 (2f9333b9, the corollary briefly proved) and stmt-derand-r2b (the head: corollary admitted, wider
  seal).
- verification-r2.zip: byte-identical originals of the host registry (machine-library-design.md, with H17) and the
  decision log, plus checks generated from git (the registry diff since round 1; the base move and the merge of the
  head onto the tip); its entries are exactly its SHA256SUMS plus SHA256SUMS itself.
- pr.diff-r2.txt, source-head-r2.json and sources-r2.zip: the diff, hashes and source closure (308 files) at the head.
- bundle.md: the round-2 pack, resolutions, findings, the H17 draft, both PROVENANCE files, the round-1 pack, policy,
  and at the head SeedMajority.lean, the Randomized facade, ClassP/DTIME.lean, ClassP/ModelInvariance.lean,
  TuringMachine/Build/ModuleHost.lean and the consumer Cryptography/Randomness/Derandomization.lean.

Check SHA256SUMS before using the pack. Return gate28-derand-host-r2-findings.md as Markdown in the chat. If you
have several evidence files, return a ZIP containing that Markdown and the evidence. The user dispatches and merges.
