# Codex audit · Gate 40 pairings (#331, statement)

Audit draft PR #331 at 110c2f9db810d243693b9a5e8976a5ad205f1bab using the scope in pack.md: a **statement audit** of the pairing campaign
(PairingCryptographyPlan.md, rulings Q1-Q13 and the location ruling): the bilinear bundle and generator, BDH and
Decision BDH, Joux's tripartite Diffie-Hellman, the IBE interface and the selective-identity game, and the Boneh-Boyen
system BB1, with the four sorried targets T1-T4, and an audit **as proofs** of the results the PR already proves (Joux
correctness and key indistinguishability, jouxGame_eq_dbdhGame, BB1 correctness, and bb1_sidSecure from T2-T4).
Campaign records are pinned at 356321accdd29b9ec73391b1c7b211b7d4cabf0f.

The bundle contains the pack, policy, the campaign plan, the statement-phase EVIDENCE.md, text excerpts of the
passages of [Jou00] and [BB04] that the statements use (the PDFs are not committed, ruling Q12), and the 12 new Lean
modules at the head.

Also:
- pr.diff.txt: the full diff from the PR base 523d80d2d4dd8e4ed6799358831e5b3806c6187b to the head;
- pr-description.md: the PR description as fetched from GitHub on 2026-11-16;
- source-head.json: the head hashes, line counts and over-width counts of the changed files;
- sources.zip: the source closure at the head of every changed module (86 files; the library root TCSlib.lean is
  included as a file, not as a closure root);
- source-excerpts/: the two excerpt files (also in bundle.md);
- verification.zip: the statement evidence stmt-pairings-r2.zip with its manifest and PROVENANCE, byte copies of the
  entries the pack cites, the round-1 evidence, the cited records, context files for the duplication question and the
  pack's git-object re-checks (pack-checks/); its entries are exactly its SHA256SUMS plus SHA256SUMS.

Check SHA256SUMS before using the pack.

Return gate40-pairings-statements-findings.md as Markdown in the chat. If you have several evidence files, return a ZIP containing
that Markdown and the evidence. The user dispatches and merges.
