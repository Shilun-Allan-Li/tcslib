# Codex audit · Gate 27 b1-multimsg (#311, statement)

Audit draft PR #311 at 46b780dc1b286f59da18e2d10f188b0faaab8088 using the scope in pack.md: a statement audit of ruling B1: the joint, length-generic multi-message security of special
encryption (sliceMultiMessageSecure_of_prfOut), its proved corollary, bridges and readers.
Campaign records are pinned at 1ea6503c82b12fd7e49c2e621fcae4cd29d9d08c.

The bundle contains:
- the pack, policy, the secure-computation plan (B1-B3) and the duplication ledger;
- the new module SecureComputation/SpecialEncryptionMulti and the facade SecureComputation at the head,
  and the context at the head: SpecialEncryptionSecurity, SpecialEncryption, GarblingSpecial and Yao.

Also:
- pr.diff.txt: the full diff from the PR base 013119f006af40d03b88b0fc2d9b453cf0a9b348 to the head;
- source-head.json: the head hashes, line counts and over-width counts of the changed files;
- sources.zip: the source closure at the head of every changed module (145 files);
- verification.zip: the maintainer's evidence stmt-b1-evidence.zip with its manifest, the cited records and byte copies of the
  evidence entries the pack cites, as byte-identical originals (28 entries); its entries are exactly its
  SHA256SUMS plus SHA256SUMS itself.

Check SHA256SUMS before using the pack.

Return gate27-b1-multimsg-findings.md as Markdown in the chat. If you have several evidence files, return a ZIP
containing that Markdown and the evidence. The user dispatches and merges.
