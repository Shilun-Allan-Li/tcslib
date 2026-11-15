# Codex audit · Gate 33 prf-mac (#317)

Audit draft PR #317 at 590d1a56a350d9e8e75ee33d31e0501182169f67 using the scope in pack.md: a proof audit of Authentication.prfMAC_secure [PS10, Theorem 135.4], with the landing
edits LE-doc (docstrings only) and LE-reuse (proof only, review finding F-01).
Campaign records are pinned at 76ff988bc26c66298a42b06a0abce1cf6cca7e34.

The bundle contains the pack, the maintainer review, the worker report, policy, the issued brief, the duplication
  ledger (DL-44), the review's overlap search, the LE-reuse PROVENANCE and Gate 30's resolutions
  (the F-01 promotion); pr.diff.txt; the six changed Lean files at the head (MAC/FromPRF and its
  helpers FromPRF/{Handler,Reduction,Random,Game,Bound}) and, as context at the head, MAC/Defs
  (the forgery game) and Pseudorandom/Functions/Defs (prfAdv, prfAdv_eq_expect).

Also:
- pr.diff.txt: the full diff from the PR base e99987221593020b9f7dbb87fe577bd6aac5ecbb to the head;
- pr-description.md: the PR description as opened on GitHub;
- source-head.json: the head hashes, line counts and over-width counts of the changed files;
- sources.zip: the source closure at the head of every changed module (172 files);
- verification.zip: every file the review and the LE-reuse record cite, as byte-identical originals:
  review-evidence.zip and reuse-evidence.zip with their manifests, the landing extracts, the cited
  records, evidence extracts, the worker extracts (worker/) and the pack's git-object re-checks
  (pack-checks/); its entries are exactly its SHA256SUMS plus SHA256SUMS (114 entries).

landing/ holds the logs at the head. The worker's own evidence is on this branch under
inbox/fills/prf-mac/ (delivery commit 51ae2c1215554ccda3dde19d8d72908ea74dd339).
Check SHA256SUMS before using the pack.

Return gate33-prf-mac-findings.md as Markdown in the chat. If you have several evidence files, return a ZIP
containing that Markdown and the evidence. The user dispatches and merges.
