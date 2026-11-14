# Codex audit · Gate 22 ext-nosrc (#303)

Audit draft PR #303 at e99a6055ff6b24cdf4b25993e83d045bd569028f using the scope in pack.md. Campaign records are pinned at 1d109ff037d12cc6520ba0fb7826e320da348d73.

The bundle contains:
- the pack, the maintainer review, the worker report, policy, the issued brief and the duplication ledger;
- pr.diff.txt, the full diff from the PR base ba0adb6b1a69787805340d06cb5ce9216b6277a0 to the head;
- all four changed Lean files at the head: Randomness/Extraction (owned), Randomness/Extraction/Rejection (new),
  Randomness/Extraction/Sampler (new) and the facade Randomness.

The zips:
- sources.zip: the source closure at the head of every changed module (203 files);
- verification.zip: every file the maintainer review cites, as byte-identical originals: review-evidence.zip and
  ledoc-evidence.zip with their manifests, the landing/ and landing-ledoc/ extracts, the cited records and the
  worker's scope-request/ (its entries are exactly its SHA256SUMS plus SHA256SUMS itself).

landing/ holds the logs at the head. The worker's own evidence is on this branch under
inbox/fills/ext-nosrc/evidence/ (delivery commit a5da5cc3b2f37f8a8540cf74eb2762cd1e2a08d4). Check SHA256SUMS before
using the pack.

Return gate22-ext-nosrc-findings.md as Markdown in the chat. If you have several evidence files, return a ZIP
containing that Markdown and the evidence. The user dispatches and merges.
