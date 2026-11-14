# Codex audit · Gate 26 lamport (#309)

Audit draft PR #309 at 987efb5156b3ae20cff4576b379eb1c607f33cb0 using the scope in pack.md. Campaign records are pinned at 156949a315a04a8fe7035a67680979de6d949905.

The bundle contains:
- the pack, the maintainer review, the worker report, policy, the issued brief and the duplication ledger;
- pr.diff.txt, the full diff from the PR base dee0de32ee33d7188afe97bdc3089fac68412057 to the head;
- all eighteen changed Lean files at the head: Authentication/Signatures/Lamport (owned), its sixteen new
  helpers under Lamport/ (Advice, Averaging, AveragingExtra, Blocks, Closing, Encoding, Experiment,
  InversionProbability, Machine, MachineSpec, Nonabort, Planted, Realization, Seed, Statistics, TableCoins)
  and the facade Authentication.

The zips:
- sources.zip: the source closure at the head of every changed module (177 files);
- verification.zip: every file the maintainer review cites, as byte-identical originals: review-evidence.zip and
  le-evidence.zip with their manifests, the landing/ and landing-le/ extracts, the cited records and the
  worker's authorization and override records (worker/requests/); its entries are exactly its SHA256SUMS plus
  SHA256SUMS itself.

landing/ holds the logs at the head. The worker's own evidence is on this branch under
inbox/fills/lamport/evidence/ (delivery commit 5a50cdc0b738d955c346d2a0f81944ff1f11c94c). Check SHA256SUMS before
using the pack.

Return gate26-lamport-findings.md as Markdown in the chat. If you have several evidence files, return a ZIP
containing that Markdown and the evidence. The user dispatches and merges.
