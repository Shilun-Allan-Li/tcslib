# Codex audit · Gate 20 dl-consolidation (#298)

Audit draft PR #298 at 6f853adc61d5d175ee83c69f6c07ab2da112cabc using the scope in pack.md. Campaign records are
pinned at 3015c622434a0321e784a3da1d83c125b426bf7e. The bundle contains:
- the pack, the maintainer review (with the rebase-r1 addendum), the worker report, policy, the issued brief and
  the duplication ledger;
- pr.diff.txt, the full diff from the PR base 2ea4df08d009a4bbdb8042795ff062d7f22db325 to the head;
- for context, the 13 shared-home Lean files at the head (Games/Probability, Simulate, Hopping, BitCodec,
  Efficiency; Asymptotic/Adversary, EnsemblesLemmas; Foundations/BitLists; PublicKey/OracleSecurity,
  OracleSecurity/PaddedCPA, OracleSecurity/ChallengeSim, HybridMachine; PrivateKey/OracleSecurity).

The zips:
- sources.zip: the source closure at the head of every changed module (240 files);
- verification.zip: the delivery review's raw evidence;
- landing.zip: the rebase over #297 and the landing edit LE-repoint-nmsim (statements-r2/ supersedes
  statements/decls2-nmsim.tsv).

landing/ holds the full-tree logs at the head. Check SHA256SUMS before using the pack.

Return gate20-dl-consolidation-findings.md as Markdown in the chat. If you have several evidence files, return a ZIP
containing that Markdown and the evidence. The user dispatches and merges.
