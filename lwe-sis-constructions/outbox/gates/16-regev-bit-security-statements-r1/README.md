# Regev bit-encryption statement audit

This directory contains the complete GitHub inputs for the statement review.
Read the exchange root and LWE/SIS namespace READMEs at the same exchange
revision, then read [AUDIT.md](AUDIT.md) and the first section of the
indexed Markdown packet.

| Pin | Revision |
|---|---|
| Verified Pass–shelat merge | `f967299b6a0bde5b7efa4062b2b55046ebd21387` |
| Proposed Lean source | `fe34bcf656be930f3ea39a10df74110695c95ed4` |
| Audit records | `f7fdb646a1cb78ff0375c9045eb0adba1ae6d57f` |

Verify `SHA256SUMS` and both ordered revision-qualified indexes. Run
`python3 extract_bundle.py --output <new-directory>` from this directory to
verify and extract the 45 exact sections. The full check receipts and
compressed diagnostics are included. The proposed facade patch was applied
only in the checked prospective tree.

To reconstruct the exact source and records commits, use a scratch clone of
`Shilun-Allan-Li/tcslib` that contains the verified merge above. In that clone,
verify and fetch the published `regev-source-records.gitbundle` using its
absolute path.

```sh
audit_gitbundle='/absolute/path/to/regev-source-records.gitbundle'
git bundle verify "$audit_gitbundle"
git fetch "$audit_gitbundle" refs/heads/codex/regev-bit-security-statements:refs/audit/regev-records
git rev-parse refs/audit/regev-records refs/audit/regev-records^ refs/audit/regev-records^^
```

The three lines must be the records, source, and base revisions in that
order. The bundle depends on the published base and carries the two new
commits.
