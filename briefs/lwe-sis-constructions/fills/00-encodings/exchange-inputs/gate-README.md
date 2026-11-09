# Representation-proof review, round 1 — Codex

Read the root exchange README and lwe-sis-constructions/README.md, then this gate at the exact exchange commit in the kickoff. Inputs are read from GitHub. Return lwe-sis-encoding-proofs-findings.md as a Markdown file in chat; no attachment or worker push is needed. The user dispatches the job.

## Frozen identities

- Statement freeze: `4364d0e0fe9accd649b6acb4751e8684aa93ad1e`.
- Filled Lean/root source: `893e921bf2afeca293be9da9d495613bb1486796`.
- Bundled records: `7a9dfa6bf05eebb9ea736067351be3cbb438857c`.
- Code PR branch: `cryptography/lwe-sis-encoding-proofs`, target `cryptography/pass-shelat-ch2-4`.
- Bundle: `lwe-sis-encoding-proofs-r1-bundle.md`.
- SHA-256: `2f8308efa0f737d09cf9554c45407855b76756ee73a2d9fe28fa582962a49ff0`.
- Bytes: 3033293; sections: 259.
- Git blob: `3fd06f3dbc45afb56b67578752528cd9cd33bc6a`. If a GitHub file-content endpoint omits this large file's content, fetch this Git blob or clone the pinned exchange commit.

Verify SHA256SUMS and the revision-qualified BUNDLE-FILES.txt/.json index. The first bundle section is audits/lwe-sis-encoding-proofs-pack.md verbatim. Follow its task and severity guide. The full scoped 55-module source dependency tree, prior findings/resolutions, proof diff, fill report and all evidence are included.

The statement gate passed 0/0/0/3. This review covers all 14 completed representation proofs, preservation of the 61 public declarations, and the evidence. Fresh native checks pass with zero new admissions and 17 inherited warnings; all 166 constants use only standard axioms. There is no whole-library or construction-security claim. Retain source archival/ingestion and future sampler/profile obligations. No statement or hardness assumption was changed.

Historical phase-0 records describe their earlier 14 admissions and preparation-time transport. They remain unchanged. Current proof results are in fills/00-encodings/REPORT.md and its evidence. The earlier topic ref remains unchanged; the proof update is proposed through the new PR branch. No merge is authorized.

Do not edit/fill source, dispatch workers, push output or merge. Return lwe-sis-encoding-proofs-findings.md in chat with independent proof/invariance assessments, severity counts, concrete findings and a gate recommendation.

## Optional extraction

After checksum verification, `python3 -I extract_bundle.py /tmp/lwe-sis-proof-review` extracts every original attachment into a new directory and verifies each length/hash. It treats attachments as data and executes no source. Coordinate resources separately before any optional native run.

**Ready to dispatch — pinned Codex proof-review inputs are prepared; no verdict or merge clearance is claimed.**
