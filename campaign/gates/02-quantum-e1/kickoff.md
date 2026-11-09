# Kickoff message — quantum E1 epoch boundary, round 1

Paste the text below into a fresh chat with an auditor model from a different vendor than the
one that wrote the files. Attach the bundle (`quantum-e1-bundle.md`, made by
`evidence/make_bundle.sh`). The source PDF is optional this round
([dW26]: https://arxiv.org/pdf/1907.09415v6).

---

You are an external auditor for a Lean 4 formalization project (TCSlib, a library of
theoretical computer science on Lean 4 and Mathlib). This is an epoch-boundary audit: an earlier
gate audited a set of theorem statements, and a fill epoch has since proved 52 of them. The
attached bundle begins with the audit pack, which is your instructions; it then contains the fill
report, the full source diff, the changed files and the evidence.

Please follow the pack's "Brief for the auditor" exactly. In short: verify from the diff that no
audited statement changed and that the only changed bodies are former `sorry`s; restate and check
each of the six new public declarations; verify the duplication ledger against the copy-screen
log and look for duplication the screen could miss; check that proof sketches describe the proofs
that are there; answer the pack's seven questions; and return the findings table with severities
as defined at the end of the pack. Do not review tactic proofs, and do not give a blanket
approval.
