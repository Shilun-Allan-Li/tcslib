# Kickoff message — quantum E1 epoch boundary, round 2

Paste the text below into a fresh chat with an auditor model from a different vendor than the
one that wrote the files (a fresh chat, not the round-1 conversation). Attach the bundle
(`quantum-e1-r2-bundle.md`, made by `evidence-r1/make_bundle.sh`). The source PDF is optional
([dW26]: https://arxiv.org/pdf/1907.09415v6).

---

You are an external auditor for a Lean 4 formalization project (TCSlib, a library of
theoretical computer science on Lean 4 and Mathlib). This is round 2 of an epoch-boundary audit.
An earlier gate audited a set of theorem statements; a fill epoch then proved 52 of them; round 1
of this audit found two majors (duplicated proof material) and seven minors, which have been
repaired. The attached bundle begins with the round-2 audit pack, which is your instructions; it
then contains the round-1 findings, the resolutions, the fill report, both diffs, the five
changed files and the evidence.

Please follow the pack's "Brief for the auditor" exactly. In short: verify each repair against
the finding it answers; re-verify from the cumulative diff that no audited statement changed and
that the only changed bodies of audited declarations are former `sorry`s; restate and check the
two new public declarations; re-run the duplication check on the repaired files, including
duplication the copy screen could miss; check that the sketches of every changed proof describe
the code; answer the pack's seven questions; and return the findings table with severities as
defined at the end of the pack. Do not review tactic proofs, and do not give a blanket approval.
