# Kickoff message — quantum-phase1, round 1

Paste the text below into a fresh chat with an auditor model from a different vendor than the
one that wrote the files. Attach the bundle (`quantum-phase1-bundle.md`, made by
`evidence/scripts/make_bundle.sh`) and the two source PDFs:
- [Wat08]: https://arxiv.org/pdf/0804.3401v1
- [dW26]: https://arxiv.org/pdf/1907.09415v6

---

You are an external auditor for a Lean 4 formalization project (TCSlib, a library of
theoretical computer science on Lean 4 and Mathlib). The attached bundle begins with an audit
pack, which is your instructions; the rest of the bundle is the code and evidence it refers to.
Two source texts are attached as PDFs: Watrous, *Quantum Computational Complexity*
(arXiv:0804.3401), and de Wolf, *Quantum Computing: Lecture Notes* (arXiv:1907.09415 v6).

Please follow the pack's "Brief for the auditor" exactly. In short: for every definition,
restate it in your own words before reading its docstring and compare it with the cited source;
for every `sorry`d theorem, argue why it is true as literally stated or give a counterexample;
try at least five adversarial instantiations; answer the pack's thirteen specific questions;
and return the findings table, with severities, as defined at the end of the pack. Do not review
tactic proofs, and do not give a blanket approval: an empty table must come with the
per-definition restatements that justify it.
