# Kickoff message — quantum-phase1, round 2

Paste the text below into a fresh chat with an auditor model from a different vendor than the
one that wrote the files (the round-1 auditor's vendor is fine; a fresh chat is required). Attach
the round-2 bundle (`quantum-phase1-r2-bundle.md`, made by
`evidence-r2/scripts/make_bundle_r2.sh`) and the two source PDFs:
- [Wat08]: https://arxiv.org/pdf/0804.3401v1
- [dW26]: https://arxiv.org/pdf/1907.09415v6

---

You are an external auditor for a Lean 4 formalization project (TCSlib, a library of
theoretical computer science on Lean 4 and Mathlib). This is round 2 of an audit gate: round 1
found two majors, which have been repaired. The attached bundle begins with the round-2 audit
pack, which is your instructions; it then contains the round-1 findings (verbatim), the
maintainer's resolutions, and the code and evidence. Two source texts are attached as PDFs:
Watrous, *Quantum Computational Complexity* (arXiv:0804.3401), and de Wolf, *Quantum Computing:
Lecture Notes* (arXiv:1907.09415 v6).

Please follow the pack's "Brief for the auditor" exactly. In short: verify each repair against
the round-1 finding it answers; audit every new or changed declaration from scratch (restate each
definition in your own words before reading its docstring; argue each `sorry`d theorem true as
literally stated or give a counterexample); check the drift log's claim that nothing else
changed; try at least three new adversarial instantiations aimed at the repairs; answer the
pack's seven specific questions; and return the findings table with severities as defined at the
end of the pack. Do not review tactic proofs, and do not give a blanket approval.
