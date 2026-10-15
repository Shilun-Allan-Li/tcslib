# ch7-phase1 — auditor kickoff message

Paste the text below into a **fresh chat with an LLM from a different vendor** (no
access to this repository or its history) and attach `audits/ch7-phase1-bundle.md`.

---

You are an external, adversarial auditor for a Lean 4 formalization of **Arora–Barak,
*Computational Complexity: A Modern Approach*, Chapter 7 (Randomized Computation)**.
Have the chapter at hand. The attached bundle begins with an audit pack (your full
instructions, the scope table, the declared deviations, and the specific questions),
followed by the campaign plan, `policy.md`, `workflow.md`, and the ten Lean modules
under audit, each under a `## ===== <path> =====` header.

Audit the **trusted surface only** — definitions, theorem statements, and the proof
sketches of the remaining `sorry`s. Do **not** review tactic proofs; several results
are already proved and machine-checked, but treat a proved statement no more gently
than a sorried one (a wrong-but-proved statement is the worst outcome). Your job is to
find infidelity, trivialization, unprovability, and missing hypotheses.

Note: part of this surface — three support modules (`CounterProgInput`, `PairEncode`,
`PolyTimePrefix`) and three filled `PolyTimeModel` targets — was drafted by a different
AI model and repaired to compile; blind-restate it like any other surface, and pay
particular attention to the circuit-encoding and prefix-operation fidelity questions
(pack questions 5–7).

Work the pack's "Brief for the auditor" and "Specific questions" in order. Priority
one is **CH7-Q1**: whether carrying all class-level probability in ℚ by exact counting
(instead of the book's `e^{-2ε²k}` bound) faithfully proves Theorems 7.10/7.17/7.18 and
Lemma 7.9, or silently weakens any of them. Blind-restate every definition before
reading its docstring; attempt at least three adversarial instantiations (try `n = 0`,
a constant verifier, and a degenerate graph for λ(G)).

Deliver the findings table in the pack's format (severity: blocker / major / minor /
note), and justify an empty table with your per-definition restatements. Do not give a
blanket approval.
