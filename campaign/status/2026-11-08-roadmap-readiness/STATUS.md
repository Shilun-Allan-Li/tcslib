# Chapters 3–4 roadmap readiness, 2026-11-08

At the time of these checks, the merged campaign Lean tree was `9b5dcf46408db681bcbc721930ef2203fa6bc47d` (MAC8). Fresh Lean checks through
leanelab.sh found no sorryAx in all 26 previously tracked headline closures
(9 for chapter 3, 17 for chapter 4) or in 19 additional roadmap results. The
same 26-probe was 19/26 on 2026-11-05. Exact probe sources and outputs are
beside this report. This is a selected proof-closure count, not a whole-tree
admission count. Ladner is outside the old 26.

| Roadmap | Merged proof status |
|---|---|
| P3.1–P3.2, oracle classes and relativization | The oracle classes, co-SAT and P-oracle facts, EXPCOM equalities, both sides of Baker–Gill–Solovay, and a non-time-constructible function are in the merged source. |
| P3.3, time hierarchies | The book-strength f log f deterministic result and its positive-bound version (#223), the nondeterministic time hierarchy and its linear-overhead universal NDTM pass. The deterministic theorem's positivity/normalization and machine model are as stated in TimeHierarchy/Diagonal. |
| P3.4, Ladner | Gate128 is closed at `1096e50b4e105392737ec52939b1db0cdbd9316d`. #249 is clear to merge as the statement scaffold; the PR remains open with six direct mathematical admissions and one packaging theorem depending on them. No proof fill is dispatched. |
| P4.1–P4.2, space classes and simulations | DTIME ⊆ SPACE ⊆ NSPACE, NSPACE to exponential time, the configuration bound, NP ⊆ PSPACE, 3SAT, EVEN and MULT, general Savitch and PSPACE = NPSPACE are in the merged tree. |
| P4.3, hierarchy and PSPACE completeness | Space hierarchy and L ⊊ PSPACE, SPACE(n+1) ≠ NP (#229), F6's forward space-universal simulation (#235), TQBF membership/hardness/completeness and finite-game determinacy pass. TQBF hardness uses Complexity.Codec and a uniform tableau, independent of RD-2. The separate closed-form ConfigCodec semantic and uniformity lemmas remain admitted (see below). |
| P4.4, logspace | The checked logspace reduction laws, PATH membership and NL-completeness, NL ⊆ P, NL = coNL and the general NSPACE complement theorem are merged. The separately queued additive NL closure lemma and deferred book items are not implied by this count. |

A separate direct-admission check imported all 144 compiled modules in the
ClassOracle, ClassPSPACE, Diagonalization, SpaceComplexity and TimeHierarchy
trees and inspected 21,541 visible owned constants. It found exactly 21
direct admissions, all in `Complexity.ConfigCodec` in ClassPSPACE/TQBF.lean,
matching the 21 source holes. These are the already statement-gated RD-2a
semantics and RD-2b uniformity work, held by Seyoon on 2026-10-14 after
the ARM-based TQBF proof landed through a different route. The older
`exists_adjacency_codec_cnf` result passes in its documented polynomial
form. The 21 admissions do not enter TQBF membership, hardness or
completeness. The separate H6 supporting modules FormulaKit.Gate and FormulaKit.Emit also
have 20 direct admissions (10 each), verified against the same snapshot and
source. The held RD-2 route therefore has 41 known direct holes across these
two scopes. This is not a repository-wide admission count. RD-2 needs an explicit resume or
scope decision before a chapter-wide zero-admission closeout.

Two of the three later priority tracks are proved and merged: book-form Theorem 3.1 and F6.
Ladner is the remaining active major theorem track. RD-2 remains a separate held proof front. Ladner’s six open proof obligations cover
the polynomial-time selector, NP membership, eventual boundedness/divergence, the padding-hardness
implication, and the final witness. The recorded sharp SAT verifier interface awaits a separate
ruling, and the memo/clock/size and simulation obligations still need concrete routes before a
fill can be dispatched. A gate for a statement scaffold does not close those proofs.

The campaign is still in infrastructure and closeout work: finish the reader and duplicate-proof
PRs, settle the active ledger items, reconcile the exact campaign-scope admissions and statement
drift, then run the final audit and blueprint increment before integration with main. Deferred
exercises remain deferred. These are distinct from the 45 proof closures observed here.
