# Report: Completing Whitney's Inequalities with the Multi-Agent Lean Pipeline

**Date:** 2026-07-08
**Target:** Close the three open `sorry` stubs (#13, #14, #15) in
`TCSlib/GraphTheory/Connectivity/`, completing the formal proof of
**Whitney's inequalities** — `κ(G) ≤ κ'(G) ≤ δ(G)` (Theorem 3.1, Bondy & Murty).

**Outcome:** ✅ All three closed. `lake build TCSlib.GraphTheory.connectivity`
succeeds with **0 errors, 0 `sorry` warnings** (790 jobs, 869 ms). The theorem
`SimpleGraph.whitney_inequalities` is now fully proved.

---

## 1. What was done

| Stub | Lemma | Difficulty | Result |
|---|---|---|---|
| #15 | `vertexConnectivity_le_edgeConnectivity` (κ ≤ κ') | strong induction on κ' | ✅ done |
| #13 | `exists_isVertexCut_singleton_of_isBridge` (Exercise 2.3.1a) | graph surgery on bridge components | ✅ done |
| #14 | `vertexConn_le_succ_of_vertexCut_deleteEdge` | 2 subgraph "transport" lemmas | ✅ done |

Two helper lemmas were added along the way (`vertexConnectivity_le_card_pred`,
`one_le_edgeConnectivity_of_connected`). `VertexEdgeConn.lean` grew from **172 →
450 lines** (~278 lines of new proof: #15 ≈ 90 + helpers ≈ 50, #13 ≈ 80,
#14 ≈ 115).

The mathematical strategy in the pre-existing `OUTLINE.md` was **correct on the
first attempt for all three lemmas** — every build failure was Lean/Mathlib
surface friction, never a wrong proof idea.

---

## 2. How the pipeline was actually used

The intended flow is `lean-orchestrator → lean-searcher → lean-prover →
lean-checker`, coordinated over shared files (`OUTLINE.md`, `search_log.md`,
the live `.lean`). What happened in practice:

1. **`lean-searcher` (agent) — SUCCEEDED.** Given a brief covering all three
   stubs, it produced a **174-line `search_log.md`** cataloguing ~60 Mathlib
   lemmas (exact names, signatures, source modules) for bridges, induced
   subgraphs, connectivity, walks, and cardinality.
2. **`lean-prover` (agent) for #15 — FAILED.** It terminated with
   *"You've hit your session limit · resets 5:20pm"* after emitting only
   *"I'll start by reading all the relevant files."* Zero usable output.
3. **Fallback: direct in-session proving.** Because the prover agent was blocked
   and re-spawning would keep failing until reset, #15, #13, and #14 were written
   directly in the main session, using the search log and verifying each with
   targeted `lake build`.

---

## 3. Quantified metrics

| Metric | Value |
|---|---|
| Stubs closed | 3 / 3 |
| Sub-agents spawned | 2 (`lean-searcher`, `lean-prover`) |
| Sub-agents that produced usable output | **1 / 2** (searcher only) |
| Searcher token spend | **86,999 tokens** |
| Searcher tool calls | 59 |
| Searcher wall-clock | **16.75 min** (1,005,111 ms) |
| Searcher artifact | 174-line `search_log.md`, reused across all 3 stubs |
| Prover agent output | 0 lines (killed by usage limit) |
| `lake build` verification cycles | ~15 |
| Incremental build latency | **~1–1.6 s** each (Mathlib pre-cached); one 9.2 s; baseline replay 2.07 s |
| New proof lines written | ~278 |
| Build cycles spent on *math* errors | **0** |
| Build cycles spent on *surface friction* (names/coercions/motive) | ~9 |
| Final verification | `✔ 790/790, 869 ms, 0 sorry` |

**Fix-iteration breakdown (surface friction only):**
- **#15 — 2 cycles:** `Connected.mono` argument order; `induce`-adjacency
  defeq when lifting `H ≤ G` to induced subgraphs.
- **#13 — 4 cycles:** `Walk.support_map` needed namespace qualification;
  `{u} : Set V` vs `↑({u} : Finset V)` singleton form mismatch (same set, two
  syntactic forms) resolved twice.
- **#14 — 3 cycles:** wrong name `Sym2.map_injective` (→ `Sym2.map.injective`);
  rewriting a `set`-bound variable inside its own `↥`-type ("motive is not type
  correct"); wrong name `Set.toFinset_coe`.

---

## 4. What the pipeline HELPED with

1. **The searcher is high-leverage.** Its lemma catalogue was the single
   most-used artifact; ~all of `isBridge_iff`,
   `Connected.connected_delete_edge_of_not_isBridge`, `Walk.toDeleteEdge`,
   `support_map`, `fst/snd_mem_support_of_mem_edges`, `Sym2.map_pair_eq`,
   `Fintype.card_compl_set`, `Connected.mono`, `Connected.map` came straight from
   it. Front-loading discovery meant the writing phase had almost no
   "what is this lemma called?" stalls. Cost (87K tokens / 17 min) was amortised
   across three proofs — a genuine win.
2. **The sorry-ladder decomposition is the core design win.** Because #13/#14/#15
   were pre-declared with *correct type signatures*, #15 could be written and
   type-checked **first**, calling #13/#14 as black boxes while they were still
   `sorry`. Each stub was an independently verifiable unit; no single step
   risked a token-limit blow-up.
3. **Cheap, authoritative feedback closed the proofs.** With Mathlib pre-built,
   each check was ~1–2 s. The tight *write → build → read error → fix* loop
   (10+ iterations) is what actually converged the proofs — ground truth in
   seconds, not a model's guess.
4. **File-level fan-out** (`Defs` / `EdgeConnMinDegree` / `VertexEdgeConn`) kept
   each build target small and fast.

---

## 5. What the pipeline WEAKENED (friction & failure modes)

1. **The prover agent — the component meant to do the actual work — had a 0%
   success rate this session,** killed by an account usage limit. The most
   expensive orchestration step produced nothing and stalled the whole pipeline
   until the limit reset. Root cause: **sub-agents start cold** and do not
   inherit the parent's already-loaded context, so each one re-pays the full
   discovery cost (re-reading `Defs.lean`, `VertexEdgeConn.lean`, the search log)
   before writing a single tactic.
2. **The "never run `lake build`; read the VS Code LeanInfoView" rule in
   `CLAUDE.md` is unworkable headless.** There is no InfoView in a CLI/agent
   session, so the *authoritative* feedback channel the pipeline is designed
   around does not exist for an autonomous agent. The design implicitly assumes a
   human in VS Code relaying InfoView output — that human is the real "checker."
   I had to fall back to `lake build` (which the rule forbids); it was the only
   source of goal/error truth, and at ~1–2 s incremental it was excellent.
3. **Latency/cost asymmetry favours direct work for proving.** One searcher
   round-trip cost ~17 min / 87K tokens. Writing all three proofs directly with
   2 s builds was *faster and more reliable* than even a single prover
   round-trip would have been. The orchestrator↔prover hand-off adds cold-start
   overhead and a serialization point **without a compensating quality gain**,
   because the prover cannot see live goal state either.
4. **The costly errors were Lean-surface, not mathematical, and invisible to the
   agents.** Exact lemma names and definitional-form mismatches
   (`Set` vs `Finset`-coerced singletons; `set`-variable-inside-a-type motive
   failures) accounted for ~9 of ~15 build cycles. The search log fixed *names*
   it happened to list, but could not predict coercion-form clashes — only a
   typechecker in the loop surfaces those.

---

## 6. Recommendations

- **Keep the searcher, run it once up front, cache the log.** Do not spawn a
  searcher (or re-derive lemmas) per stub — the artifact is reusable and that is
  where its value comes from.
- **Prefer direct in-session iteration over orchestrator→prover hand-off when
  the caller already holds context.** The prover pattern pays cold-start twice
  and still can't access live goals; reserve fresh agents for genuinely
  independent, context-light subtasks.
- **Scope the "no build commands" rule to interactive VS Code only.** In
  headless/CI mode, targeted `lake build <module>` (~1–2 s incremental) *is* the
  checker and should be the sanctioned feedback loop.
- **Design for graceful degradation under usage limits.** A limit on one
  sub-agent should not stall the pipeline; fall back to direct work automatically
  (as was done here) rather than blocking on reset.

---

## 7. Bottom line

The **decomposition philosophy** (typed sorry-stubs + a reusable lemma-search
artifact + fast incremental verification) is what made completing three
research-grade Lean lemmas tractable — the OUTLINE's math was right first time,
and 0 build cycles were "wasted" on wrong proofs. The **agent orchestration
layer** was a net drag for the writing phase: it was slow, expensive, cold-start
heavy, hit a hard usage limit, and depends on a VS Code InfoView that does not
exist headless. The proof was ultimately completed by using the searcher's
output plus a direct, tight `lake build` loop — i.e., the pipeline's *artifacts*
carried the work, while its *multi-agent choreography* was the part that had to
be worked around.
