An API PR in `ClassNP/PClosure`: `Complexity.preimage_mem_NP`. If `L' ∈ NP` and `f` is polynomial-time computable, then `f ⁻¹' L' ∈ NP`; so `NP` is closed downward under Karp reductions (with `L ≤ₚ L'` by `f`, `L = f ⁻¹' L'`). The space hierarchy's corollary `SPACE_linear_ne_NP` needs it, to pull a padded language back along the padding reduction.

**Where it lives, and why it moved.** The first version put it in `ClassNP/Reductions`, beside `mem_P_of_polyTimeReducible`. That needed an import of `PClosure`, which brought `Mathlib.Tactic.Linarith` into every module downstream of `Reductions`. Linarith's closure activates Mathlib's simp lemma `Nat.cast_min`, and that broke one `simp` step in `ClassNP/TMSAT` (the merged-tree replay failed there, with 7 modules behind it). The user ruled (2026-11-04) that the theorem moves to `PClosure`, beside `preimage_mem_P`, and that `TMSAT`'s step is made robust in this PR.

**The changes**
- **`ClassNP/PClosure`:** the new theorem. The verifier for the preimage accepts `⟨x, u⟩` when `|u| ≤ C (|f x| + 1) ^ c` and `⟨f x, u⟩ ∈ V`: an intersection of a length test and a preimage of `V`, both in `P` by this file's rows. The certificate bound is `C (A + 1) ^ c (|x| + 1) ^ (d c)`. No new import.
- **`ClassNP/TMSAT`:**
  - `tmsat_take_computes`'s last step replaces `min a.length b.length` by its value in each case before `simp`, so no `min` is left for the simp set to reshape. It now elaborates with and without `Mathlib.Tactic.Linarith` in scope; the old step fails with it.
  - The lemma gains its proof sketch.
- **`ClassNP/Reductions`** is unchanged from the campaign branch.

**Checks** (against the snapshot of the campaign after #175)
- **Elaboration:** `PClosure` and `TMSAT` have 0 diagnostics; `preimage_mem_NP` uses only the standard axioms.
- **Rule 10:** the theorem, sealed over the six other-file definitions it reaches with the three `@[simp]` ones erased, has 0 diagnostics; the six controls close unsealed and fail sealed.
- **Freeze:** `PClosure` goes 16 → 17 public. `TMSAT`'s statements are unchanged; one private body changes.
- **Lint:** `ClassNP` 0 FAIL, the base's warnings. The policy linter is clean on `PClosure`; `TMSAT` keeps 9 inherited findings (it had 10, and the touched lemma's is fixed).

**Merge conditions:** gate 88's round 2, and the merged-tree replay of the two files' downstream closure (66 modules).

🤖 Generated with [Claude Code](https://claude.com/claude-code)
