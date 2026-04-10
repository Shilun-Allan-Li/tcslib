# /lean-search

Search Mathlib 4 for lemmas, tactics, or definitions relevant to a proof goal.

## Usage
- `/lean-search "<description>"` — find lemmas by mathematical description
- `/lean-search "goal: <lean goal syntax>"` — find lemmas that close a specific Lean goal
- `/lean-search "name: <partial name>"` — find lemmas whose name contains a pattern
- `/lean-search "tactic: <goal>"` — identify which automation tactic closes a goal

## Instructions

Read the user's query following this command.

---

Use the `lean-searcher` agent to perform the search. Pass it:
"Search Mathlib 4 for: [user's query]. Save all findings to lean_proof/search_log.md (append, do not overwrite). Current proof context: [read lean_proof/OUTLINE.md if it exists and summarize relevant goals]."

---

After the searcher completes, report:

1. **Top recommendation**: the lemma name or tactic with exact Lean 4 syntax
2. **How to use it**: `rw [lemma]` / `exact lemma` / `apply lemma` / `simp [lemma]` / just `ring`
3. Confirm it's been logged to `lean_proof/search_log.md` for future use

If the search found nothing useful: suggest running `/lean-step split N` to break the goal into simpler sub-goals that automation can handle.

$ARGUMENTS
