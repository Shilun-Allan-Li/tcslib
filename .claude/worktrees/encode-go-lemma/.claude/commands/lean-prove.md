# /lean-prove

Start a new Lean 4 proof or manage an existing one.

## Usage
- `/lean-prove <theorem statement>` — start a new proof with a sorry-skeleton
- `/lean-prove --assemble` — (not needed for Lean; Main.lean is always the live file)
- `/lean-prove --reset` — archive current proof and start fresh
- `/lean-prove --from <papers/name.md> <theorem_name>` — start from a formatted paper

## Instructions

Read the argument following this command.

---

**If a theorem statement is provided:**

1. Check if `lean_proof/Main.lean` already exists.
   - If it does: "A proof is already in progress. See `lean_proof/Main.lean`. Did you mean to `/lean-prove --reset` first, or continue with `/lean-step`?"

2. If starting fresh:
   - `mkdir -p lean_proof`
   - First run the `lean-searcher` agent to identify relevant Mathlib imports and any obviously useful lemmas. Pass it: "Search for Mathlib lemmas relevant to this Lean theorem: [theorem statement]. Focus on identifying the correct imports and any automation (ring/omega/simp) that might close sub-goals."
   - Then run the `lean-orchestrator` agent. Pass it the full theorem statement and the search findings: "Create a sorry-skeleton for this theorem in lean_proof/Main.lean and write lean_proof/OUTLINE.md. Search findings: [findings]. Theorem: [statement]"

3. After the skeleton is created, run the `lean-checker` agent to verify it compiles: "Check lean_proof/Main.lean and report compilation status."

4. Display the result:
   ```
   Sorry-skeleton created with N stubs.
   Compilation: PASS (sorry warnings only)

   Run `/lean-step 1` to begin filling in the proof.
   Run `/lean-status` to see the full outline.
   ```

---

**If the flag is `--reset`:**

```bash
mkdir -p lean_proof/archive
timestamp=$(date +%Y%m%d_%H%M%S)
mkdir -p lean_proof/archive/$timestamp
mv lean_proof/Main.lean lean_proof/OUTLINE.md lean_proof/search_log.md lean_proof/error_log.md lean_proof/step_*.md lean_proof/archive/$timestamp/ 2>/dev/null
echo "Archived to lean_proof/archive/$timestamp/"
```

Confirm: "Previous proof archived. Ready for `/lean-prove [new theorem]`."

---

**If the flag is `--from <papers/name.md> <theorem_name>`:**

1. Read the specified paper file and find the theorem.
2. Extract the candidate Lean signature from it.
3. Proceed as with a normal theorem statement, using the paper's signature.

$ARGUMENTS
