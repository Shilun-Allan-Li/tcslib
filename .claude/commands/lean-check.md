# /lean-check

Check the current state of lean_proof/Main.lean: sorry stub count, and any errors reported by the VS Code LeanInfoView.

**Do not run `lake build`, `lean`, or any build command.** Error and goal state come from the VS Code LeanInfoView panel.

## Usage
- `/lean-check` — report sorry stub status and ask user for LeanInfoView output
- `/lean-check fix` — check, then attempt to auto-fix simple errors based on LeanInfoView output

## Instructions

---

**If no argument or just `lean-check`:**

Use the `lean-checker` agent:
"Read lean_proof/Main.lean, count sorry stubs, and produce a sorry-status report. Then instruct the user to open the file in VS Code and read any errors from the Lean InfoView panel. Ask the user to paste the LeanInfoView output so you can map errors to sorry stubs and suggest fixes."

Display the full report from the checker.

---

**If argument is `fix`:**

1. First run the `lean-checker` agent for the sorry-status report and to collect LeanInfoView output from the user.
2. For each error in the report that is "simple" (wrong lemma name, missing import, obvious type annotation):
   - Use the `lean-prover` agent to apply the fix directly. Pass it: "Fix the error on line [N] in lean_proof/Main.lean: [error description]. The suggested fix is: [suggestion from checker]. Do not change any sorry stubs — only fix the specific error."
   - Ask the user to check LeanInfoView again after each fix.
3. Stop before any error that requires mathematical reasoning — those need `/lean-step N`.

Report: which errors were auto-fixed, which remain and need manual attention.

---

$ARGUMENTS
