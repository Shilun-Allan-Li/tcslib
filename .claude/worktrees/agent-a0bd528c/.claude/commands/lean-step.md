# /lean-step

Fill in a specific sorry stub in lean_proof/Main.lean, or split an oversized stub.

## Usage
- `/lean-step <N>` — fill in SORRY #N with real tactics
- `/lean-step split <N>` — split SORRY #N into smaller sub-stubs
- `/lean-step review` — run the reviewer/checker on the full file
- `/lean-step all` — attempt to fill all remaining stubs (use carefully — each is done sequentially)

## Instructions

Read the argument after this command.

---

**If a step number N is provided:**

1. Verify `lean_proof/Main.lean` and `lean_proof/OUTLINE.md` exist. If not: "No proof in progress. Run `/lean-prove [theorem]` first."

2. Verify SORRY #N exists in Main.lean:
   ```bash
   grep -n "SORRY #$(printf '%02d' N)" lean_proof/Main.lean
   ```
   If not found: "SORRY #N not found. Run `/lean-status` to see available sorry numbers."

3. Check if SORRY #N is already marked `[x]` in OUTLINE.md. If so: "SORRY #N is already filled. Did you mean a different number?"

4. Check `lean_proof/search_log.md` — if it has relevant entries for this goal type, mention them to the user before delegating.

5. Use the `lean-prover` agent to fill this stub. Pass it:
   "Fill in SORRY #[N] in lean_proof/Main.lean. Read the outline in lean_proof/OUTLINE.md, read search_log.md for available lemmas, and verify with lean after filling."

6. After the prover completes, run `lean-checker` to confirm:
   "Run a quick check on lean_proof/Main.lean to confirm SORRY #[N] is correctly filled and no new errors were introduced."

7. Report:
   ```
   SORRY #N: [filled / blocked / too large]
   Current errors: [N errors or 0]
   Sorrys remaining: X

   [Next action suggestion]
   ```

---

**If the argument is `split N`:**

Use the `lean-orchestrator` agent:
"SORRY #N in lean_proof/Main.lean is too complex. Split it into 2-3 smaller sorry stubs with more structure. Preserve all other sorrys and re-number if needed. Recompile to verify."

---

**If the argument is `review`:**

Use the `lean-checker` agent for a full report:
"Run a complete check of lean_proof/Main.lean. Report all errors, all remaining sorrys, and suggested next actions."

---

**If the argument is `all`:**

Work through all remaining (unfilled) sorry stubs sequentially from lowest to highest number.

For each one:
1. Invoke `lean-prover` on that stub
2. Invoke `lean-checker` to verify
3. If the prover is blocked (reported ⚠️ BLOCKED): stop and report which stub blocked, then ask the user how to proceed
4. Continue to the next only if the previous succeeded

Report final status after all attempts.

$ARGUMENTS
