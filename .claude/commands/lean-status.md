# /lean-status

Display the current state of the Lean proof: sorry stub progress, compilation status, and blockers.

## Usage
- `/lean-status` — show full status
- `/lean-status short` — one-line summary only

## Instructions

---

**If no argument or `lean-status`:**

Gather the following information directly (do NOT invoke full agents — use fast Bash + Read):

```bash
# 1. Count total and filled sorrys
echo "=== SORRY COUNTS ==="
grep -c "SORRY #" lean_proof/Main.lean 2>/dev/null && \
grep -c "sorry -- SORRY" lean_proof/Main.lean 2>/dev/null

# 2. List all sorry stubs and which are filled
grep -n "SORRY #" lean_proof/Main.lean 2>/dev/null

# 3. List open vs closed in OUTLINE.md
grep "SORRY #" lean_proof/OUTLINE.md 2>/dev/null

# 4. Check for compilation errors (quick run)
cd lean_proof && timeout 30 lean Main.lean 2>&1 | grep -E "^.*:.*: error:" | head -10

# 5. Check for blocked stubs in error log
grep "BLOCKED\|SORRY.*FAIL" lean_proof/error_log.md 2>/dev/null | head -10

# 6. Check search log entries
wc -l lean_proof/search_log.md 2>/dev/null
```

Read `lean_proof/OUTLINE.md` and `lean_proof/Main.lean` header to get the theorem name and strategy.

Display:

```
## Lean Proof Status: [Theorem Name]

Strategy: [from OUTLINE.md]

### Sorry Stubs
[ ] SORRY #01 — [description]       ← NEXT
[x] SORRY #02 — [description]       ← filled
[x] SORRY #03 — [description]       ← filled
[ ] SORRY #04 — [description]       ← BLOCKED (see error_log.md)
[ ] SORRY #05 — [description]

Progress: 2/5 stubs filled (40%)

### Compilation
[0 errors / N errors — run `/lean-check` for details]

### Blockers
- SORRY #04: blocked (see lean_proof/error_log.md)

### Search Log
[N entries in lean_proof/search_log.md]

### Suggested Next Action
Run `/lean-step 1` to fill the next open stub.
[or: Run `/lean-search "[description]"` to unblock SORRY #04.]
[or: All stubs filled! Run `/lean-check` to confirm 0 errors.]
```

---

**If argument is `short`:**

Just print one line:
```
[Theorem Name]: 2/5 sorrys filled | 0 errors | Next: /lean-step 1
```

$ARGUMENTS
