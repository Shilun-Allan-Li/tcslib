# Sub-agent `probe` notes (gsw-6b-statements)

Worktree `/home/user/sub/probe` (detached), olean tree `/home/user/oleans/probe`, `.lake/packages`
linked to the lead's. Every Lean process ran under the shared pool
(`python3 -I /home/user/ev/tools/lead/pool_run.py <label> <log> -- bash /home/user/ev/tools/probe/run_probe.sh <file>`);
no `lake` command was run.

## Timeline
1. Start at statement head 292ed483 (checkpoint 1; O2 head dd84941f), oleans = prefix closure + 4 GSW modules.
   - P3 (O2), P1 (selector), P2a (PBP, kernel), P4 (decryption formula) written and run here; the GSW
     files they import (`Branching`, `DecryptFormula`, `Scheme`, `BitEncoding`) are unchanged between
     292ed483 and the final head a855e111 except one docstring rewrap in `Branching.lean` (lead's message).
2. Lead message: statement series rebased, final head a855e111 (checkpoint-1 head 57815173).
   After the running Lean steps finished: `git checkout --detach a855e111…` and re-seed
   `rsync -a --delete /home/user/oleans/lead/TCSlib/ /home/user/oleans/probe/TCSlib/`
   (297 lead oleans built from sources byte-identical to a855e111; `/home/user/ev/subagents/seed2-check.txt`).
   All probes are re-run at the final head (see probes/README.md for the final runs).
   - `rsync` is not installed on the host: the re-seed was done as the equivalent copy
     `cp -a /home/user/oleans/lead/TCSlib /home/user/oleans/probe/TCSlib.new`, swap, remove the old tree;
     `diff -rq /home/user/oleans/lead/TCSlib /home/user/oleans/probe/TCSlib` printed nothing (581 `.olean`
     files). Worktree `git rev-parse HEAD` = a855e111f3dd31e1d4664117618813dff544cb6d.
3. Pool: size 3 (`/home/user/pool/size`), shared with the lead's root build and seals. `timeout` around
   `pool_run.py` counts the wait for a slot, so several early "timeouts" of scratch tests were slot waits,
   not computations; later runs use no `timeout`.
4. `#eval` mechanics (why the probes carry their own strict evaluators):
   - `homEvalPBP`/`homEvalFormula` fold closures (`Fin w → Ciphertext P` states): `#eval` recomputes the earlier
     steps at every entry access, so cost is exponential in the program length (a 2-instruction program at
     `q = 5` did not finish in minutes). A first fix that re-materialized the closure state (`let a := Array.ofFn …;
     fun i j => a[i][j]`) was no better (and a `by simp [a]` index proof inside it looped at elaboration).
   - Final evaluator (`EvalA.snippet`): fold over a **strict array accumulator** (`toArr`/`ofArr`, `@[noinline]`),
     proved equal to the library definition through its readers only (`evalA_eq` via `homEvalPBP_eq`,
     `BranchingProgram.evalWith_eq`; `formulaA_eq` via `homEvalFormula_eq`; `bootNANDA_eq`, `bootGateA_eq`
     via the three `bootGate` case readers; `fheEvalA_eq` via `fheEval_eq`; `levelGateA_eq` via
     `levelGate_of_lt`/`_of_le`; `leveledEvalA_eq`, `leveledEvalCircuitA_eq` via `leveledEval_eq`,
     `leveledEvalCircuit_eq`). So every `#eval` evaluates the library definition itself.
   - Progress of long `#eval`s is streamed to `<probe>.progress` files (Lean's messages only appear at the end).
   - Kernel `decide` cannot reduce anything built with `Nat.clog` (well-founded): `decryptFormula`,
     `nandFormula`, `decDepth`, `bootNAND`; nor `barrington` (well-founded). Those are `#eval` only.
5. Memory incident: the first P2b (kernel `decide` of G2's witness check at q = 256 over 12 cases) reached
   13.2 GB RSS and was killed by the OOM killer (pool log: probe-P2b rc=137). It may have pressured other pool
   jobs at that moment. P2b was rewritten to `#eval`. Peak memory of every other probe run: see README.md.
6. Lead: maintainer review moved the heads (O2 5bd5ada5, final 2c974b5f, then 8f92fe7d after the
   `Nat.clog_le_self` fix in G16's sketch). On "re-seed ready": `git checkout --detach
   8f92fe7d53967bc488a4075fb38210e7d40b9031`; `rm -rf /home/user/oleans/probe/TCSlib; cp -a
   /home/user/oleans/lead/TCSlib /home/user/oleans/probe/TCSlib`; also `TCSlib.olean`;
   `diff -rq` empty, 1,451 module oleans + the root (lead: 1,452 modules built from sources identical to
   8f92fe7d, /home/user/ev/build/root-final/summary.txt). Pool size now 2. All final probe, census and
   clash runs below are at 8f92fe7d.
7. Lead's order (pool size 2, one slot for probes): long `#eval`s strictly one at a time, each capped at
   25 minutes (`tools/probe/run_capped.sh`): P5a (bootNAND, 4 pairs: 16.7 min, complete), then P6b (smallest
   parity-twin circuit `twoC`, all inputs), then P5b (`xorPad`: XOR + one fan-in-0 + one fan-in-1 gate).
   The earlier P6b (xor/odd layered + `leveledEvalCircuit` AND) and the q = 4096 noise part of P2c were
   stopped to free the pool (partial results kept and marked).
8. Pool use (from /home/user/pool/pool.log, labels `probe-*`): 94 acquisitions, about 4.4 slot-hours up to
   21:42 UTC. Peak memory: 5.72 GB (P2a kernel `decide`, first run), 5.60 GB final P2a; every other run
   ≤ 3.3 GB; one OOM incident, 13.2 GB (first P2b, killed, rewritten) — see item 5.

## Lead's note (end of the sub-agent's run)
The `probe` sub-agent stopped at about 22:33Z on an API usage limit, after writing `probes/README.md` and finishing the
census, clash/shadow and duplication work. Its two capped runs (P5b `fheEval`, P6b `leveledEval`, 25 minutes each) were
re-run uncapped by the lead from the same sources at 8f92fe7d, under the pool (labels `lead-probe-P5b_FheEval`,
`lead-probe-P6b_LeveledCircuits`), outputs `probes/*.uncapped.log`, `*.uncapped.run`, progress appended to
`*.progress`; results in REPORT.md § 10.
