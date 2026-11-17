# Sub-agent `seal` notes (gsw-6b-statements, brief check 6, Rule 10)

## Environment and heads
- The worktree `/home/user/sub/seal` is always detached. Nothing was committed and no tracked file was edited.
  Probe, control and resolver sources are under the untracked `evidence-scratch/rule10/`; copies are under
  `/home/user/ev/rule10/`. Heads, in order:
  1. `292ed483`, the old checkpoint-1 head (`rule10/cp1/`, `rule10/o2/` at O2 `dd84941f`).
  2. `a855e111`, the first final head, on the lead's message (`rule10/final-bitenc/`, `rule10/final/`).
  3. `8f92fe7d53967bc488a4075fb38210e7d40b9031`, on "re-seed ready", the final head after the maintainer review
     (`rule10/r2/`). The O2 head is `5bd5ada5f42c5e1228ea84ad70f4d8c52a3644fd`. The intermediate head `2c974b5f`
     named in the lead's earlier message was superseded before any run.
- The olean tree is `/home/user/oleans/seal`. It started as the lead's copy at `292ed483`. It was re-seeded twice,
  at `a855e111` and at `8f92fe7d`, from `/home/user/oleans/lead/TCSlib/`.
  - The host has **no `rsync`**, so I used
    `rm -rf /home/user/oleans/seal/TCSlib && cp -a /home/user/oleans/lead/TCSlib /home/user/oleans/seal/TCSlib`,
    then `diff -rq` between the two trees: identical both times.
  - a855e111: 297 oleans. The lead's `seed2-check.txt` says 297/297 are built from a855e111.
  - 8f92fe7d: 1,451 oleans under `TCSlib/`; the root `TCSlib.olean` sits beside it in the lead's tree and is not
    needed. The lead's `/home/user/ev/build/root-final/summary.txt` says 1452/1452 are bound to 8f92fe7d.
- No `lake` command was run, and nothing was written to the olean tree. Every Lean process went through the shared
  pool: `xr/runner_pool.py` → `/home/user/ev/tools/lead/poollib.py`, running `lean -DmaxErrors=0` with no `-o`.
  This covers the collector, the seals, the controls, the resolver probes and the instance-kind probe.
- Pool size was 3 until the lead set it to 2, before the r2 runs.

## O2 identity (BitEncoding)
- `TCSlib/Cryptography/LWE/BitEncoding.lean`:
  - sha256 `ac627bf2…67d5` at `dd84941f` (old O2), `292ed483` and `a855e111`;
  - sha256 `74cf46e4…23a4` at `5bd5ada5` (new O2) and `8f92fe7d` (`r2/{o2,final-bitenc}/source-identity.tsv`).
- Its TCSlib closure (`LWE.Basic`, `LWE.Noise`) is unchanged from base to final.
- The tools key the source on a revision (`git show <rev>:<path>`), so BitEncoding was sealed at both O2 and final
  revisions every time. The request lists are identical: 9 rows, in all runs.

## What I ran (chronological)
1. `seal_pipeline.sh` for `o2` (rev dd84941f) and `cp1` (rev 292ed483, 5 owners), JOBS=2.
2. For `cp1`: controls (`xr/controls_full.py`), `scan_unfold.py`, `scan_resolve.py`, `xr/notation_check.py`,
   `xr/summarize.py`. The first `scan_resolve` run failed on all 5 probes, because `resolveGlobalName` takes an
   `Options` argument in Lean 4.25. I fixed the tool and reran; the failed logs were overwritten.
3. The `cp1/misc-instkind` probe: `Parameters.neZero_columns` is a theorem with instance=true;
   `fheView_fst`/`_snd` are theorems.
4. `run_checkpoint.sh` for `o2` (a full rerun replacing step 1's o2 output); this was the first test of the
   one-command path.
5. Checkout of a855e111 and re-seed, then `run_checkpoint.sh` for `final-bitenc` and `final` (11 owners, JOBS=3).
6. Checkout of 8f92fe7d and re-seed, then `run_heads.sh 5bd5ada5… 8f92fe7d… /home/user/ev/rule10/r2`
   (log `r2-run_heads.log`). Then `xr/compare_requests.py` against the a855e111 runs (`r2/compare-a855e111.txt`):
   52 probes compared, 0 different.

All results passed: every seal, control, scan and notation check, in every run (README.md has the tables).

## Pool use and memory
- 313 Lean runs released through the pool under `seal:` labels (`grep 'seal:' /home/user/pool/pool.log`).
- Exit codes: rc 0, or rc 1 for the expected negative controls and the 5 failed first resolver probes. No OOM, no
  crash.
- Peak RSS 2,989,120 KiB (about 2.85 GiB), `SealcoeB_…_GSW_Asymptotic`. Each run holds one slot.
- Wall time was dominated by waiting for slots during the lead's root builds. Probe times: 25–85 s each, about 2 s
  for unsealed controls and resolver probes.

## Tool changes
Every change is also recorded in each tool's header in `/home/user/ev/tools/seal/`.
- **Copied unchanged** from gsw-6a-statements: `xr/mkcollect.py`, `xr/CollectTemplate.lean`, `xr/touched.py`,
  `xr/build_seals.py`, `xr/build_controls.py`, `xr/request_payload_adapter.py`,
  `xr/legacy_request_payload_adapter.py`.
- **Adapted:**
  - `xr/mkseals_ab.py`, `xr/mkseals_coe.py`: when rev = HEAD, the git-show bytes are asserted equal to the
    worktree file.
  - `xr/sealsum.py`: install/EOF sums over chunk parts, `counts_ok`, a header line, the first error line per
    failing declaration, RSS and seconds.
  - `scan_unfold.py`: `OWN` lines and per-file hit counts.
  - `seal_pipeline.sh`:
    - tool paths;
    - the pool runner instead of the host lock;
    - scratch directory `evidence-scratch/`;
    - the collector run with no `-o`;
    - touched.json made in place, with a base-rev argument;
    - the olean tree from `$TCSLIB_OLEANS`.
- **New:**
  - `xr/runner_pool.py`: runner_full.py under poollib, with parallel submission.
  - `xr/controls_full.py`: consumer-file controls with an unsealed pretest and the full strict/coe harness.
  - `xr/notation_check.py`, `xr/summarize.py`, `xr/compare_requests.py`.
  - `scan_resolve.py`: the Lean-resolved scan for core/Mathlib definitions.
  - `run_checkpoint.sh`: one head and module list, one command.
  - `run_heads.sh`: the O2 and final set, one command.
- **Not used:** the other 6a tools, copied for reference only: `check.py`, `controls.py`, `liveness.py`,
  `runner_lock.py`, `runner_full.py`, etc.

## Open points
- None blocking.
- At these heads the new files still contain sorry'd theorems (counts in `seal-summary.tsv`, equal to the unsealed
  build). The seals check the statements and the proofs present now; filled proofs need a rerun, with the one
  command `run_heads.sh <o2> <final> <outroot>`.
