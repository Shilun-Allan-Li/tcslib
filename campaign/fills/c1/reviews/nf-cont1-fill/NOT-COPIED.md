# What in this folder should not be copied into the records

**What to copy:**
- `REVIEW.md` and `NOT-COPIED.md`;
- `scripts/`;
- `out/`, without the items below;
- `land/NDNormalForm.lean.txt`;
- the probe sources listed as kept below.

Copy every `.lean` file under `probe/` with `.txt` appended (`*.lean.txt`, the records'
convention), so that no tool treats it as a module. The `out/` files name the paths that existed
when they ran: `rvprobe/<name>.lean` in the head worktree, copied from `probe/`.

| Path | Why not copied | How to reproduce |
|---|---|---|
| `wt-head/`, `wt-base/` | The review's worktrees at `825ee3f5` and `348781a3`, each with a `.lake/packages` symlink. `wt-head/rvprobe/` held the elaborated copies of the probes. Removed at the end of the review | `git worktree add --detach <dir> refs/deliv/c1-nf-cont1` (or the base); then link `.lake/packages` |
| `oleans-clone/` (1.1 GB) | The copy-on-write clone of `oleans-leqc3` that received the head's, then the landed file's, four downstream `.olean`s (out/24, out/29j). Deleted at the end of the review | `cp -cR $S/oleans-leqc3 <dir>`; then `tools/leanelab-o.sh` per module, in out/23a's order |
| `out/04-diff-U0.txt` (141 KB) | `git diff -U0` of the base and the head | `git diff -U0 348781a3 825ee3f5` |
| `out/13a-refs.txt` (36 KB) | The 457 refs grepped for names, at the time of the grep | `git for-each-ref --format='%(refname) %(objectname) %(objecttype)'` |
| `out/14a-tacargs.tsv`, `out/14b-idents.txt`, `out/14e-simpq-idents.txt`, `out/14f-resolve.txt`, `out/14h-inspection-table.tsv` (about 170 KB together) | Working tables of the inspection; out/14g and out/14i summarize them | `scripts/tacargs.py` on the head (lines 705–3328); the resolution tail in `probe/NFResolve.lean`; the classification in out/14g's command |
| `out/16b-probe-run.txt` (113 KB) | The `#check` echo of the worker's 908-check probe: 0 errors, the two deprecation warnings | elaborate `probe/NFProbeExt.worker.lean.txt` (as `.lean`) with `tools/leanelab.sh` |
| `out/18c-comment-text.txt` (29 KB) | The new region's comment and docstring text, extracted | out/18b's command |
| `out/25b-consolidation.diff` (28 KB) | `git diff ba46b709 825ee3f5` | that command |
| `probe/NFSeal.lean`, `probe/NFSealCtl_sealed.lean`, `probe/NFSealCtl_unsealed.lean`, `probe/NFSrcCtl_sealed.lean`, `probe/NFSrcCtl_unsealed.lean`, `probe/land/*` | Generated copies of the module (about 185–200 KB each) with the 257-definition seal block and the controls | `python3 -I scripts/mkseal.py <owned file> out/11-seal-candidates.txt <NFSealDefs.txt> <dir>`; the source controls are `probe/src-controls.lean.txt` appended (out/12f's command) |
| `probe/NFAudit.lean`, `probe/NFLand.lean`, `probe/NFLandAudit.lean`, `probe/NFLandSeal.lean`, `probe/NFAllCons.lean`, `probe/NFSimpQ.lean`, `probe/NFResolve.lean` | Generated: the head or landed module, alone or with a tail, or with asserted replacements (NFAllCons: E1 alone; NFSimpQ: 34 `simp` calls turned into `simp?`) | `scripts/mk_audit.py` (NFAudit, NFLandAudit); `scripts/mkseal.py` (NFLandSeal = `probe/land/NFSeal.lean`); `cp land/NDNormalForm.lean.txt` (NFLand); the inline Python of out/22d, out/14c and out/14f |
| `probe/NFProbeExt.lean`, `probe/NFProbeExt.worker.lean.txt` | Byte-identical copies of the delivery's `evidence/probe/NFProbeExt.lean` | `cp` |

**Keep:**
- `probe/NFExact.lean`, written by hand: the `exact?` probe of out/22c (X01–X14);
- `probe/NFDownAx.lean`, written by hand: the downstream axioms of out/24e;
- `probe/src-controls.lean.txt`, written by hand: the 41 source controls of out/12f;
- `probe/seal-set.txt`: the 257 sealed definitions;
- `land/NDNormalForm.lean.txt`: the tested landed file, git blob
  `5723152d424b4de35a10fd77446fa912083db412`, SHA-256 `3da2779c…3b43`;
- `out/29a-landing-edits.diff`: the landing PR applies it;
- `scripts/landing_edits.py`: it regenerates the landed file from the head, with every edit
  asserted.

**Large but worth keeping:** `out/08-audit.txt` and `out/29c-land-audit.txt` (58 KB each). They
hold every axiom print, the census, the walk (141 TCSlib constants) and the seal candidates.

**Not run:** the full v3 screen. Another review's screen held the machine-wide lock throughout. The
restricted run (`scripts/screen-nf.sh`, `screen-nf-pairs.py`) is in `out/20-screen-nf.*`.
