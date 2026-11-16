# Olean snapshot procedure (adopted 2026-11-16, Seyoon)

This procedure replaces the old practice: a fixed snapshot at base `eff2dcd0` (SHA-256 `457ba704…`), in-place builds with
backups, and a restore after every job. The olean trees `$SP/dl-oleans` and `$SP/dl-oleans-2` move to it once their
snapshot rebase to the tip completes. In 1–4, `T` is the current tip of `cryptography/pass-shelat-ch2-4`, and `$SP` is
this session's scratchpad.

1. **One complete snapshot at T.** Keep exactly one complete olean snapshot directory, outside any worktree, built at T. It
   holds every TCSlib module's `.olean`; it is not an in-tree `.lake/build`. Record its object map (module path → SHA-256 of
   the `.olean`), the SHA-256 of that map, T, and the module count. Record these in `snapshots.md` beside this file.
2. **Validate each PR by a merged-tree replay against the snapshot,** never against an older base:
   - compute the prospective merge with `git merge-tree --write-tree <T> <PR head>` and export only that tree's needed
     paths;
   - start the output directory as a hard-linked copy of the snapshot (`cp -al`, which costs almost no disk);
   - rebuild only the PR's changed modules and their downstream import closure, in dependency order. Use one `lean`
     process per module (`scripts/lean_check_tree.sh` style, never `lake build`), and delete each module's stale
     `.olean`/`.ilean` before compiling it;
   - require rc 0 and 0 `error:`/`error(` for every module, then write the output object map and record the prospective
     tree hash.

   Unchanged slow modules, such as `Complexity/ClassP/BinaryArith/DetMod`, are never rebuilt. Seals, axiom probes and
   controls run against the output directory.
3. **On merge:** fetch the branch and run
   `git diff --name-only <merge commit> <prospective tree> -- '*.lean' lean-toolchain lake-manifest.json`.
   If it is empty:
   - adopt the replay output as the new snapshot, by renaming it or hard-linking it under a new name;
   - rehash it on disk against its map, requiring 0 extra / 0 changed / 0 missing;
   - record the new map SHA-256, the merge commit as the new T, the module count and the date;
   - delete the previous snapshot's oleans, but keep its manifest.

   No extra build is needed.
4. **If the diff is not empty** (another PR merged in between and touched the same closure), do not adopt. Rerun the PR's
   replay on the new tip first. Better, do this before merging: when two open PRs share downstream modules, merge the one
   with the larger rebuild first, then re-replay the other. It rebuilds only its own closure on the new snapshot.
5. **Housekeeping:**
   - one Lean process per module;
   - never interrupt a running build;
   - work on one tree at a time;
   - pause if free disk falls below about 1 GB;
   - discard a replay output that will not be adopted as soon as its evidence is recorded.
