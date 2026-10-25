# Gate 74: the merged-tree replay

After #161 merged, the campaign branch was merged into #162 (`e984516b`, "Merge the campaign
branch (after #161) into lean/startup-kit"); the merge changes none of the kit's four files. The
kit elaborates with no diagnostic against `oleans-lu2api` (`elab-InterpreterStartup-lu2api.out`).

`replay-lkit.sh`: the four changed files' downstream closure (`down-lkit.txt`, five modules) at
`e984516b`, chained from `oleans-lu2api`, fresh oleans into `oleans-lkit`. **Passed (user,
2026-10-25): 5 of 5, 0 failed; static-equal (1 sorry warning, `ntime_hierarchy`)**
(`replay-lkit.log`, `replay-lkit-static.txt`).
