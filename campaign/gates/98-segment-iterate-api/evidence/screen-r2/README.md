# Gate 98's screen on the audited trees (round 2, finding 2)

- **Trees:** `git archive bdc73ab1 -- TCSlib` (the base: the campaign's Lean after #196) and
  `git archive 7b5774fb -- TCSlib` (#202's audited head). Frozen copies, never worktrees.
- **Population** (`population.txt`): every `.lean` file of the base that mentions `Segment`
  (`git grep -l Segment bdc73ab1 -- 'TCSlib/*.lean'`), 17 files; the head gives the same 17.
- **Command:** `nice -n 10 python3 -I scripts/copy-text-screen-v3.py <tree> $(cat population.txt)`,
  under the screen lock, base then head (`status.txt`: exit 0, 991 s and 996 s).
- **Result:** 1,341 declarations, 778 pairs and 285,948 characters at both; `pairdiff.py` 0 new,
  0 gone (`pairdiff.txt`). The pairs with a `Contract/Basic` declaration on one side
  (`restricted.txt`) are the same 23 at both, and the same 23 as round 1's; one is
  `Segment.trans` against `Tautology`'s `tautDual_segment_add` (SG-1).
