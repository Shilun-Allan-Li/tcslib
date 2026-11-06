# RP-1: the rule-10 seal regenerated at the merged head (gate 107, minor 1)

The same generator as `../rule10/` (`mkprobes.py.txt`, output path changed) was run on #216's
merged head `485cfbab`, whose Lean equals the campaign after #216 merged (`e4e7a419`). It was run
over every module that imports one of the five home files, plus the three home files that see
another home: **53 modules** (`targets.txt`), now including `SavitchARM/Deepen`. Each copy carries
`attribute [local irreducible]` on every one of the seven definitions it can see, and each was
elaborated one at a time with `leanelab.sh` against `oleans-lcamp2` (`run.sh.txt`).

**Result: 53 of 53 exit 0, with 0 errors** (`probes-merged.out`, one `== <module> exit=N errors=N`
header per probe). The only other output is the campaign's existing `sorry` warnings, all in
`ClassPSPACE.TQBF`.
