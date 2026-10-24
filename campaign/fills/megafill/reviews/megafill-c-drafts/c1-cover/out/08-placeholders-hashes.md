# Check 8: placeholders the maintainer fills at issue, and every full hash

Raw greps: `out/08-placeholders.raw`, `out/08-hashes.raw`. Line numbers are the drafts' at
`6e8db28f`.

## The C1 draft (`c1-fill-replaycanon.DRAFT.md`)

| Line | Placeholder | Fill with |
|---|---|---|
| 3–7 | the `<!-- DRAFT … -->` comment | delete; the file moves to `campaign/fills/c1/briefs/c1-fill-replaycanon.md` (the cover's path, 22) |
| 9 | `⟨Megafill C, item N⟩`, `cover brief ⟨…⟩` | "Megafill C, item 1 of ⟨4, or fewer after drops⟩", `megafill-C.md` |
| 11–12 | "**Budget:** 3 hours (the cover's proposal)" | the issued budget, without "(the cover's proposal)" |
| 19, 52, 53 | `@ANCESTOR@` | the shared base (the inputs commit), by `git rev-parse` |
| 54–56 | blob `e2cdab7b46ef1dc50e36f2504d92e78913c5bb1d` | re-check at the shared base (`git rev-parse <base>:…NDCodeSimulator.lean`); it changes under Q-B1 (A) |
| 77 | `⟨BASE⟩` | the tip whose Lean content is the shared base's |
| 80–83 | `⟨IN-FLIGHT⟩` and its drafting note | the open PRs at issue; #156 now edits six files (`0e5f210b`), not only `Build/Seam`; drop "among them B5a" if B5a is dropped |
| 41–44, 400, 409, 443, 454 | the staged inputs (`inputs/`, `orders/`, `logs/`) | stage from the pre-ship folder as its README's last paragraph says, re-measured at the shared base |
| 217 | `⟨a.inputTape, …⟩` | not a placeholder (Lean anonymous-constructor syntax) |

No other `⟨…⟩` or `@…@` in the file.

## The cover (`megafill-C.DRAFT.md`)

| Line | Placeholder | Fill with |
|---|---|---|
| 3–7 | the `<!-- DRAFT … -->` comment | delete; the file becomes `campaign/fills/megafill/briefs/megafill-C.md` |
| 19, 33 | `@ANCESTOR@` | the shared base |
| 27–29 | `⟨Q-B1: …⟩`, `⟨Q-U1: …⟩` | the rulings and the merged PRs (each by number and merge commit), or remove the item (F10) |
| 37 | `this cover | ⟨…⟩` | **cannot be filled** (a file's own hash): delete the row; the dispatch message carries it (F8) |
| 38–41 | the item briefs' SHA-256 | `shasum -a 256` of each dispatch copy |
| 62–65 | the budgets | the issued budgets (D1 and Q-M2 may change C1's and B5a's) |
| 69–70 | `⟨Q-M2: …⟩` | the ruling's text (07-cover.md gives a wording) |

## The G4 draft (`s13d-fill-g4-cont4.DRAFT.md`)

| Line | Placeholder | Fill with | Listed by the report? |
|---|---|---|---|
| 3–8 | the comment (pre-ship "at `97299639`", "⟨SORRIES⟩ (30 …)", "⟨SCREEN⟩ (846/477 …)") | delete; the record is now `preship-6e761018/` (27 sorries) | yes |
| 6 vs 20, 76, 77 | `⟨ANCESTOR⟩` in the comment, `@ANCESTOR@` in the text | the shared base | yes |
| 10, 13 | banner `⟨Megafill C, item N⟩`, `⟨…⟩`, "**Budget:** ⟨…⟩" | item 4 (or renumbered), `megafill-C.md`, "the rest of the session" | yes |
| 79 | blob `1abbb871…` | unchanged at the drafting base and the tip (verified) | — |
| 96 | `⟨BASE⟩` | as for C1 | yes |
| 99, 149 | `⟨SNAPSHOT⟩` | the pre-ship's snapshot (`oleans-lslsk` at `6e761018`, or the issue-time re-run's) | yes |
| 100 | `⟨IN-FLIGHT⟩` | as for C1; #156 now edits `Build/Seam` (in G4's population) | yes |
| 505–506 | `⟨SCREEN: 846 declarations, 477 pairs, 136,473 characters at 97299639 …⟩` | the shared base's screen base (equal at `6e761018`; changes if #156 merges first) | yes |
| 551 | "**95 modules**" (not a placeholder) | **96** at `6e761018` and the drafting base (`Build/InputRewind`, #153) | **no** |
| 560, 567 | `⟨SORRIES⟩`, `⟨SORRIES − 2⟩` | 27 and 25 at the drafting base | yes |
| 573 | "33 WARN over 39 files" (not a placeholder) | **40 files** at `6e761018` (`lint-build.txt`) | **no** |
| 583–584 | `⟨the other modules' sorries at the issue: CodeSimulator, NDCodeSimulator, UniversalK at 97299639⟩` | `CodeSimulator`'s `exists_uniformSimulator`, `NDCodeSimulator`'s `exists_replayCanonizer`, `UniversalK`'s two (G4's base-sorries at `6e761018`) | **no** |

## Every full hash in these files (`git cat-file -t`, never typed)

| File:line | Hash | Type | Means what the text says |
|---|---|---|---|
| C1 draft 4; cover 4; C1 README 3; env README 3; report 12 | `77f1eb4fb74deb7a1ac7bae7bc4e98d5d0f9a532` | commit | the drafting base ("Backlog: megafill C's briefs handed to a drafting agent"); Lean equal to the tip `6e8db28f` and to `906a9d7b` (`git diff --name-only … -- '*.lean'` empty both ways) |
| C1 draft 55 | `e2cdab7b46ef1dc50e36f2504d92e78913c5bb1d` | blob | `NDCodeSimulator.lean` at the base and at the tip |
| G4 draft 79 | `1abbb8716d0450ea9b7cc10ef15e6204ed920b4a` | blob | `Build/ZoneRebalance.lean` at the base |
| report 6 | `1133762f39ea344b56e40d0c6e9af98eaf915bb0` | commit | the drafting brief's commit, an ancestor of the base |
| report 4 | `496ac104…cc3` (SHA-256) | — | the drafting brief's SHA-256: matches the file at the base and at the tip |

Short hashes (`77f1eb4f`, `6e761018`, `97299639`, `04164b21` = `fillinputs.py`'s blob) all resolve
and mean what their text says.

RESULT: all hashes PASS. Placeholders: one unfillable (F8), three G4 issue-time items missing from
the report's list (F11).
