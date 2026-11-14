# Gate 136 resolutions for #304

Round 1 audited `bd8cd565ce1c9999211173b237f9ff8eae3f3d62` and returned **CLEAR (0 blockers,
0 majors, 1 minor, 8 notes)**, recorded verbatim as `findings.md` (SHA-256 `7907822d6ae4770615f77b00acc512522b6a1aebae3df69099c6a21111b8458a`).

| Finding | Resolution |
| --- | --- |
| G136-01 · the wider copy screen's API sources were not in the carrier | **Fixed in the records.** `evidence/screen-wide-population/` now holds the eight population files at the campaign base `210d8748` (`GIT-BLOBS.txt` binds each to its Git blob; `SHA256SUMS`). Seven are identical at the PR head; the eighth, `Ladner.lean`, is the PR's own file, whose head version is the change itself. The screens are unaffected (Codex reproduced both byte for byte from the pinned sources). |

Notes G136-02 to G136-09 need no action. **Gate 136 is closed.**
