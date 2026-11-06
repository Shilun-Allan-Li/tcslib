# Gate 03g: round 2 resolutions — gate closed

- **Round 2:** findings `findings/gate03g-r2-findings.md`, verbatim, SHA-256 `5a207047fbdc5c62cbd95efc9e3c38200be0070657eecc287feb677d688e028f`; pin
  `1ea782b11617e15a51c3e2f6bd15dd0e3befbd95`; bundle `1ffe0fa5…`. **CLOSE: 0 blockers, 0 majors,
  1 minor, 2 notes.** Round 1: #3–#6 and M2 fixed; M3 scheduled; M4 recorded; #1, #2 and M1 "not
  resolved" only because of R2-1 (both majors repaired).

| Finding | Severity | Resolution |
|---|---|---|
| R2-1 | minor | **Confirmed.** The sketch's final aggregation applies `K ε_B(n)` to both branches; in the edgeless branch (`m = 0`, `K = 0`) one multi-value hiding gap remains, at most `ε_B(n) ≤ N² ε_B(n)` for `n ≥ 1`. The final `ε` is unchanged. **Records fixed:** erratum appended to `review/gate03g-review.md`; the 3-colouring fill notes carry the corrected term. **Lean docstring:** clean-up part 2, item L (unless the 3-colouring fill rewrites the sketch first). |
| R2-2, R2-3 | note | **No change.** |
