# Gate 38 · resolutions, round 1 · CLOSED

Codex's verdict is **CLEAR**, with no findings (0/0/0/0).
- **Findings:** `findings/gate38-derand-findings.md`, SHA-256 `a375dfc1c746a27942fae29c8bf0646788ac9f1278825387aaf663ee059f8b90`.
- **Audited head:** `c27005d67298f79c785a4e8ac1648da0a67d3614`, records `24f44052`, exchange `4b6ee799`.

Codex confirmed the following.
- **H17 holds as stated.** One machine gives both clauses. The fuel is `Nat.bits (2^w)` and the terminal rank is included. `R+2 ≤ 3R` is used, and `final_bound` is not applied to exponential fuel. The envelope uses the same budget.
- **The DTIME corollary** goes through `mem_DTIME_iff` only.
- **Theorem 180.1 holds:**
  - the integer root schedule;
  - the expanded output length `P(s) > s`;
  - one non-uniform bad-input distinguisher, with a uniform bound past `max(N,12)`;
  - margins of 7/12 and 5/12, using `half_lt_randProb_iff`;
  - eventual `2^{n^ε}` time, with earlier lengths absorbed into a constant.
- **Shared files:** they gain exactly E1–E3 and SR-01. `polyTimeComputable_find` and `final_bound` are unchanged.
- **Rule 10:** the only failures are the 20 F-01 ones (11 old plus 9 in E1), with no other failing declaration. This is ruled debt, DW-5.
- **Duplication:** no further undisclosed duplication.
- **Documentation:** LE-doc is correct.
- **Axioms:** standard. Admissions go 26 → 23.
- **Integration:** the combined build covers all 694 modules.

**Gate 38 is CLOSED.** #326 is clear to merge. Merge order: #326 and #327 in either order, then #324 last.
