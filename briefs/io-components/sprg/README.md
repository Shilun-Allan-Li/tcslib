# io-sprg: dispatch pack for the structured-seed PRG job ([JLS26, §2–§4, Theorem 4.1])

One end-to-end Codex job in a local checkout on Seyoon's Mac (campaign `IOComponentsPlan.md`):
statements and proofs in one run, a **statements gate** on its first push (checkpoint 0, M0) and a
**proofs gate** on the final. Unit `io-sprg`, branch `fill/io-sprg`, delivery to
`inbox/fills/io-sprg/` on `exchange/pass-shelat-ch5-8`.

| File | What it is |
|---|---|
| `design-r1.md` | the design note the prompt points to: settled points (§0), source map (§1), layout under `TCSlib/Cryptography/Obfuscation/StructuredSeed/` and the Stage 2 crossings (§2), the parameter convention (§3), proposed statement shapes (§4), milestones M0–M5 (§5), risks, deviations, **open questions (§9)** |
| `duplication-sweep.md` | TCSlib and Mathlib names the job must reuse (MR), may reuse, or must not use, with file:line |
| `dispatch-prompt.md` | the prompt Seyoon pastes into Codex, with placeholders `<BASE>`, `<RECORDS>`, `<EXCHANGE>` |

**Size.** About 4,700–7,900 Lean lines in ~19 new files (central ≈ 6,000); M0 alone 1,800–2,600.
Every Stage 2 touch on the job's imports is additive or proof-level (design §2.4).

**Settled (Seyoon, 2026-11-18, records `0fec2589` and `a2bf4bac`).** Rounding by the maintainer
(design §3: one security parameter κ, ℓ = κ^E, n = ℓ^⌈d/2⌉, W = ⌊ℓ^{δ/2}⌋², √c = κ·⌊ℓ^{δ/2}⌋,
B = ⌈mκ/W⌉); exact laws with samplers as separate contracts, **no sampler bridge in this job**;
degree d, not p. 14's d + 1; subexponential security only through the Foundations/Subexponential
API (branch `foundations/subexp`, the job's base), core theorems as explicit-slack inequalities
between machines (LPN advantage in its own dimension ℓ), with negligible and subexponential
corollaries; NUPPT adversaries only.

**Open questions for Seyoon** (design §9; recommended option first; ★ = his vision matters most,
they fix what the FE ⇒ iO bootstrapping can consume):
★Q-S1 LPN hypothesis form (the construction's ℓ-indexed family via `LWE.Family`) · ★Q-S2 modulus
(deterministic p(κ)) · ★Q-S3 efficiency of Eval/Q_I (not asserted, deferred) · ★Q-S4 Def 3.3's
class (degree-d, composite form) · Q-S5 code home (`Obfuscation/` area) · Q-S6 reduction
arithmetic (proved machines, no `ArithmeticFP`) · Q-S8 gate repairs (relayed mid-run). Q-S7 is
withdrawn (settled).

**Maintainer, before dispatch.**
1. Get Seyoon's rulings on Q-S1–Q-S6 and Q-S8; write them to `rulings.md` here (with the
   rulings already in the plan); if any is not the recommended option, edit items 2–3 of the
   prompt (marked *Q-S…*).
2. Stage the source: `outbox/io-components/sources/jls26.pdf` (SHA-256
   `bb357e8d01cc0932899453f3d877b67b58f33253eabf2564854f8f38721e2f3d`) with a `SHA256SUMS`, shared
   with io-phfe (one copy); push the exchange; put that commit in `<EXCHANGE>`.
3. Commit this folder (with `rulings.md`) and a decision-log row in `IOComponentsPlan.md`; put that
   commit in `<RECORDS>`.
4. Put the head of `foundations/subexp` in `<BASE>` (`git rev-parse`; the tip of
   `cryptography/pass-shelat-ch2-4` once that PR has merged). Record the API's final names in
   `rulings.md` (the pack uses working names `SubexpSmall`, `SubexpHard`). If Lean moved since
   `0fec2589`, re-check the sweep's line numbers (and whether S2-A's `ProbComp.mul_prob_le_expect`
   is in).
5. Check that the host addendum and `lean-slot.sh` at `<EXCHANGE>` still hash to `02a6af16…` and
   `ff64d8d5…`, and that the bb1-sim tools at exchange `2467bc3b…` are reachable.
6. Tell Seyoon the two Codex jobs share the Mac with one Lean slot each (`io-sprg`, `io-phfe`).

**Not yet ready to dispatch — placeholders, the `foundations/subexp` base, the staged source and Seyoon's rulings are pending**
