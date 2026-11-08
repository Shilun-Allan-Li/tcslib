# Gate06C round1 resolutions

**CLOSED: PASS WITH MINORS,0blockers/0majors/4minors**, at frozen source
`3f6db40e1688c4a0bb922c9575dd3bd2157a650b`. Verbatim findings were committed first
at records636609a032bd48899dd5adbc3752353a3b2efc66:67,052bytes, SHA-256
`577621ca9f6fa665dbc6bd3150f4625ddf2b05d19b9f6021bf652c30c8580ac4`.
They arrived as user-supplied untracked local Codex Markdown; no auditor push
identity is invented. Issued records/exchange remain c81baa7712ab1b43357276ef5df138d02616c9d0 /
5928e06c02b382b63b9b384db89d0458b520f351. The incoming report remains unchanged.

| Finding | Maintainer disposition |
| --- | --- |
| C-01, minor | Accept a prose qualification, preserving the algorithm and all statements. For generated keys and n>0, both length checks force successful canonical pair parsing and the valid2n-bit tag. At n=0, the malformed four-bit0000 decrypts to the valid empty message; explicitly disclose this finite-prefix behavior. There is only one plaintext at zero. No new parsing guard is commissioned. |
| C-02, minor | Accept the first-discrepancy coupling with an always-reject-fresh-pair game. Rejected guesses reveal no random tag there; each candidate succeeds with probability at most2^(-2n), giving q/2^(2n) per bit-game. Repeated failed guesses in the real game do not have constant conditional success probability. Combining both bit-games can introduce fixed factors, so the sketch no longer promises an unjustified coefficient-one final advantage bound. The negligible-security statement is unchanged. |
| C-03, minor | Accept count-and-length phase normalization with canonical metadata/fallback. With k original moves and p=proverMoves, retain exactly p bounded real prover messages and append k-p honest-prover empty fillers. Do not force a cheating verifier's replies empty. This fixes real views and bounds every simulated prefix including pairing/index overhead. Handle k=0 or Q=0 by the exact empty-history view. Statistical post-processing gives Q times delta; no new simulator-shape premise is assumed. In3COL each padded six-move phase contains two real prover messages and one prover filler. |
| C-04, minor | Accept explicit equality testing in the hypothetical short-tag counterattack. Skip the refused challenge-equality branch and charge nonce/masked-message coincidences to the negligible failure probability (at most2/2^n in the random-pad model, plus PRF error). The attack is overwhelmingly successful; it is not unconditionally query-distinct. The actual whole-ciphertext tag algorithm is unchanged. |

The concrete proposals and frozen internal reviews are in review-r1-c/. The
combined A/B/C/D patch covers15 minor dispositions across13 files; it passes
joint application checking and exact noncomment-byte preservation. It remains
unapplied. No theorem/header/body/hypothesis/algorithm/cost/import/attribute or
admission was changed, and no new Lean check or proof completion is claimed.
The report's table says the private XOR lemma lacks a docstring; source already
has its formula docstring. This nonmaterial report inaccuracy is recorded without
editing the original or introducing a new source finding.

## Preserved scope and evidence limits

This is a statement/sketch/correctness gate. All13 direct Composability admissions
and their six derived admitted-dependent results remain; the3COL numerical
negligibility proof does not discharge generic repetition. No public-key CCA2
construction or many-challenge bridge follows. Fixed-length padded games retain
their explicit query-domain restrictions. CPA-only converses and distinct COPY/
bottom conventions remain as stated. Strict aborting simulation concludes the
stated statistical error, not a truncation theorem for expected-time simulation.

The bounded integrity review reproduces171 exact source sections,20 records,
all14 listed pack leaves,3,419 archived entries and eight recorded Composability
source-pass receipts. These are source/historical-run identity checks, not new
kernel runs. Common17 source failures,46 admitted-dependent identities and legacy
C3 observations remain disclosed. Root-export elaboration and combined post-S2
verification are not granted by this audit.

The auditor compared the exact supplied PS10 PDF and author PSV versions. Historical
publisher-byte/text identity is unverified. Official Goldreich reader content was
accessed, but its recorded raw PDF hash and published-edition comparison were not
verified; draft pagination is not transferred to the published book. Deferred
paper proofs were reviewed as maintainer sketches. No fresh primary-PDF access
or native run is claimed by these maintainer dispositions. Internal finite models
illustrate boundary cases only and do not supply Lean or hardness proofs.

All four gates now close at the frozen source: A0B/0M/2m, B0B/0M/5m,
C0B/0M/4m, D0B/0M/4m. Existing PR #232 still needs the comment proposals and
source-matched reconciliation/checks with merged S2 before landing. A clean
merge-tree preview is not verification. Cleanup remains deferred, and the strict
full221-path dependency screen finds no eligible direct crypto proof among39
targets; no new fill, audit or proof branch is prepared by this closure.

**Not yet clear to merge — 06C and all statement gates are closed; #232 still needs comment application and combined-source checks.**
