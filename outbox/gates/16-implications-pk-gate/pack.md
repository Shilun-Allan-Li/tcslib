# Gate 16 · Implications: public-key encryption from RSA and from factoring

Round 1. Auditor Codex. Seyoon ruled on 2026-11-11 that RSA and Rabin go in one PR with one Codex audit.

- **PR:** draft [PR #292](https://github.com/Shilun-Allan-Li/tcslib/pull/292) at
  `33a616bcc14450b9e3110e4f8801abea1198b2fb` (branch `maint/pass-shelat-implications-pk`).
- **Target and base:** it targets `cryptography/pass-shelat-ch2-4` on base
  `33cb7ae74c8e6ac23ed5bb1875121eadfe0c2046`, the campaign after #291; later base commits are records only.
- **What it adds:** a new catalog layer, `TCSlib/Cryptography/Implications` (facade exported from
  `TCSlib.lean`), and its first module, `Implications/PublicKey.lean`.
- **Scope:** this is a combined statement and proof audit. The proofs are four-line compositions of published
  theorems.

## The two catalog entries

```lean
theorem exists_adaptiveCPA_of_rsa (H : ArithmeticFP) (hR : RSAAssumption) :
    ∃ S : FixedLengthPKScheme, S.msgLen = .var ∧ S.AdaptiveINDSecure .cpa

theorem exists_adaptiveCPA_of_factoring (H : ArithmeticFP) (hD : BlumDensity)
    (hF : FactoringAssumption) :
    ∃ S : FixedLengthPKScheme, S.msgLen = .var ∧ S.AdaptiveINDSecure .cpa
```

The source is [PS10], R. Pass and a. shelat, *A Course in Cryptography*, third edition, January 2010. The
relevant results are Theorems 53.2 and 57.2 (RSA), §2.12 and Theorems 61.8 and 63.10 (Rabin–Blum), Theorem 87.3
(Goldreich–Levin), Algorithm 104.3 and Theorem 104.4, the bitwise scheme of p. 103, and Definition 171.5.

## What to check

1. **Statements.**
   - Is each statement the right catalog endpoint per the Implications design (`implications/README.md`, in the
     bundle)? That means: a full, explicit assumption set; a meaningful message space; and the exact audited game.
   - Are all premises present? In particular:
     - `ArithmeticFP` is the arithmetic efficiency premise.
     - `BlumDensity` stays a hypothesis.
     - No hidden admission enters through a callee.
   - Does `FixedLengthPKScheme` carry the guarantees the module docstring claims?
     - uniform polynomial-time key generation and encryption;
     - polynomial-time decryption;
     - fixed-length ciphertexts;
     - perfect correctness.
   - Is `msgLen = .var` enough to rule out a vacuous witness?
2. **Proofs.** Each composes four published results:
   - `rsaTrapdoor_oneWay` / `rabinBlumTrapdoor_oneWay`;
   - `TrapdoorCollection.shiftParameter_oneWay`, shifting by 2 / 3;
   - `TrapdoorCollection.OneWay.exists_glPad_singleBitSecure`, with
     `rsaTrapdoor_shiftParameter_encD_length` / `rabinBlumTrapdoor_shiftParameter_encD_length` as the
     exact-width premise `henc`;
   - `BitPublicKeyScheme.SingleBitSecure.exists_adaptive_cpa`.

   Confirm the composition is sound, and that the shift does not weaken the guarantee: the scheme's
   parameter `n` is the security parameter of the adaptive game.
3. **Axioms.** Both theorems must print only `propext`, `Classical.choice` and `Quot.sound`. Inspect the full
   dependency chain, not just the wrapper: the design notes warn that a wrapper with no local `sorry` is not
   enough.
4. **Layering.** Implications imports construction modules, and nothing imports Implications except the root.
   Check the module and facade docstrings (`## Contents`, references), the namespace
   `Implications.PublicKey`, and that there is no `@[simp]`. The design notes' instruction not to publish RSA or
   Rabin wrappers "with the current impossible `henc` premise" is now met: `henc` is proved at the shifted
   parameters.
5. **Rule 10.** The proofs name only theorems. The seal probe re-elaborates both proofs with the main
   definitions sealed, together with a control.

## Evidence (`evidence/`)

- `build.jsonl`, `build-order.txt`: `Implications/PublicKey`, the facade and `TCSlib` pass with rc 0, 0 errors
  and no warnings. Each row records the source SHA-256, which matches `source-head.json`.
- `SealProbe.lean`, `seal-probe.log`: both proofs elaborate with `rsaTrapdoor`, `rabinBlumTrapdoor`,
  `shiftParameter`, `glPad`, `tdpBitScheme`, `SingleBitSecure`, `bitwise`, `padded`, `AdaptiveINDSecure`,
  `RSAAssumption`, `FactoringAssumption` and `BlumDensity` sealed. The only error is the intended control at
  line 33. The probe's `#print axioms` lines give the standard axioms.
- `screen-axioms.log`: the original composition screen.

## Findings delivery

Return `gate16-implications-pk-findings.md` as a Markdown file in this chat. For multiple evidence files, return a
ZIP. The user dispatches and merges.

| # | Severity | File and declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|

Severities:
- **blocker:** a false or unusable statement, or a scope violation.
- **major:** a missing premise, a vacuous or misleading endpoint, a hidden admission, a forbidden read, or
  necessary evidence that cannot be verified.
- **minor:** documentation or API defects.
- **note:** anything else.

Report the audited head and the counts by severity. The gate closes at zero blockers and zero majors.
