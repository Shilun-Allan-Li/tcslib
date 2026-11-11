# Gate 12 · CPA pilot statements

Round 1. Auditor Codex. Draft [PR #287](https://github.com/Shilun-Allan-Li/tcslib/pull/287) at
`135d54511dc0e5c42d93d1d680bf1f26c6aba5cc` on branch `maint/pass-shelat-cpa-pilot`, targeting
`cryptography/pass-shelat-ch2-4` on base `ed0f723871e0fd65e674bcf3f55c7e0ee173fdf5` (the campaign
after #284–#286).

This is a **statement audit**. It runs before any fill. It covers the two admitted statements,
the two corollaries proved from them, and three new reader lemmas. These are the first steps of
the Implications endpoint "multi-message IND-CPA public-key encryption". Seyoon ruled on
2026-11-11 for the route: two generic theorems, then compose. The endpoint game is
`FixedLengthPKScheme.AdaptiveINDSecure` (Gate 09, merged in #284), and it is not changed here.
The source is [PS10], R. Pass and a. shelat, *A Course in Cryptography*, third edition,
January 2010: Definition 171.5, and Algorithm 104.3 with Theorem 104.4 and p. 103.

## What to check

1. **`FixedLengthPKScheme.INDSecure.adaptive_cpa`** (`PublicKey/AdaptiveCPA.lean`).
   - Is it true for every `FixedLengthPKScheme`, with exactly these hypotheses?
   - Check the cap semantics of `adaptiveIndImpl`: a challenge past the cap repeats the latest
     ciphertext; with cap 0 the reply is zero. Check also the history-based refusal of `Dec`
     (vacuous under CPA), a zero cap, and polynomial `q` and `cap`.
   - Is the hybrid sketch sound? In particular:
     - the endpoints `H_0` and `H_cap` equal the `b = false` and `b = true` experiments;
     - the advice index `i⋆(n)` comes from `exists_advantage_hybrid_gap`;
     - the reduction is built by T2 (`exists_interactiveHandlerMachine`), with its outer-query
       budget;
     - the `cap(n)` factor is handled by `Negligible.polyExpr_mul`.
   - Can a fill complete it through published interfaces only? Name any missing reader.
2. **`BitPublicKeyScheme.SingleBitSecure.bitwise_padded_cpa`** (`PublicKey/BitwiseCPA.lean`).
   - Is it true, with the padding bound `hL` for `S.bitwise` and `hmsg : n ≤ L(n)`?
   - The adversary chooses its messages after seeing the public key. The module docstring says
     that n-bit ensemble `Secure`, whose messages are fixed in advance, would not suffice. Is that
     right, and is single-bit security the right premise?
   - Check the bit-hybrid sketch: the endpoint hybrids `H_0` and `H_n`, `n = 0`, and the reduction
     `D` on `⟨pk, c⟩` with its flip/zero output rule. `D` is built through T1, with `j⋆(n)` in
     the initial state and `n` encryption tapes as its seed. Check also the exact single-bit
     identity, and the coin layout of the bitwise encryptor (`bitwise_enc_runAt`,
     `bitwiseEncCoins_ofFn`).
3. **The corollaries.** `bitwise_padded_adaptive_cpa` and `exists_adaptive_cpa` are proved from the
   two targets.
   - Does `exists_adaptive_cpa` state a meaningful catalog-ready guarantee: `msgLen = .var`, the
     same key generator, adaptive CPA?
   - Is anything missing that the RSA and Rabin catalog theorems will need, such as correctness
     and efficiency? Those are carried by `FixedLengthPKScheme`.
4. **Readers.** `bitwise_gen`, `bitwise_enc` and `bitwise_dec` must state the definition exactly.
   Each should be public, not `@[simp]`, and have a docstring with its formula.
5. **Rule 10 and duplication.**
   - No statement or proof reads another file's definition. The evidence includes a seal probe of
     both corollaries with a control.
   - Nothing duplicates an existing public TCSlib or Mathlib result. Compare with
     `PublicKeyScheme.Secure.multiMessageSecure`, `SingleBitSecure.bitwise` and
     `AdaptiveINDSecure.single`.
6. **Placement, imports, facade exports and docstrings.** Policy §§1–3 apply.

## Evidence (`evidence/`)

- `replay.jsonl`, `replay-order.txt`: the 15 modules downstream of the change, rc 0, through the
  library root and `audits/pass-shelat/Checks`. `sorry` warnings are exactly the two targets.
  `replay-after-docfix.jsonl` rechecks the 8 modules after the final docstring wrap.
- `SealProbe.lean`, `seal-probe.log`: both corollaries elaborate with `padded`, `bitwise`,
  `ofPadded`, `INDSecure`, `AdaptiveINDSecure`, `SingleBitSecure`, `runAt`, `pairEncode` and
  `pairFstD` sealed. The only error is the intended control at line 27, which reads `bitwise`
  through its body.
- `axioms.log`: the readers use standard axioms. `exists_adaptive_cpa` additionally depends on
  `sorryAx` through the two admitted targets, as intended.

## Findings delivery

Return `gate12-cpa-pilot-findings.md` as a Markdown file in this chat. For multiple evidence
files, return a ZIP. The user dispatches and merges.

| # | Severity | File and declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|

Severities:
- **blocker:** a false or unusable statement, or a scope violation;
- **major:** a missing hypothesis, a statement too weak or too strong for its consumers, a
  forbidden read, a duplicate public result, or necessary evidence that cannot be verified;
- **minor:** documentation or API defects;
- **note:** anything else.

Report the audited head and the counts by severity. The gate closes at zero blockers and zero
majors.
