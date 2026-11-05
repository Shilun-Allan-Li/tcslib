# Algorithm 99.1's `Dec` guard: evidence (2026-11-05)

- **The commit:** `2f8ac2114c3c8feecfeef7a4e8d3519e3a9c9ad7` on
  `cryptography/pass-shelat-ch2-4-dec-guard`, one commit on top of the dedup commit
  `c7d5a6e22dfd48b603e57fc2def3b470ba170249`. It changes `Asymptotic/MultiMessage.lean` only.
  - `prfDecFun` first checks that the ciphertext is a pair of `n`-bit strings (`prfDecWF`), and
    otherwise outputs `1^{n+1}`, which decodes to no message.
  - `runAt_prfDec` takes the two length hypotheses.
  - The new `decodeFin_runAt_prfDec_of_not_wf` gives the refusal.
- **Why.** The evaluator `E` agrees with `F` only on `⟨s, x⟩` with `|s| = |x|`. Without the
  guard, `Dec` evaluated `E` on malformed ciphertexts, where it is arbitrary. For
  `E ⟨s, x⟩ = s` off that domain, a chosen-ciphertext query `⟨r, c⟩` with `|r| = n − 1` and
  `|c| = n + 2` (still `3n + 2` bits) returns `c ⊕ k`, so the key. Theorem 168.2 (CCA1), stated in
  prong C, would be false for such evaluators. It was found while stating prong C.
- **The checks** (`replay.log`): the dedup commit's olean tree, with `MultiMessage` and its
  dependents rechecked. The dependents are the `Asymptotic` facade, the root facade (imports only)
  and `audits/pass-shelat/Checks.lean`. **Both modules pass, with 0 errors and no `sorry`.**
- **Headline axioms** (`checks-axioms.log`): 291 prints, 54 through `sorryAx`. They are identical,
  declaration by declaration, to the dedup commit's.
