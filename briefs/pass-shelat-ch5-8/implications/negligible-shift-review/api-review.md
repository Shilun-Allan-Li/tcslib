# Existing API for fixed right shifts of negligible functions

**No new lemma or proof block is needed.** At frozen Gate06 head `3f6db40e1688c4a0bb922c9575dd3bd2157a650b`, the public theorem `TCSlib.Cryptography.Negligible.comp_of_le` already proves the stronger closure property:

```lean
theorem Negligible.comp_of_le {μ : ℕ → ℝ} (hμ : Negligible μ)
    (φ : ℕ → ℕ) (hφ : ∀ N, N ≤ φ N) :
    Negligible fun N => μ (φ N)
```

Home: `TCSlib/Cryptography/ZeroKnowledge/NP.lean:288–297`. This is a public theorem, not a private helper. With `μ : ℕ → ℝ`, `hμ : Negligible μ` and `s : ℕ`, the exact existing term is:

```lean
hμ.comp_of_le (fun n => n + s) (fun n => Nat.le_add_right n s)
```

Its result is `Negligible (fun n => μ (n + s))`. It works for every fixed natural `s`, including zero, for signed real-valued functions, without a monotonicity assumption on `μ`. No consumer unfolds `Negligible` or another foreign definition; the term applies two published theorem interfaces.

The local pinned Lean 4.25.0 primary source `Init/Data/Nat/Basic.lean:369` gives `Nat.le_add_right : ∀ (n k : Nat), n ≤ n + k`, so the parameter order in the term above matches the actual Core API. No web source, guessed lemma name or tactic search was used.

## Finite-prefix convention and existing proof

`Foundations/Negligible.lean:57–63` defines negligibility by eventual strict bounds `|μ n| < 1 / (n : ℝ)^c`, with an arbitrary natural threshold for each exponent. The existing composition theorem chooses `max n₀ 1`. For `n` past it, `n+s ≥ n ≥ n₀`; the original bound at `n+s` applies, and `1/(n+s)^c ≤ 1/n^c` since `n ≥ 1`. Thus it preserves the current finite-prefix convention, including the harmless parameter-zero corner, without changing the definition or demanding a bound on every small parameter.

## Normalization design correction

The main-records `implications/normalization-design.md` currently says that no constant-shift negligibility lemma was found. Its requirement 4 is mathematically supplied by `Negligible.comp_of_le`; it need not be reproved twice or replaced by a narrower copied proof. A precise suggested replacement for the negative API claim is:

> No Collection/TrapdoorCollection parameter-shift constructor or one-wayness transport was found. The existing public `Negligible.comp_of_le` theorem in `ZeroKnowledge/NP.lean` already supplies constant right-shift closure, using `Nat.le_add_right`.

The theorem's current location is higher than the intended collection-normalization layer. Importing `TCSlib.Cryptography.ZeroKnowledge.NP` makes it available now; `Foundations.Negligible` alone does not export it. If the later lower-layer construction needs a foundational import boundary, the existing general theorem is the factoring candidate to relocate under its unchanged name, rather than duplicate its proof. This note does not propose or perform that move while Gate06 is frozen.

The shifted collection's run/coin transports, sampler membership/inversion correctness and one-wayness argument remain separate missing work. Reusing this elementary theorem alone proves none of those transports or an end-to-end PKE claim. No external job/gate/fill is proposed.

## Fingerprints and limits

- Frozen `Foundations/Negligible.lean`: SHA-256 `5e6d2c9e69dbfe012c36a92bad05ec27e691c044dae73a7277b9599902074e1a`.
- Frozen `ZeroKnowledge/NP.lean`: SHA-256 `a324cf2acd579a86946f857e8c69fcd8e3f96fb08efc03f1902d1b5c6ba354fe`.
- Inspected normalization design: SHA-256 `7c12f84dba4dfe31b35cc839a82de55e8e26c3cf742b21fae8eba7177d98089e`.
- Pinned Lean 4.25.0 `Init/Data/Nat/Basic.lean`: SHA-256 `74c62ccabe494d3d2325bce4472ec4fd3f4b12628e2bdc8273bc334025647c71`.

This was source/signature inspection only. The application term was not natively elaborated in this task. No Lean/cache/build command, other repository program, app, source edit, Git mutation or evidence mutation occurred. Only this ignored scratch note was saved; zero tactic blocks or new declarations were written.

**Not yet clear to merge — the API suffices statically, while the normalization transports and later serial verification remain outstanding.**
