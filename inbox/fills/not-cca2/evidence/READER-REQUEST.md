# Escalation: a challenge reader with explicit width transports

The mathematical target has not been refuted. This is an interface escalation at
checkpoint 2, before the challenge/decryption simulation can be assembled under
the required published-reader discipline.

## Reproduced failure

At the issue base, the following client compiles:

```lean
example (S : FixedLengthScheme) (atk : Attack) (b : Bool) (n : ℕ)
    (k : List Bool) (mm : Fin (n + n) → Bool) : True := by
  have hh := FixedLengthScheme.indImpl_challenge_none S atk b n k mm
  have hh' := heq_of_eq hh
  exact True.intro
```

Prepending only

```lean
attribute [local irreducible] FixedLengthScheme.inLens FixedLengthScheme.outLens
```

makes the `heq_of_eq hh` application fail: the published equation contains
the native `Fin (n+n)` input and native `Fin (S.ctLen.eval n)` answer, whereas
`indImpl` is typed using `S.indSpec n`'s input and answer families. Their
identifications currently depend on definitional reduction of the sealed lengths.
The published propositional length equations are available, but the tested direct,
input-cast and heterogeneous-equality routes did not discharge this conversion
without reopening the foreign definitions.

- `ReaderBefore.lean`, `logs/reader-before.log`: PASS.
- `ReaderAfter.lean`, `logs/reader-after.log`: expected FAIL at `heq_of_eq hh`.
- `attempts/OracleFromPRF-challenge-transport.lean` and
  `attempts/Seal-challenge-transport.lean`: the full attempted consumer with an
  explicit query cast and heterogeneous equality.
- `logs/seal-checkpoint2-fixed.log`, `logs/seal-checkpoint2-transport.log` and
  `logs/seal-checkpoint2-transport2.log`: successive width-conversion failures.

This is a failure of the tested interface consumption, not a claim that no
arbitrarily elaborate transport proof can be written.

## Smallest proposed provider correction

Add the following reader beside `indImpl_challenge_none` in **OracleSecurity.lean**.
It leaves every definition and the target statement unchanged and spells both
width transports explicitly:

```lean
theorem indImpl_challenge_none_cast (S : FixedLengthScheme)
    (atk : Attack) (b : Bool) (n : ℕ) (k : List Bool) (mm : Fin (n + n) → Bool) :
    S.indImpl atk b n k 2
      (cast (congrArg (fun d => Fin d → Bool) (S.inLens_two n)).symm mm) none =
      (ProbComp.sample (S.enc.Coins n)).bind fun r =>
        let c := S.encryptAt n k (if b then (splitHalf mm).2 else (splitHalf mm).1) r
        .pure (cast (congrArg (fun d => Fin d → Bool) (S.outLens_two n)).symm c, some c) := by
  rfl
```

The prototype in `ReaderProposal.lean` uses the temporary name
`proposed_indImpl_challenge_none_cast`. Its provider-side proof and a client under
sealed `inLens`, `outLens` and `indImpl` both compile. Its printed axioms are exactly
`propext`, `Classical.choice`, `Quot.sound`; there is no admission.
See `logs/reader-proposal.log`.

The prototype is evidence for review, not an authorized production change or part
of `patches/` or `src/`. The issued scope permits only `prfScheme_dec` as a reader
addition. A maintainer can publish this additional reader and issue a continuation
base before the fill resumes. The Dec interface may need analogous transports,
but no such additional change is requested as a demonstrated requirement here.
