# B8 fill (maintainer): `exists_not_timeConstructible`

The target ([AB09, Exercise 3.5]) is filled by the maintainer, following the B1 light half's
precedent: the proof came from the pre-ship research route check. The drafted B8 brief's
probe already closed the whole route (`audits/evidence/b8/B8RouteProbe.lean.txt`), so the
proof went straight into `Diagonalization/NotTimeConstructible.lean` and no agent batch was
issued. Like any fill, it goes to a **fill gate**.

## The route (flagged appendix in the target's docstring)

- **Witness.** `T n := n + [HALT (str n)]` at the campaign's scheme
  `TimeHierarchy.code`, over the dyadic enumeration. `rank s := codeBitsNat (s ++ [true]) − 1`
  and `str n := (n + 1).bits.dropLast`. Only `str (rank s) = s` is needed.
- **Stages (i)–(iii)** are compiled by `Turing.codePrim_machine`, the primitive-recursive
  compiler of `MathlibBridge` (the `CircuitComplexity/UHaltMachine` precedent). The emitter
  is `s ↦ 1^(rank s)`, written as a mapped range. No machine is hand-built.
- **Stage (iv)** is the audited equality test read on the one bit where the two candidates
  differ: the low bit of `(T (rank s)).bits` exclusive-or the rank's parity, branched with
  `FinTM.exists_cond`. That bit is the halting bit, so no two-word comparator is needed.
- **The bit identity** `(codeBitsNat (s ++ [true])).bits = s ++ [true]` comes from
  Mathlib's `Nat.digits_ofDigits` and `Nat.digits_two_eq_bits`, through a new bridge
  `codeBitsNat = Nat.ofDigits 2`. There is no induction on bits, so it is not a third copy
  of the private `bridgeNumber_bits` (MathlibBridge) or of UHaltMachine's numbering.
  This costs one flagged import, `Mathlib.Data.Nat.Digits.Lemmas`.

## Verification

- **Freeze** (`audits/logs/b8-fill-freeze-lint.log`). The target's statement is unchanged.
  Only its body changed, plus 14 new private helpers (the `ntc` prefix). There are no new
  publics. The module status reads "proved". Lint gives 0 FAIL, 0 WARN.
- **Axioms** (`audits/logs/b8-fill-axioms.log`):
  `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`.
- **Duplication** (`audits/logs/b8-fill-screen-{before,after}.txt`). The drafted brief's
  population gives 605 → 616 declarations, and 376 → 376 pairs with an identical list.
  **New copies: none.**
- **Replay** (`audits/logs/b8-fill-replay.log`). 2 modules, `NotTimeConstructible` and the
  `Diagonalization` facade, at `a96a6ab9`; the user ran it from the maintainer's command.
  **0 errors and 0 sorry warnings.**
- **Size.** 235 lines.
