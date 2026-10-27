# A+: the interpreter startup as one published contract (design note, maintainer, 2026-10-25)

**The ruling (user, 2026-10-25, megafill C's D-3):** before B5a's uniform simulator is briefed,
harvest the startup that it shares with the interpreter core (`Turing.exists_ndInterpreterCore`,
`TuringMachine/NDCodeSimulator.lean`) into one published contract that both cite. The alternative,
pre-disclosing a below-90% pair between the two assembly bodies, was not taken. **The user then
asked for this note before any Lean.** It proposes the boundary, the statement and the vehicle. The
decisions it needs are at the end. **Ruled (user, 2026-10-25): the recommendation on all five** (a
maintainer API PR; `p` passive tapes with an embedding; existential roles; the core re-pointed in
the same PR; the PR opened after #164 and #165 merge).

## What the two machines share

The core (`NDCodeSimulator.lean:891`, proof lines 908–2384 at `a524c36f`) is one left-nested seam
composite of twelve phases. Phases 1–11 run from the native input `z = ⟨⟨bits t, α⟩, x⟩` to the
**threshold** of the hosted loop:
1. the header pass capturing `bits t` (the kit's `headerCapture_run`);
2. the input rewind (`inputRewindTM`);
3. the header pass capturing `α`;
4. the rewind of the counter capture (`rewindTM`);
5. its copy onto the loop's counter tape (`copyTM`);
6. the window copy `x.take t` (the kit's `exists_windowCall`);
7. a second input rewind;
8. the rewind of `α`;
9. the installation behind a release adapter (the kit's `installCall_releasePhase`);
10. the seam layout (the kit's `exists_layoutCall`);
11. the rewind of the window.

These phases' proofs run from line 1060 to 1856, about 800 lines; the threshold inventory
(1887–2047) adds about 160 more. Phase 12 embeds the core's own loop host (`ic_loopHost`, the
replay machine over H2) at the threshold, and with the final assembly it is about 330 lines.

B5a's route (`campaign/fills/b5a/drafts/b5a-fill-unisim.DRAFT.md`, "What this is") is phases 1–11
with two differences, and then its own loop (`h1HostedVerdictTM`, already proved in
`CodeSimulator`).

| | the core | B5a |
|---|---|---|
| installed machine | `(c.decode α).tm.replayTM` (the replay of the decoded NDTM: `k + 1` tapes, the stream last) | `F.machine (F.decode α)` (`F.k` tapes) |
| installer | `ic_table_call c`: `exists_replayCanonizer` through `FinTM.exists_installCallTM` | `F.exists_polyCanonizer` through `FinTM.exists_installCallTM` (the route probe's `b5a_install`) |
| passive tapes | one: the choice stream `s` on tape `j`, unchanged by the startup | none |
| time | `C(α) · (t + 1)`, and the prefix clause `C(α) · (t' + |x| + |bits t| + 1)` | `d · (|α| + |x| + t + 1)^d`, `d` uniform |
| after the threshold | `ic_loopHost`, the replay over H2 | `h1HostedVerdictTM`, the verdict over H2 |

Both installers have the **same shape**: one machine `CI`, uniform in `α`, which from `stateWord
CI.k α` reaches `stateWord CI.k (serializeK (M α))` with a first return within `cost α`. That
shape is exactly `exists_installCallTM`'s conclusion (`ic_table_call`, `b5a_install`). The startup
therefore needs the installer only through that contract. It never needs the canonizer, the code
scheme or the format.

## The proposed statement (a sketch; exact field lists are fixed in the PR)

Home: `Build/InterpreterStartup`, the startup kit's module. It is the kit's assembly, it already
imports the rows the phases use (or nearly: `Build/Rewind`, `Build/InputRewind` and
`Build/Catalog`'s `copyTM` to be added, all upstream of it), and its replay closure is small.

```lean
/-- **The interpreter startup** … -/
theorem exists_interpreterStartup {k : ℕ} (n : List Bool → ℕ)
    (M : ∀ α : List Bool, MultiTapeTM k Bool (Fin (n α + 1)))
    (CI : FinTM Bool) (entryI doneI : CI.State) (cost : List Bool → ℕ) (hCI : 0 < CI.k)
    (installs : ∀ x α : List Bool, ∃ T ≤ cost α, 0 < T ∧
      (∀ u, 0 < u → u < T → (CI.tm.runFrom
        (Cfg.ofWords (input := x) entryI (stateWord CI.k α)) u).state ≠ some doneI) ∧
      CI.tm.runFrom (Cfg.ofWords (input := x) entryI (stateWord CI.k α)) T =
        Cfg.ofWords doneI (stateWord CI.k (serializeK (M α))))
    (p : ℕ) :
    ∃ (K : ℕ) (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q) (U : MultiTapeTM K Bool Q)
      (entry done : Q) (ιP : Fin p ↪ Fin K) (jctr jwin jtbl jsm : Fin K) (A B : ℕ),
      ⟨the four roles distinct and outside ιP's range⟩ ∧
      ∀ (α x : List Bool) (t : ℕ) (ps : Fin p → ℤ → Option Bool),
        let z := pairEncode (pairEncode (Nat.bits t) α) x
        let start : Cfg K Bool Q z := ⟨some entry, 1, ⟨ps on ιP, blank elsewhere⟩, fun _ => 0, []⟩
        ∃ T, T ≤ cost α + A * ((serializeK (M α)).length + α.length + 1) +
                B * ((Nat.bits t).length + min t x.length + 1) ∧
          (U.runFrom start T).state = some done ∧
          (∀ u < T, (U.runFrom start u).state ≠ some done) ∧
          ⟨the threshold's fields: input head at 1, output `[]`, every head at 0;
            `jctr` holds `bits t`, `jwin` holds `x.take t`,
            `jtbl` holds `tableBitsK (M α).tr`, `jsm` holds `summaryCells none (unaryFin (M α).q₀)`;
            the passive tapes hold `ps`; every other tape blank⟩
```

**Consumers.**
- **The core** re-proves `exists_ndInterpreterCore` as the startup at `p = 1`, with `ps` the
  stream and `M α = (c.decode α).tm.replayTM`, `seamCompTM`-composed with its embedded loop host at
  the threshold. Phase 12 and the final assembly stay; phases 1–11 and the inventory go. The
  statement is unchanged; `NDCodeSimulator` shrinks by roughly 900 lines. The ledger keeps its
  form: the startup's `B`-term is the core's `|bits t|`/`min t |x|` part.
- **B5a** cites it at `p = 0`, with `M α = F.machine (F.decode α)` and `b5a_install` as the
  installer, composed with `h1HostedVerdictTM` at the threshold. The brief's route shrinks to the
  composition, the verdict and the polynomial ledger. The assembly-level pair with the core
  disappears, because neither body re-walks the startup.

**Size and cost (estimates).** The PR adds about 1,000–1,100 lines (the eleven phases generalized
over `M`, the installer and `p`) and removes about 900 from `NDCodeSimulator`. The replay covers
the kit's module's downstream closure: the module, `NDCodeSimulator`, `NTimeHierarchy` and the two
facades. That is 5 modules, the same as #162's, and none of them is heavy. One API gate goes with
it, with the usual seal and controls and a consumer probe at `p = 0`, which is B5a's.

## Decisions

1. **Vehicle.**
   - (a) **A maintainer API PR** (recommended). The proof exists. The work is generalizing a
     proved proof over three parameters, with the kit's lemmas already published. This is the
     startup kit's pattern (#162), at about twice its size. One gate.
   - (b) A statement PR with its gate, then a Codex fill of the proof, then the fill's gate. This
     takes two gates and a fill round. A fill also cannot re-point `NDCodeSimulator` outside its
     owned region, so a second PR would follow.
2. **Passive tapes:** `p : ℕ` with an embedding `ιP` (recommended; general, and `p = 0` costs
   nothing), or a single optional stream tape.
3. **Roles:** existential role indices with their distinctness facts (recommended; consumers embed
   their loops at them), or a fixed numeric layout (`K = 11 + k₁ + k₂ + CI.k + p` as in the core).
   Fixed numbers would expose `prefixCanonTM`'s tape counts in the statement.
4. **Re-point the core in the same PR** (recommended, the #153 and #162 precedent), or leave the
   core as it is and ledger the overlap until the dedup window. Leaving it keeps the copy that A+
   exists to remove.
5. **Timing:** after #164 and #165 merge (A1 adds nothing the startup uses; G4 is unrelated), so
   that the PR's base is quiet. The note does not depend on either.

## As built (PR #169), and the departures from this sketch (gate 79)

- **The serialization word** replaces `serializeK (M α)` in the statement, because `serializeK`
  lives in `CodeSimulator`, which would close an import cycle. Consumers convert by
  `serializeK_eq`.
- **The endpoint states less than the sketch's "every other tape blank".** It specifies the four
  role tapes and the `p` passive tapes, with their heads at `0`, and the input head at its first
  cell. The startup's other tapes are internal scratch with no stated contents, which a
  consumer's loop embedding leaves aside. A consumer that needs further clean tapes reserves
  them as passive tapes, started blank.
- **The core cites it at `p = 4`, not `p = 1`:** the stream, the loop's two banks and the loop's
  capture.
- **B5a will cite it at `p = F.k`, not `p = 0`.** Its hosted verdict `h1HostedVerdictTM F.k`
  needs the initial configuration's `F.k` mirrored work tapes blank, with their heads at `0`
  (`h1HostedVerdict_effect`'s `Rep`). The startup's roles supply the buffer (`jwin`, holding
  `x.take t`), the counter (`jctr`), the table (`jtbl`) and the summary (`jsm`). The junction
  reads `CodeSimulator`'s private loop lemmas, so B5a's pre-ship proves it, in a `CodeSimulator`
  overlay, before B5a issues. Gate 79's consumer probe shows the reservation at `p = F.k`
  (`b5aP_startup`, round 2). The loop then runs on the window, so B5a's acceptance argument
  must also bridge `x.take t` to `x` (gate 79, round 2, note 3; the B5a review).
  **Proved (maintainer, 2026-10-27):**
  `campaign/fills/b5a/drafts/b5a-fill-unisim/preship-junction/`, in the owned file's overlay,
  sealed over 20 definitions with their controls. `b5a_bank` gives the tape map from the
  startup's roles. `b5a_junction` reads the relabelled threshold as the embedded `vhostCfg`
  start, with the `Rep` on the window. `b5a_tail` runs the seam into the embedded verdict, to
  output `[answer]` deciding acceptance on `x` itself.
