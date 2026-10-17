# B6-F1: stopped on a binding-route conflict

**Status: 0/1; stopped before phase 1. No Lean source was changed.**
This is a diagnostic archive, not a completed fill or a checked partial proof.
`Turing.exists_stepClockTMVia` remains sorried at the original pin.

The user's instruction was to stop and report if the brief conflicts with the
repository. The prescribed proof route needs arithmetic bridges that are private
at the pin, while the brief prohibits private citations, re-proving counter
arithmetic, and unfolding the relevant definitions. I stopped rather than relaxing
those rules. This is an API/brief conflict, not a counterexample to the theorem.

## Verified input and base

- Uploaded brief SHA-256:
  `b6f55f0adeafe38f477759b420ebbc6f0c3e01f253a14ace88e82b7ffd0dc6df` — matches.
- Cloned `complexity/arora-barak-ch3-4`, not `main`.
- The ancestor check passed against the fetched campaign head
  `73424fa10c56d4f66d08f1905a0f75f4e9c6b972`.
- Created `fill/b6-stepclock` at exactly
  `70b503b49760b65817a3bce4b876dc466c32235c`; HEAD remains there.
- No rebase, merge, cherry-pick, push, or PR.
- The repository brief differs from the attachment only by the literal
  `@ANCESTOR@` placeholders. Replacing them with the commissioned pin reproduces
  the uploaded bytes exactly. This is not the obstruction.

See `evidence/provenance.log` for the commands, exit statuses, and hashes.

## Escalation E1: the arithmetic interface does not support the binding route

All source references below are at the pin, in
`TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean`.

| Required step | Available implementation at the pin | Conflict |
| --- | --- | --- |
| Debit: underflow means the word is all false; success preserves width | `counter_dec_spec`, line 393 | Private. The reference debit uses it at lines 855 and 907. |
| Rounds: a successful physical decrement produces the next `counterWord` | `counter_word_decrement`, line 479 | Private. The reference rounds proof uses it at line 1183. |
| Relate optional decrement to the next frozen word | `counter_word_succ`, line 416 | Private. Deriving it directly relies on unfolding `counterWord`. |
| Timeout: connect zero value to underflow | `counter_dec_zero`, line 421 | Private. `counterWord_value` alone gives the value, not this decrement condition. |
| Timeout: identify the exhausted frozen word | `counter_word_exhausted`, line 530 | Private. The reference proof uses it and `counter_dec_zero`. |
| Exact accumulated time after appending a debit | `counterOverhead` is a definition at line 386; the reference proof unfolds it at line 1210 | No public zero/successor equation is supplied; rule 10 forbids that unfolding. |

For example, route step 2 needs precisely the bridge already implemented as:

```lean
private lemma counter_word_decrement (w : List Bool) (r : ℕ)
    (hr : r < Nat.ofDigits 2 (w.map Bool.toNat)) :
    decFixed (counterWord w r) = some (counterWord w (r + 1))
```

The obstruction is a concrete composition gap:

1. `decrementTM_run_succ_ofCfg` (line 272) requires
   `decFixed w = some v` as a hypothesis.
2. `counterWord_value` (line 459) supplies only the binary value of a frozen word.
   `counterWord_length` (line 439) supplies only its width.
3. The existing bridge from those facts to the needed decrement hypothesis is
   private, as shown above.
4. The brief says counter arithmetic is cited, never re-proved; ground rule 7
   repeats that prohibition. Ground rule 10 restricts citations to public
   declarations at the pin and prohibits unfolding definitions in `CounterLoop`.
5. Copying the private lemma, accessing its generated private name, unfolding the
   definitions, or silently changing the route would therefore violate the brief.

The import probe checks that the listed declarations resolve; it does not check
these missing bridges. Its successful pre-ship run does not establish that the
supplied route can be completed under the restrictions. The pre-ship overlay
leaves the debit and both final clauses as stubs.

This is not a claim of formal unprovability from every conceivable combination
of the library's theorems. It is a specific missing interface in the mandatory
route, with its existing implementation and the restrictions identified.

## Additional conflict to resolve with E1

Ground rule 10 forbids unfolding any definition in `CounterLoop`, except the
decrement table for the two stated lift obligations. Yet the prescribed proof of
`sc_lastLayout` in `tools/home.lean.txt` contains:

```lean
simp [clockCfg, lastEmb]
```

`lastEmb` is defined in `CounterLoop.lean` at line 617. Thus the supplied home
block itself needs an explicit exception or a public equation for that embedding.
The uploaded brief simultaneously says to take that prescribed block first.
I did not choose an unstated exception.

The generic debit also needs the field behavior of `Cfg.decodeSymbols` and
`Cfg.liftOver`. The reference debit unfolds these definitions, while rule 10
forbids unfolding definitions in `SymbolLift`. The supplied public overlay
transport returns a `Cfg.liftOver` expression, but the source file has no matching
overlay/shadow field API. This should be clarified in the same repair.

## Requested maintainer repair

Expose the existing counter arithmetic bridges (including zero/successor cost
equations), and either expose the required embedding/overlay/shadow equations or
explicitly permit their definitional projections. Then issue a revised pin and
brief. Alternatively, explicitly authorize the specific local bridge proofs and
definitional reductions, with a duplication disposition. No such repair was made
in this delivery.

The planned promotion candidates `sc_debit` and `sc_clockTM` remain unimplemented.
No new declaration, appendix, status change, or external proof citation was added.

## Verification and delivery checklist

| Item | Result |
| --- | --- |
| Phase reached | Before phase 1; no prescribed block or glue installed |
| Source scope and freeze | Empty tracked diff; all declarations and docstrings byte-identical |
| Source size | 218 lines; 5 public declarations; 0 private declarations |
| New R3-row/S-private citations | None; diff is empty |
| New copies | None; no source edits |
| Base sorry list | Copied verbatim; 28 declarations in the supplied base inventory, not independently elaborated |
| Dependency inventory | 21 TCSlib modules, including StepClock; saved in `evidence/import-closure.txt` |
| Cache initialization | Attempted `lake exe cache get`; exited 1: `could not detect the configuration of the Lake installation` |
| Bootstrap / final sweep | Not run; no successful sweep is claimed |
| Axiom prints / import probe / lint | Not run |
| Sanity examples | Pending; supplied file is an explicit status marker |
| New open private stubs | None; original public target still contains its original `sorry` |
| Axiom walk | Not run; no new proof or modulo claim |
| Format-patch series | Empty because HEAD equals the base; command exited 0 |
| Git bundle | Not supplied: Git refuses an empty bundle; recorded in `evidence/bundle.log` |

The initial cache failure is recorded separately from the route conflict. It was
not investigated further after the stop condition was established; it is not a
claim that the required Lean version is unavailable.

The archive includes the unchanged target and supporting pinned sources, the
uploaded brief, the original home/glue/probe inputs, the order list, source-search
evidence, check-status logs, and checksums. Files under `pinned-inputs/` are
unmodified reference copies, not proposed changes to another batch's files.

## Duplication screen

The unchanged prescribed flattened before-screen completed with exit 0:

```text
declarations screened: 907; copy pairs (target reproduces >= half of source): 662; reproduced text: 187,245 chars
```

Its complete output reproduces the committed base byte-for-byte after removing
the base header. See `evidence/screen-before.txt` and
`evidence/screen-before-status.log`.

An after-screen was not run: no edit occurred and work stopped before phase 1.
`evidence/screen-after.txt` records that status rather than presenting a copied
before-screen as an independent run. There are no new cross-file or in-file pairs
to disclose because every source byte is unchanged.
