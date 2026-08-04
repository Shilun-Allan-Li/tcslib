<!-- generated-by: proofmatch informalization (not_in_text) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching.lean :: SwitchingLemma2.encode_go_wellformed -->
<!-- origin: boolean-ch04-dnf-switching-lmn round-7 verdict not_in_text (0.86) -->

# The Razborov encoder's auxiliary output is well-formed

**Claim.** Run the encoder `razborovEncode.go` on a DNF `f` of width ≤ `w`
(any fuel, any path `P`, any restrictions), starting from an empty
accumulator. Its auxiliary output is always the rendering (`triplesToAux w`)
of a list `ts` of triples `(position < w, direction, marker)` with

1. at most `|P|` entries, and
2. `marker = true` on the last entry (when `ts` is nonempty).

**Proof.** Induction on the fuel, generalizing the path and restrictions.

- *Empty cases* — fuel exhausted, path empty, no clause of `f` survives the
  restriction, or the chosen clause has no free literals: the encoder emits
  nothing; take `ts = []`.
- *Main case* — the encoder processes one surviving clause `t`, then recurses:
  - Every recorded position indexes into `t`, and `|t| ≤ width(f) ≤ w`, so
    positions are `< w` (`processClauseLits_aux_idx_lt`).
  - The clause's recorded block is nonempty, and marking its last entry
    (`markLast`) renders, under `triplesToAux`, exactly as the `(w, false)`
    terminator the encoder appends (`triplesToAux_markLast`).
  - The output splits as this block followed by the recursive output
    (`encode_go_acc`); the induction hypothesis gives a well-formed
    `ts_rec` for the tail. Take `ts = markLast block ++ ts_rec`.
  - *Length:* block entries consume path steps one-for-one
    (`processClauseLits_len_add`). *Final marker:* it is `ts_rec`'s last
    (true by IH), or the marked block's last when `ts_rec = []`.

**Why it matters.** This is the decodability invariant behind the `(4w)^d`
count: every auxiliary string parses back (`parseAux`) into at most `d`
triples over a `4w`-letter alphabet (used by `exists_aux_injection`).
