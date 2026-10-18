**B8 fill-gate audit — `Complexity.exists_not_timeConstructible`**

Audited object: the supplied 29-file packet for fill commit `a96a6ab9` (PR #36), against the attached base at `9b47f7b9`. This is an attachment-based audit. I applied the patch only to a temporary extracted copy; I did not access or modify the repository. No Lean elaboration was run.

The theorem and reduction pass the mathematical audit. Two documentation corrections are needed. The numbered findings below cover all nine brief items and all repository-side attestations.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | minor | `NotTimeConstructible.lean` · `exists_not_timeConstructible`, “Route as filled”; `b8-fill-pack.md` §3; `b8-fill-record.md` | The appendix incorrectly attributes stages (i)–(iii) to the primitive-recursive compiler. | `codePrim_machine` supplies the emitter, parity decider and two tails. Stage (iii) is the constructor `M` assumed in `TimeConstructible ntcT`; `exists_comp_partial` composes it with the emitter. No primitive-recursiveness of `ntcT` is asserted or used. | Say “Stages (i)–(ii) are combined in a compiled emitter; stage (iii) runs the assumed constructor.” Also prefer “a bit guaranteed to differ” to “the one bit where the two candidates differ”: incrementing an odd number can change several bits. |
| 2 | minor | `NotTimeConstructible.lean` · module design and target sketch; `ntcRank`, `ntcStr` | The inherited “length-lexicographic” / “1 prepended” description does not describe the implemented list order. | `rank [true,false] = 4`, whereas `rank [false,true] = 5`; ordinary lexicographic order with `false < true` puts these words in the opposite order. The implementation appends the high sentinel to a little-endian list. The private definitions and round-trip theorem are correct. | Describe a “little-endian dyadic enumeration,” with the high sentinel appended to the list. Keep the definitions and frozen theorem unchanged. |
| 3 | note | `NotTimeConstructible.lean`; attached base, patch and freeze log | Freeze and the 235-line size claim are verified. | Applying the patch reconstructs the attached head byte-for-byte. Git blob hashes are `5c074f42d339ea6e68addae7c9a049b5eb458d67` and `d289c0cfd0bc562d3d7b151e5ab8c3fd5f47e490`, matching the patch headers. The sole public signature is identical. Additions are exactly three private definitions and eleven private theorems; the other changes are the declared import, appendix/status text and target body. The head has 235 lines. | None. |
| 4 | note | `NotTimeConstructible.lean` · `ntcRank`, `ntcStr`, `ntcT`, `ntc_str_rank` | The witness is nonvacuous and needs only the proved direction of the round trip. | For every word `s`, `str (rank s) = s`. For every natural `n`, `n ≤ T n ≤ n+1 ≤ T (n+1)`. Thus the witness dominates the identity and is nondecreasing. Neither monotonicity nor `rank (str n) = n` is required by the statement or reduction. | None. |
| 5 | note | `NotTimeConstructible.lean` · `ntc_not_timeConstructible`, `ntc_bodd_T` | The implementation faithfully completes the audited HALT reduction, including odd-rank carries and empty output. | The emitter produces exactly `rank s` true bits. The assumed constructor outputs `(T (rank s)).bits`. Its low bit is `(rank s).bodd XOR HALT c s`. `exists_cond D B₁ B₀` complements precisely when the rank is odd, giving the singleton `[HALT c s]` on every input. The HALT case split is in `ntc_bodd_T`; the final split is on rank parity. | None. No hand-built counter, two-word comparator or runtime estimate is needed. |
| 6 | note | `NotTimeConstructible.lean` · `ntc_codeBitsNat_eq_ofDigits`, `ntc_bits_codeBitsNat_append_true`; `MathlibBridge.lean` · `bridgeNumber_bits`; `UHaltMachine.lean` · `bits_foldr_bit_one` | The digits bridge and flagged import are justified; this is not a third copied implementation of the inductive numbering proof. | The new code translates `codeBitsNat` to `Nat.ofDigits 2`, invokes `Nat.digits_ofDigits` with binary digits and final digit 1, and uses `Nat.digits_two_eq_bits` plus map injectivity. The older helpers instead induct using `Nat.bits_append_bit`. Their sentinel identity is mathematically equivalent, but the fill specializes shared Mathlib results rather than copying those recursive proofs or their machinery. | None. The duplication ruling is about reused proof implementation, not a claim that the mathematical identity is new. |
| 7 | note | `copy-text-screen.py`; all 12 supplied Lean population files; screen logs | Both reruns exactly reproduce the supplied screen logs. | Before: 605 eligible bodies; after: 616. Both have 376 directed pairs and 114,081 reproduced characters, with byte-identical pair lists and no pair involving the target. The 11-body increase is ten eligible new privates plus the newly eligible public proof; four short new privates are below the 60-character cutoff. | None, subject to the stated heuristic scope. |
| 8 | note | `b8-fill-axioms.log`, `b8-fill-replay.log`, `b8-fill-freeze-lint.log` | The supplied axiom, replay and lint records support the reported closure; their execution/freshness remain attestations. | The target axiom print lists exactly `[propext, Classical.choice, Quot.sound]`, without `sorryAx`. Replay records exit 0, zero errors and zero sorry warnings for the target and facade. Lint records 0 FAIL / 0 WARN over four files. I independently verified the source freeze, but did not reproduce these three executions: the packet lacks the complete import/build tree, facade and checking/lint scripts. | None under the pack’s explicit attestation boundary. “Proved” is consistent with the delivered body and supplied axiom record. |
| 9 | note | `B8RouteProbe.lean.txt`, `B8RouteProbe.out` | The probe supports the route, but is not itself a replay of the delivered digits-based proof. | `F6Probe.route_check` independently assembles the reduction and its supplied axiom output excludes `sorryAx`; merely importing/checking the old sorried target does not make it a dependency. The probe’s L1 uses induction, while the fill uses the new digits import. The probe explicitly places that alternative in a companion file not attached here. | None. Keep probe evidence separate from the delivered target’s axiom/replay evidence; probe execution and chronology are maintainer attestations. |

The duplication standard was applied beyond string matching. The equality

\[
\operatorname{codeBitsNat}(s\mathbin{++}[\mathrm{true}])
=(s\mathbin{++}[\mathrm{true}]).\operatorname{foldr}(\operatorname{Nat.bit},0)
=s.\operatorname{foldr}(\operatorname{Nat.bit},1)
\]

shows exactly why the new bit identity and `bridgeNumber_bits` express the same fact; `UHaltMachine` additionally reverses the input for its public numbering. This semantic overlap is real. The new implementation discharges the identity through the existing general Mathlib digits API, with a short representation bridge; it does not reproduce the earlier private induction/positivity family. The emitter similarly uses public primitive-recursion closure lemmas and the existing `codePrimBitsNat`, without copying UHaltMachine’s local bit/fold development. I found no new wholesale duplication requiring acknowledgment under failure mode 5. An unchanged screen alone would not establish that conclusion.

The three new definitions, read mathematically, are:

| Definition | Mathematical meaning | Comparison with its description |
|---|---|---|
| `ntcRank s` | Read the list `s` least-significant-bit first, append a highest bit 1 to preserve its length and zero bits, then subtract one. | Correct private description; the surrounding length-lexicographic description needs finding 2. |
| `ntcStr n` | Take the canonical little-endian binary digits of the positive number `n+1` and remove the last, highest bit. | Correct. Positivity ensures this removes a 1. |
| `ntcT n` | Add one to `n` exactly when the word `ntcStr n` is a halting instance for the fixed effective scheme `TimeHierarchy.code`; otherwise return `n`. | Correct. HALT is total as a classical Boolean function, including false on malformed pairs. This definition does not posit an executable halting oracle. |

For completeness, the reduction’s mathematical steps are as follows, using the pack’s `rank`, `str`, `T` and `c` abbreviations.

1. Every entry of `(s ++ [true]).map (fun b => if b then 1 else 0)` is below 2, and its last entry is 1. The two Mathlib digits lemmas and the representation bridge therefore give

   \[
   (\operatorname{codeBitsNat}(s\mathbin{++}[\mathrm{true}])).\mathrm{bits}
   =s\mathbin{++}[\mathrm{true}].
   \]

   The right side is nonempty, so its value is positive. Consequently natural subtraction cancels correctly:

   \[
   \begin{aligned}
   \operatorname{rank}(s)+1&=\operatorname{codeBitsNat}(s\mathbin{++}[\mathrm{true}]),\\
   \operatorname{str}(\operatorname{rank}(s))
   &=(s\mathbin{++}[\mathrm{true}]).\mathrm{dropLast}=s.
   \end{aligned}
   \]

2. The definition gives `T n = n` or `T n = n+1`. Hence

   \[
   \forall n,\qquad n\le T(n)\le n+1\le T(n+1).
   \]

   This proves the required growth condition independently of any machine assumption. The adjacent inequality also implies monotonicity by iteration, although the public theorem does not require it.

3. Suppose `TimeConstructible T`. Its literal definition supplies one finite binary machine `M` that, on every word `x`, halts with `(T x.length).bits`. Its particular bound `c₀ · (T x.length + 1)` can be discarded. `ntc_primrec_emit` and `codePrim_machine` supply the total emitter

   \[
   E(s)=\operatorname{map}(\lambda\_ .\mathrm{true},\operatorname{range}(\operatorname{rank}(s))),
   \qquad \operatorname{length}(E(s))=\operatorname{rank}(s).
   \]

   The partial-composition contract therefore gives a machine halting on every `s` with `(T (rank s)).bits`. The same compiler supplies the rank-parity decider and the two singleton-output tails. All of these compiled functions are primitive recursive; `T` itself is not submitted to the compiler.

4. Splitting the HALT Boolean into its two possible values and using `bodd (n+1) = !bodd n` gives

   \[
   (T(n)).\mathrm{bodd}
   =n.\mathrm{bodd}\mathbin{\oplus}\operatorname{HALT}(c,\operatorname{str}(n)).
   \]

   Substitute `n = rank s`, use step 1 and `Nat.bodd_eq_bits_head`, and obtain

   \[
   ((T(\operatorname{rank}(s))).\mathrm{bits}).\mathrm{headI}
   =(\operatorname{rank}(s)).\mathrm{bodd}\mathbin{\oplus}\operatorname{HALT}(c,s).
   \]

   If the rank is even, the unmodified head is `HALT c s`. If it is odd, the head is its negation, so the negated-head tail is `HALT c s`. `exists_cond` runs the selected branch on the original input `s`, not on the decider’s output. Thus the assembled `R` satisfies

   \[
   \forall s,\ \exists t,\quad
   R.\mathrm{ComputesInTime}(s,[\operatorname{HALT}(c,s)],t).
   \]

   This is precisely the computability assertion forbidden by `HALT_not_computable TimeHierarchy.code`. Therefore `¬TimeConstructible T`, and step 2 supplies the other conjunct of the unchanged existential theorem. All machine-existence steps use the attached public contracts; I have not independently kernel-checked this argument.

Adversarial checks:

| Instantiation | Calculation and result |
|---|---|
| Empty input `s = []` | `rank [] = 0`, `str 0 = []`. The empty word is not a `pairEncode` output, so `HALT c [] = false` and `T 0 = 0`. The constructor may output `0.bits = []`; `headI [] = false`, and the tail still outputs the required singleton `[false]`. |
| Trailing zero: `s = [true,false]` | The sentinel value is 5, so the rank is 4; `5.bits.dropLast = [true,false]`. The zero bit is retained. Reading the unsentinelled word as a number would collapse it to the value of `[true]`, but the implemented enumeration does not. |
| Odd rank with a carry: `s = [false,true]` | Its rank is 5. If its HALT bit is false, `T 5 = 5`, low bit true, and negation returns false. If its HALT bit is true, `T 5 = 6`, low bit false, and negation returns true. This is a case analysis, not an assumption that either HALT value is decidable. |
| Consecutive HALT bits true then false | The corresponding values are `T n = n+1` and `T (n+1) = n+1`; the downward change of the halting bit cannot violate monotonicity. |

An independent finite arithmetic check covered all 511 Boolean words of length at most 8 and both possible halting-bit values; the round trip and corrected output passed. This is supplementary checking, not Lean elaboration or a replacement for the universal identities. The existing `ntc_str_rank` and `ntc_bodd_T` already provide the important general sanity statements; no additional theorem is necessary to close this gate.

The source comparison used the authors’ [available book draft](https://theory.cs.princeton.edu/complexity/book.pdf?trk=public_post_comment-text), Chapter 3, exercise 5, whose indexed text asks for existence of a non-time-constructible function. Identity domination is a strengthening; no computability or monotonicity requirement is imposed on the sought witness. Direct retrieval of the published-text PDFs failed, so I do not claim a fresh page-image inspection of the 2009 edition. The attached P3.2 source comparison supplies the published Exercise 3.5 attribution. Mathlib’s official [digits definitions](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/Digits/Defs.html#Nat.digits_ofDigits) and [digits lemmas](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/Digits/Lemmas.html#Nat.digits_two_eq_bits) corroborate the two general identities used. Those web pages are an API cross-check, not evidence of elaboration against the campaign’s pinned Mathlib.

I reran the attached script unchanged, using `python3 -I`, over exactly the 12 attached Lean files, first substituting the attached base for the target and then using the head. Both processes exited 0; their complete output matched the respective supplied log byte-for-byte. SHA-256 hashes of those reproduced outputs are `29f1327633833b02eb485755643e2ea9cae4ed2c31ff0e6ec8e133150ba8366f` (before) and `f29678b24383d11a23b68fc75e030e56f8650423295e9d6f7b37fbf39aa6f4e1` (after).

The script counts only bodies of at least 60 whitespace-stripped characters and detects same-kind directed pairs using greedy common blocks of at least 25 characters, covering at least half the source body. It does not establish semantic nonduplication, and the 376 pairs are not a count of 376 independently adjudicated debts. I inspected all 14 additions, including those below its cutoff. The owned file had no proved-copy material in the base, and I found none introduced in the fill (cumulative owned-file copied material: 0 of 235 lines). Existing pairs among unchanged population files are not reopened by this audit.

Notation glossary: `rank`, `str`, `T` abbreviate the three private `ntc` definitions; `c` is `TimeHierarchy.code.toMachineCode`; `s` and `x` are Boolean words; `n` and `t` are natural numbers; `M`, `E`, `R` are the assumed constructor, compiled emitter and assembled machine, and `c₀` is the constructor’s positive time multiplier. `++` is list concatenation; `[b]` is a singleton list; `bits` lists binary digits least-significant first; `bodd` is the parity Boolean; `headI` returns the first bit or false on an empty list; `⊕` is Boolean exclusive-or. Other names retain their attached Lean definitions.

PASS — 0 blockers / 0 majors / 2 minors / 7 notes.
