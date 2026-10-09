# P3.2 round-2 statement-gate audit

**Verdict: PASS — 0 blockers, 0 majors, 2 minors, 1 note.** The arbitrary-scheme blocker is resolved at the statement level. Both round-1 counterconstructions violate the new simulator clauses. The existence statement and the four dependent statements are mathematically true as stated. This does not certify their pending Lean proofs.

Packet: `ch3-p32-r2-bundle.md`. Declared revision: `9a92fa1aeb377d568972e42229979cf81562ba41`, branch `complexity/arora-barak-ch3-4`. Independently verified SHA-256:

```text
9de1defa7ecd5a188b355152349d3d88df3d475a61fa94887081fb2ad15a153f
```

Locations below are file-local lines in the extracted attachments; filenames are relative to `TCSlib/Complexity/` unless otherwise stated. No source files were modified.

## Findings

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| R2-1 | **minor** | `Diagonalization/EXPCOM.lean:119–134` · existence sketch | The received parser/canonizer construction already has polynomial phase bounds that only need assembling. | `TuringMachine/MathlibBridge.lean:19–28,1038–1063,1078–1096` explicitly delivers an arbitrary-time primitive-recursive compilation, marks the earlier polynomial-canonizer proposal as superseded, and says no polynomial bound was proved. `Universal.lean:2649–2652,2844–2861` still charges `canonizerTime`. Thus the attached implementation does not establish the claimed provenance of the polynomial bound. This is an attribution/fill-description defect, not a counterexample to the new existence statement; an independent polynomial construction is given below. | Replace the claim about received polynomial ledgers with an explicit obligation to construct an efficient parser/canonizer or an independent bounded-acceptance simulator for the concrete grammar. Reuse the decoder's correctness lemmas, not an unproved complexity guarantee for the generic compiled canonizer. Do not describe this solely as exporting an existing time analysis. |
| R2-2 | **minor** | `Diagonalization/Relativization.lean:151–152` · enumeration sketch | The remaining arithmetic concerns a “triple pairing.” | Lines 132–140 correctly use four coordinates, including repetition. The closing sentence retains the old coordinate count. The theorem and the substantive repair are correct. | Change this to “four-coordinate pairing” or simply “pairing.” |
| R2-3 | **note** | `Diagonalization/EXPCOM.lean:135–149,161–164` · existence, `expCode`, `EXPCOM` | Choosing the scheme supplies the new simulator guarantees. | Correct as an interface dependency: the choice has type `UniformMachineCode`, so its projections include both guarantees. However, its inhabitance currently comes from `sorry`; `EXPCOM` therefore depends on that admission even as a definition. The pack declares this accurately. | No statement change required. At the fill gate, verify the axiom closure of the existence theorem, `expCode`, `EXPCOM`, and the completed consumers. |

## Round-1 dispositions

| Round-1 item | Round-2 disposition |
|---|---|
| 1. Arbitrary effective coding scheme | **Resolved.** The chosen type now contains the uniform semantic guarantee actually needed. The argument applies to every inhabitant of that type; it does not depend on identifying an opaque choice with a preferred witness. |
| 2. One-state default and missing recurrence coordinate | **Resolved substantively.** The three-state default is possible; alternatively, the embedding of a one-state plain machine has four states and is well-formed. The repetition coordinate makes representative indices unbounded. R2-2 is only residual wording. |
| 3. Wrong unary-tail injectivity citation | **Resolved at every changed citation site.** Two uses of `pairEncode_injective`, followed by list lengths, recover the three components. |
| 4. Fixed-oracle versus all-oracle clocks | **Retained, benign here.** No changed argument transfers a halting promise to a different oracle. |
| 5. Missing universal-machine implementation / build evidence | **Partly discharged as requested.** The three requested modules are present and their relevant contracts were inspected. Fresh build artifacts and the full dependency closure remain outside this packet audit. |

## Restatements of the new and changed definitions

**`UniformMachineCode` (99–114).** It inherits total decoding to one-work-tape binary machines, an encoding that survives arbitrary trailing `true` padding, and a finite machine computing the decoded machine's fixed serialization within some length-dependent time. In addition, it supplies one finite binary simulator and one natural number `simDegree`, both selected before the code, input, and deadline. For every such triple, the simulator halts with exactly `[true]` if the decoded machine has halted with exactly `[true]` by the deadline, and with exactly `[false]` otherwise, within

\[
d\bigl(|\alpha|+|x|+t+1\bigr)^d,
\qquad d=\texttt{simDegree}.
\]

Its input is `pairEncode (pairEncode (Nat.bits t) α) x`. The two implications are exhaustive by excluded middle, and output uniqueness prevents an incorrect opposite answer. In particular, the negative clause includes timeout, silent halting, and halting with any output other than the singleton `[true]`.

There is no promise on malformed outer simulator inputs or noncanonical clock encodings. No consumer needs one: the dispatcher constructs the specified input. The time is polynomial in the **numerical deadline**, not in its bit length. The interface does not require an efficient `encode` or inherited `canonizer`, nor does it itself bound the decoded table's size.

**`expCode` (148–149).** A fixed, noncomputably selected inhabitant of the preceding structure, whose existence is currently admitted. This fixes a single simulator and degree for all oracle queries.

**`EXPCOM` (161–164).** A word belongs exactly when it is `pairEncode α (pairEncode x (replicate n true))` and `expCode.decode α` halts on `x` with output exactly `[true]` within `2^n` source transitions. The deadline is inclusive; `n=0` means one transition. Empty code, input, and unary padding are permitted when the separators are present. Malformed triples are excluded; malformed machine codes retain whatever total decoding the selected scheme specifies.

The interface is stronger than the consumers strictly need: arbitrary deadlines and polynomial numerical-time simulation suffice, whereas powers-of-two deadlines with a suitable uniform exponential bound would already support this cluster. That extra strength is realizable and harmless. The lower inclusion only needs the inherited encoding law; no consumer incorrectly infers fast canonization from the new fields.

## Both counterconstructions fail the new clauses

Use the round-1 notation: `c_H` decodes `true :: s` as the one-step constant-accepting machine when `s ∈ H`, and as the one-step constant-rejecting machine otherwise. Consequently,

\[
(\operatorname{decode}_{c_H}(\mathtt{true}::s)).
 \operatorname{ComputesInTime}(\varepsilon,[\mathtt{true}],1)
\iff s\in H.
\]

If this scheme extended to `UniformMachineCode`, feed its simulator

\[
\operatorname{pairEncode}
 \bigl(\operatorname{pairEncode}(\operatorname{bits}(1),\mathtt{true}::s),
       \varepsilon\bigr).
\]

This word has length `2|s|+12` and is constructible in linear time. Both simulator clauses apply at the common bound

\[
d\bigl((|s|+1)+0+1+1\bigr)^d=d(|s|+3)^d.
\]

Thus the simulator would decide `H` in polynomial time.

1. **First counterconstruction.** Round 1 chose a decidable `H ∉ EXP`. The conclusion `H ∈ P ⊆ EXP` is a contradiction. The scheme remains effective but cannot meet the new simulator specification.

2. **Second counterconstruction.** Round 1 used `E₀ = EXPCOM[c₀]`, the tagged join `A = 0E₀ ∪ 1H`, and a decidable stage construction ensuring `U_H ∉ P^A`, where `U_H` asks whether `H` contains a word of the input's unary length. This `H` is also outside EXP, even when the base scheme is merely effective. Indeed,

   \[
   H\in\mathrm{EXP}
   \Longrightarrow U_H\in\mathrm{EXP}
   \subseteq\mathrm P^{E_0}
   \subseteq\mathrm P^A,
   \]

   contradicting the stage construction. The first implication enumerates the `2^n` candidate words: a bound `a·2^(n^k)` for testing each candidate gives at most `a·2^(n+n^k)` testing time. The next inclusion is the fixed-code padding reduction, which does not require uniform decoding; the last inclusion prefixes oracle queries with `0`. Hence this second scheme cannot possess the new simulator either. This reasoning does not assume the repaired P-versus-NP identity that it is checking.

## Existence and the dependent time bounds

### The existence statement is true, but needs the corrected construction obligation

Use `encode := CodeTM.serialize` and `decode := codeDecode`, with `codeDecode_serialize_pad` for the encoding law. The following gives a polynomial algorithm for the two simulator clauses, independently of the arbitrary-time compiler in `MathlibBridge`.

1. Parse the nested simulator input, preserving the binary deadline. In the machine code, read the binary state count and perform the minimum-length check **before** iterating over states. The actual guard is `81 * (numStates + 1) ≤ rest.length` (`CodeParser.lean:134–145`). Binary comparison/multiplication here is polynomial in the input length; a huge declared count must not first be expanded into a unary loop.
2. If the guard passes, there are at most linearly many states and records to check. Scan all fields, range-check the unary state indices, and check that the remaining suffix is all `true`. Success identifies a serialization prefix of the supplied code; failure selects the fixed silent fallback. In particular,

   \[
   |(\operatorname{codeDecode}\alpha).\operatorname{serialize}|
   \le \max\{|\alpha|,84\}.
   \]

   The constant `84` is the fallback's serialization length: `2` header bits, `1` initial-state bit, and `9·9` record bits. This bound follows from the concrete grammar, not from the abstract new interface.
3. Simulate at most `t` source transitions with a binary countdown. Keep the finite transition table, simulated input/work heads, visited work-tape interval, and a three-way output status: empty, exactly `[true]`, or permanently different. An output only grows, so the third status cannot return to the second. Check haltedness after the `t`-th transition before declaring timeout; emit one Boolean answer only after deciding the predicate.
4. With `S = |α|+|x|+t+1`, the input encoding has length at most `6S`, the table has length `O(S)`, and the simulated work interval has at most `2t+1` cells. Bounded scans of these regions, table lookups, counter operations, and at most `t` repetitions give a fixed polynomial running time `C S^e` for a finite multitape machine. A fixed finite tape alphabet can be encoded in binary with polynomial overhead. Choose an integer `d ≥ max{1,C,e}`; since `S ≥ 1`,

   \[
   C S^e\le dS^e\le dS^d.
   \]

The same efficient parser can emit the serialization prefix, or the fixed fallback serialization, and therefore supply the inherited effective-canonizer field as well. This constructs compatible fields for a concrete scheme, without treating `Classical.choice exists_effectiveMachineCode` as if it came with a decoder-identification theorem.

This is a mathematical machine-construction argument for the statement's truth. The finite-control implementation, simulation invariant, and polynomial ledger still need Lean proofs. The attached generic compiler provides no substitute for that time analysis; that is precisely R2-1.

### `EXP_subset_POracle_EXPCOM` survives unchanged in strength

Fix an EXP decider, convert it to the one-work-tape binary normal form, and relabel it to `N`. Its new code `α_L := expCode.encode N` is a fixed finite string, regardless of the computability or efficiency of `encode` as a function of machines. The inherited decoding law gives `expCode.decode α_L = N`.

After increasing the input exponent to at least one if necessary, a sufficiently large constant `C` makes the polynomial exponent `Q(n)=C(n+1)^c` dominate the normal-form running time through `2^Q(n)`, including empty inputs and constant factors. The map

\[
x\longmapsto\operatorname{pairEncode}
 \bigl(\alpha_L,\operatorname{pairEncode}(x,1^{Q(|x|)})\bigr)
\]

is polynomial time. Two pairing injections and equality of unary lengths recover its unique components; source-output uniqueness gives the reverse membership implication. One oracle query then decides the language. No relation between `expCode` and `TimeHierarchy.code` is needed.

### `NPOracle_EXPCOM_subset_EXP` now has a uniform ledger

Fix its oracle NDTM and a polynomial bound `p(n)=c(n^k+1)`. We may enlarge this bound so that `c,k ≥ 1`; monotonicity preserves the decision promise. In particular, `p(n) ≥ n+1`, so copying or scanning the original input is included below. Write `p=p(n)` only in this calculation.

Along a length-`p` choice word, a query at simulated step `s<p` has length at most `s`. For a valid query the exact pairing length gives

\[
2|\alpha'|+2|x'|+n'+4=|z|\le p,
\]

so all three component lengths are at most `p`. Its simulator input uses `bits(2^{n'})`, which has **`n'+1` bits**; constructing the clock does not require writing `2^{n'}` symbols. The new clauses bound its running time by

\[
\begin{aligned}
d(|\alpha'|+|x'|+2^{n'}+1)^d
&\le d(3p+2^p+1)^d\\
&\le d(5\cdot2^p)^d
=d5^d2^{dp}.
\end{aligned}
\]

Here `p ≤ 2^p` and `1 ≤ 2^p` justify the second inequality. The coefficient and exponent are fixed independently of the branch and query.

To include the host rather than merely counting simulator transitions, isolate its tapes, copy exactly the query prefix up to the first blank, capture the simulator's answer, clear its visited scratch, restore the suspended configuration, and resume. A conservative quadratic overhead in the call's runtime plus `p+1` suffices for these operations using explicit tape simulation and bounded clearing. With at most `p` calls per branch and `2^p` branches, a permissible total bound is

\[
\begin{aligned}
T(n)
&\le C_0\,2^p(p+1)
       \bigl(p+1+d5^d2^{dp}\bigr)^2\\
&\le C_0(1+d5^d)^2\,2^{(2d+2)p}
 = C_1\,2^{(2d+2)c(n^k+1)}.
\end{aligned}
\]

The second inequality uses `d ≥ 1` and `p+1 ≤ 2^p ≤ 2^{dp}`. These bounds include input/choice-word setup, malformed-query rejection, input repositioning, and scratch cleanup. They are construction bounds, not asserted exports of the unfinished dispatcher.

For `n ≥ max{2,(2d+2)c}`, the term `(2d+2)c n^k` is at most `n^(k+1)`. Absorb the remaining constant exponential factor and the finitely many smaller input lengths into the multiplicative constant allowed by `DTIME`. This gives membership in `DTIME (fun n => 2^(n^(k+1)))`, hence EXP. The sketch's exponential conclusion is therefore payable; it is not an attempt to absorb a variable-code constant.

For correctness, induction over simulated transitions uses the exact membership answer from the two clauses at each query. Only the selected oracle is simulated. Enumerating all length-`p` choice words includes every accepting computation; absorbing halting pads earlier terminations, and the all-branch halting promise makes every final branch verdict defined. Acceptance tests exact output `[true]`, without assuming rejected branches emit `[false]`.

### Statement verdicts

| Declaration | Verdict and justification |
|---|---|
| `exists_uniformMachineCode` | **True as stated.** The concrete grammar supports the polynomial construction above. Repair the provenance claim in its sketch. |
| `EXP_subset_POracle_EXPCOM` | **True as stated.** Fixed-code padding and the inherited decoding law suffice. |
| `NPOracle_EXPCOM_subset_EXP` | **True as stated.** The new simulator supplies the uniform query bound; enumeration and host overhead remain singly exponential. |
| `POracle_EXPCOM_eq_EXP` | **True as stated.** Combine the lower inclusion with `POracle_subset_NPOracle` and the upper inclusion. |
| `NPOracle_EXPCOM_eq_EXP` | **True as stated.** Combine the upper inclusion with the lower inclusion followed by `POracle_subset_NPOracle`. |
| `POracle_EXPCOM_eq_NPOracle_EXPCOM` | **True as stated.** Both sides equal EXP. |
| `exists_finOracleTM_enumeration` | **True as stated.** Finite state relabelling preserves every transition and oracle answer with no time change; four-coordinate enumeration supplies unbounded repetitions. |

For the last row, fix the tape count, state count, and table rank of a representative. Distinct fourth-coordinate values give distinct natural indices. Among `i₀+1` such indices, at least one is at least `i₀`, proving the exact recurrence quantifier. A direct default uses three distinct query/yes/no states, starts in the yes state, and halts on its first ordinary transition; it is well-formed under every oracle.

The uniqueness repair is also exact: equality of the outer pairs first fixes the codes, equality of the inner pairs fixes the inputs and replicated tails, and applying `List.length` to the latter equality fixes the padding exponent. No unary-first lemma is needed.

## Adversarial checks

| Instance | Result |
|---|---|
| Both tagged round-1 schemes, empty simulated input, deadline `1` | Their hypothetical simulator decides the hard embedded language in polynomial time. Both are excluded. |
| `simDegree = 0` | Impossible: at source deadline `0`, `simulator_rejects` would require `[false]` from an initialized simulator in zero steps. Initial configurations are live. Thus positivity follows from the clauses; no extra field is required. |
| Source deadline `0`, including empty code/input | Every initialized source is live; the negative clause applies. The `+1` leaves a positive base in the budget. |
| Source halts exactly on transition `t` | Accepted precisely when the completed output is `[true]`; checking timeout before this haltedness test would be an incorrect fill. |
| Source emits `true` but remains live at the deadline; or halts with `[]`, `[false]`, or `[true,false]` | All require the simulator's `[false]` answer. The new negative clause covers more than timeout. |
| Short code with a huge binary state count | The concrete decoder checks minimum table length before state iteration. A polynomial implementation uses binary arithmetic for that guard. |
| Empty outer query, malformed inner pair, or non-unary tail | Reject during triple parsing. The simulator is invoked only on a constructed, specified input. |
| Empty unary padding | The EXPCOM deadline is `2^0=1`; it is not a zero-step query. |
| Query tape with garbage after its first blank, or at negative cells | Copy only the extracted query prefix. Extra tape contents do not enter the membership test. |
| Very long fixed encoding of the language's normal-form machine | Harmless for the lower inclusion: its length enters a fixed reduction constant, not the input-dependent exponent. |
| Constant polynomial-time witness or empty original input | Enlarge to `c,k ≥ 1`; absorb finitely many small input lengths in the DTIME constant. No division by the input length is used. |
| Rank overflow, too few states, or arbitrarily large repetition coordinate | Default is well-formed, and valid representatives recur above every requested index. |

## Dependencies, source fidelity, and evidence limits

The EXPCOM shape and the three class identities match [AB09, Example 3.6(3), p. 74](https://theswissbay.ch/pdf/Gentoomen%20Library/Theory%20Of%20Computation/Sanjeev_Arora%2C_Boaz_Barak-Computational_complexity__a_modern_approach-Cambridge_University_Press%282009%29.pdf); the repair makes the implicit efficient-coding requirement explicit. The source comparison used the retrieved indexed published-text passage, not a downloaded complete book. [BGS75, pp. 432–436](https://cse.ucdenver.edu/~cscialtman/complexity/Relativizations%20of%20the%20P=NP%20Question%20(Original).pdf) confirms the all-oracle clock convention and the equality/separation targets. Its scanned original was accessible. The clock deviation remains declared and does not obstruct these repairs.

The attached dependency surface shows no accidental migration of the hierarchy or non-time-constructibility construction to `expCode`. `TimeHierarchy.code` still chooses an `EffectiveMachineCode`; `NotTimeConstructible.lean` still uses that scheme. Oracle agreement and the three separation-side declarations do not use the new scheme. The equality half of `baker_gill_solovay` uses the repaired EXPCOM identity as intended. Importing its module does not by itself change the meanings of the separation-side statements.

Independent packet checks:

- Extracted postimage Git blob hashes are `c416c5e4991c7c01580acd1c55d4188df6b5e482` for `EXPCOM.lean` and `3e12c6cf3dfcc2a7a70606f5625afe5a2019d782` for `Relativization.lean`, matching the supplied diff. The complete repair diff passes `git apply --reverse --check` against the attachments.
- The five phase files contain exactly 18 executable `sorry` tokens: `7 + 6 + 4 + 1 + 0`; no `axiom` declarations were found there. The EXPCOM file has the advertised one structure, two definitions, and six theorem stubs.
- The supplied sweep records the declared full revision, exactly 18 sorry warnings, no `error:` lines, and the facade entry. The supplied Diagonalization lint subsection reports 0 FAIL / 0 WARN over four files. Other directories have warnings; the pack did not claim otherwise.

Coverage is the changed definitions, the new existence statement, both inclusions, the three identities, the enumeration repair, both old counterconstructions, and the relevant attached dependency contracts. The eleven other unchanged P3.2 theorem stubs retain their round-1 dispositions and were not independently re-audited in full. Tactic proofs, the entire private interpreter/compiler implementation, unprovided imports such as `UniversalBlock.lean`, fresh `.olean` generation, repository-wide export status, and kernel axiom inventories were not verified. No Lean elaboration was run. This is a statement-gate pass, with the two minor corrections above still recommended.

## Notation glossary

- `d`: the selected scheme's `simDegree`; necessarily positive.
- `α, x, t`: a machine code, simulated input, and numerical deadline; primes denote query components. `ε` is the empty word and `|·|` is word length.
- `S`: `|α|+|x|+t+1` in the existence argument. `C,e` there are fixed polynomial coefficient and exponent.
- `H,c₀,c_H,E₀,A,U_H`: the auxiliary language, base scheme, tagged scheme, base EXPCOM language, tagged oracle join, and unary witness language from the round-1 constructions. `M₊,M₋` are their constant one-step accepting/rejecting machines; `s` is a tagged code's suffix there. `a,k` in the candidate-enumeration calculation are fixed time-bound parameters.
- `N,α_L,Q,L`: the normal-form decider, its fixed code, padding exponent, and language in the lower inclusion. `c,C` in that paragraph are fixed exponent/padding constants.
- `n,p(n),c,k`: original input length and polynomial oracle-time bound `c(n^k+1)`; `p` abbreviates `p(n)` only within the upper-bound calculation. `n'` is a query's unary padding length, `z` is that query, and `s` in that calculation is the elapsed simulated step count.
- `T(n),C₀,C₁`: the constructed deterministic simulation's running-time bound and fixed constants independent of the input, branch, and query.
- `i₀`: the requested lower bound on an enumeration index. `1^r` denotes a word of `r` true bits, and tagged joins `0E₀,1H` prepend the indicated bit.
