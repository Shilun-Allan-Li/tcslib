# Arora–Barak Chapter 6, pp. 108–111 — Formalization Plan

Target: book pages 108 through 111, stopping at the start of §6.2 "Uniformly
Generated Circuits". Source PDF:
`blueprint/src/references/Sanjeev_Arora,_Boaz_Barak-Computational_complexity__a_modern_approach-Cambridge_University_Press(2009).pdf`,
PDF pages 134–137 (book pages 108–111).

Output module: `TCSlib/Complexity/CircuitComplexity/`.
Existing foundation: `PPoly.lean` (Def 6.1 adaptation, Def 6.2 `Language.InSIZE`,
Def 6.5 `Language.InPPoly`), `Basic.lean`, `Formulas.lean`.

## Status legend

`TODO` → not started · `WIP` → formalizer has written it, critic not satisfied ·
`DONE` → critic passed and `lake build` is green · `SKIP` → deliberately not
formalized, reason recorded.

---

## Work units

### U0 — Def 6.2, Def 6.5 · DONE
`Language.InSIZE`, `Language.InPPoly`, `ACP.PPoly` in `PPoly.lean`. Audited
against AB in a previous session; correspondence table is in the module
docstring. Do not redo.

### U1 — `SIZE` API + Example 6.3 (all-ones language) · DONE
File: `CircuitComplexity/SizeClasses.lean`

- Monotonicity: `T ≤ T'` pointwise → `InSIZE T ⊆ InSIZE T'`.
- `InSIZE T → InPPoly` when `T` is polynomially bounded.
- Example 6.3, part 1: `{1ⁿ : n ∈ ℕ}` is decided by a linear-size family.
  Concretely: build the `FeedForward` family whose single non-input layer is one
  unbounded `AND` gate over all `n` inputs, prove it accepts exactly the
  all-ones words, and bound its size.

Example 6.3 part 2 (grade-school addition has linear-size circuits) is **SKIP**:
it needs a binary-encoding scheme for `⟨m, n, m+n⟩` that AB never pins down, and
the result is used nowhere later in the chapter. Record the skip, do not build a
half-specified encoding.

### U2 — Claim 6.8 (every unary language is in P/poly) · DONE
File: `CircuitComplexity/UnaryLanguages.lean`

For `L ⊆ {1ⁿ}`, the length-`n` circuit is the Example 6.3 AND-tree when `1ⁿ ∈ L`
and the constant-`0` circuit otherwise. Depends on U1.

This is the payoff unit of §6.1.1: it is what makes `P/poly` contain undecidable
languages, and it needs no Turing machine. Prioritize it over Theorem 6.6.

### U3 — Def 6.9 (CKT-SAT) + Lemma 6.11 (CKT-SAT ≤p 3SAT) · DONE
File: `CircuitComplexity/CircuitSat.lean`

- `CktSat`: circuits with a satisfying assignment.
- Lemma 6.11: the Tseitin-style map sending each gate `vᵢ` to a variable `zᵢ`
  with clauses forcing `zᵢ ↔ (z_j ∧ z_k)` etc., plus the unit clause on the
  output. Prove satisfiability is preserved in both directions.

Reuse, do not re-derive: `TCSlib/Complexity/NPReductions/SATTo3SAT.lean` already
has `Clause`, `Clause3`, `CNFFormula`, `Formula3` and an equisatisfiability
proof. Check what is reusable before writing a clause type.

Note that AB states Lemma 6.11 for its own fan-in-2 basis. Our circuits have
unbounded fan-in `AND`, so the gate-to-clause map must either handle width-`w`
gates or go through a fan-in-2 reduction. Decide this explicitly and write the
decision in the module docstring.

### U4 — UHALT, and P/poly ⊄ decidable · DONE
File: `CircuitComplexity/UHalt.lean`

`UHALT = {1ⁿ : n's binary expansion encodes ⟨M, x⟩ with M halting on x}`, and
the corollary that `P/poly` contains an undecidable language, via U2.

Mathlib has the computability side: `Mathlib.Computability.Halting`,
`ComputablePred`, `Nat.Partrec`. The corollary "some unary language is
undecidable" may be obtainable from a cardinality/diagonal argument already in
Mathlib without building AB's explicit `⟨M, x⟩` encoding — look first.

### U5 — Theorem 6.6 (P ⊆ P/poly) · SKIP for this loop
Requires: a Turing machine model, `P` as a complexity class, and Remark 1.7's
oblivious-TM simulation, none of which exist in this library. AB's proof is a
sketch that leans on Cook–Levin. This is a multi-week project, not a loop
iteration.

Deliverable instead: a docstring in `SizeClasses.lean` recording the statement,
what it depends on, and why it is deferred. Do **not** write `theorem P_subset_PPoly ... := sorry`.

### Lemma 6.10 (CKT-SAT is NP-hard) · SKIP
Depends on `NP` and on Theorem 6.6's machinery. Deferred with U5.

---

## Explicit skip list (do not formalize; recorded so the loop does not revisit)

| Item | Reason |
|---|---|
| Note 6.4, straight-line programs | An alternative presentation of circuits that AB never uses again — the only follow-up is Exercise 6.2. Formalizing it would add a second circuit model with no consumer. |
| Remark 6.7, logspace-computability of the circuit | A strengthening of Thm 6.6, and its natural home is §6.2's uniformity discussion, which is outside this range. |
| Silicon-chip motivation, footnote 1 | Prose. |
| "is n¹⁰⁰ practical" discussion | Prose. |
| Exercise 6.1's sharper `O(2ⁿ/n)` bound | A different and harder construction than Claim 2.13's; nothing in range needs it. (**Claim 2.13 itself is no longer skipped** — Theorem 6.22 needs it, so U9 proves it in `Universal.lean`.) |

---

## Wave 2 — the rest of Chapter 6 (pp. 113–122)

Surveyed in full. Most of §§6.3–6.6 and §6.8 is an `iff` with `P`, `NP`, `EXP` or
`PH` and is blocked; `ch6/NOT_FORMALIZED.md` lists every blocked item. What
follows is what is genuinely machine-free.

### U9 — Claim 2.13: every Boolean function has a circuit · DONE
File: `CircuitComplexity/Universal.lean`

Every `f : (Fin n → Bool) → Bool` is computed by a circuit of size `O(n · 2ⁿ)`
(AB cites `n2ⁿ`; Exercise 6.1 sharpens to `O(2ⁿ/n)` — the weaker bound suffices).
AB cites this from Chapter 2 rather than proving it here, but Theorem 6.22 needs
it, so it must exist. Constructive: the DNF over satisfying assignments.
`Formulas.lean` already has `DNF` and `DNF.eval`.

Independent of U10 and U12.

### U10 — Theorem 6.21: existence of hard functions · DONE
File: `CircuitComplexity/HardFunctions.lean`

Some `f : (Fin n → Bool) → Bool` is computed by no circuit of size `S`. AB says
"for every `n > 1`"; U10 carries no hypothesis, because the statement is simply
vacuous where it has no content. **`exists_not_eval_of_lt` is vacuous below
`ℓ = 3`** — the side condition forces `S = 0` and `Circuit.size` is never `0` —
so U11 must pick `ℓ ≥ 3`. (AB's own `2ⁿ/(10n)` is below `1` until `n = 6`, so AB
is vacuous further out than we are.) A counting argument: there are `2^(2ⁿ)` functions, and at most `2^(L(S))`
circuits of size `≤ S`, where `L(S)` bounds the encoding length — so any `S` with
`L(S) < 2ⁿ` works.

**AB's constant does not survive, but not in the direction this plan predicted.**
The prediction here was that unary indices would make our `S` *smaller*. That was
wrong: unary costs `n` bits per leaf where AB's `9·S·log S` costs `≈ 9n` per gate,
so `2ⁿ/(n+5)` is numerically *larger* than `2ⁿ/(10n)` for every `n ≥ 1`.

What actually diverges is the **model**, and it diverges against us. AB's `|C|` is
the vertex count of a fan-in-2 **DAG** with one shared source per variable;
`Circuit.size` counts every node of an unbounded-fan-in **tree**, so every literal
occurrence costs a node and no gate can be reused. But it also charges **1** for a `k`-ary
gate where Def 6.1 charges `k - 1` vertices, which cuts the other way, so **the
two families are not comparable**: a size-`S` tree embeds in a DAG of size
`≤ S + 2n` and the reverse fails badly. AB's statement is strictly stronger at the
`S ≈ 2ⁿ/n` that matters, and a function hard for size-`S` trees need not be hard
for size-`S` DAGs — but at small `S` neither family contains the other.

Also corrected: `ACP.size_le_length_encodeSigma` is the **wrong direction** for
this unit — it bounds size by length. Counting circuits by strings needs length
bounded by size, which is U10's own `length_encodeCircuit_succ_le`.

Independent of U9 and U12.

### U11 — tree-model size hierarchy (**not** Theorem 6.22) · DONE
File: `CircuitComplexity/Hierarchy.lean`

AB's Theorem 6.22 is `SIZE(T) ⊊ SIZE(T')`, and **is not deliverable** — neither
transfer between `ACP.FeedForward` and `BoolCircuit.Circuit` exists, so U10's
hardness cannot reach `Language.InSIZE`'s model. What U11 delivers is the same
argument over an explicitly tree-model class, `Language.InTreeSize`. Nothing is
named `SIZE`; no theorem is named for 6.22. AB's proof: take `f` hard for
`ℓ`-bit inputs by Thm 6.21 (**constant `2^ℓ/(ℓ+5)`, not AB's `2^ℓ/(10ℓ)`**; the
parametric hook is `ACP.exists_not_eval_of_lt`), pad it to `n` bits by ignoring all but the first `ℓ`,
and bound the padded function both ways using Claim 2.13.  (AB's upper constant on p. 116 is `10 ℓ 2^ℓ`, **not** `2^ℓ · 10` — `pdftotext` drops the `ℓ` glyph there, and AB's own `SIZE(11 n^1.1 log n)` pins it down.) **U9's bound is
`2 ^ n * (n + 1) + 1`, not AB's `n2ⁿ`** — the hook is
`ACP.exists_circuit_eval_eq_size_le`. Builds on U9 and U10 only — `PPoly.lean`
is not imported, and `Language.InSIZE` is named in `Hierarchy.lean` solely to say
the class here is not it.

### U12 — NC, AC, and their inclusions · DONE
File: `CircuitComplexity/NCAC.lean`

- `Def 6.24` `NC^d` / `NC`, `Def 6.25` `AC^i` / `AC` — both are *circuit* classes
  with no uniformity condition, so both are machine-free. (AB's "one can also
  define uniform NC" needs logspace and is out of scope.)
- `NC^i ⊆ AC^i ⊆ NC^{i+1}` — the real content: unbounded fan-in `w` is simulated
  by a tree of fan-in-2 gates of depth `⌈log₂ w⌉`.
- `Example 6.26`, `PARITY ∈ NC¹`, by the balanced binary tree.

**`NC` needs fan-in 2, which this library does not have.** `AC` is natural for us
(our gates are already unbounded); `NC` is not. This is the bounded-fan-in
subclass question from the very start of this work. Decide and record: a new
fan-in-2 circuit type with a forgetful map to `Circuit`, or a `maxFanin ≤ 2`
predicate over the existing one. `Circuit.maxFanin` already exists in `Basic.lean`.

Independent of U9–U11.

## Standing conventions (apply to every unit)

- **Alphabet.** Languages are `Language Bool`; circuits are `Fin 2`;
  `finTwoEquiv` converts at the boundary and nowhere else. This matches
  `Turing.FinEncoding` and cslib's `MultiTapeTM k Bool State`, so that the
  sibling branch's `P` and our `P/poly` compose without transport.
- **`P` is not ours to define.** A sibling branch is vendoring cslib's
  multi-tape TM for the Turing-machine side. Do not define a machine model,
  `P`, or a time-bounded class here.
- **Namespaces: the namespace follows the circuit type.** `ACP` for
  `FeedForward`, `BoolCircuit` for `BoolCircuit.Circuit`, `Language` for
  language-level notions that name no circuit. The earlier form of this rule
  ("circuit machinery goes in `ACP`") predates the two-circuit-type split and was
  wrong: a lemma about `Circuit` cannot sit in `ACP` without leaving its own
  type's namespace, and `ACP.CircuitFamily` already occupies the name.
  Consequence, queued for the cross-track pass: `ACP.cktSatLang`
  (`Encoding.lean`) is misplaced — it is a language of `BoolCircuit.Circuit`s.

### U6 — cross-track consistency pass · DONE
No per-file critic can see these; they are the orchestrator's to run once every
unit lands.

- **Hoist `Language.unary`.** It lives in `UHalt.lean`, which *imports*
  `UnaryLanguages.lean`, so it must move up. U4's critic verified
  `Language.unary S` is literally the set `Language.exists_le_allOnes` builds
  inline at `UnaryLanguages.lean:48` — equal by `rfl`, not merely equivalent —
  so that lemma collapses to a one-liner afterwards.
- **U4 advisories.** `## Main results` omits `uhalt_inPPoly` and
  `not_computablePred_mem_uhalt`, the two facts the module title advertises;
  rename `exists_inPPoly_not_computablePred` to carry the `L ≤ allOnes` conjunct
  it actually states; drop the duplicate AB Claim 6.8 citation.
- **Relocate the three `Circuit.eval_*` lemmas** from `CircuitSat.lean` into
  `Basic.lean`, where they belong — they are general facts about
  `BoolCircuit.Circuit.eval` parked in U3's file only to respect file ownership.

### U7 — `policy.md` compliance · DONE
Added after the user introduced `policy.md`. The ch6 output met none of §2
(no `## References` section in any file, no `[AB09, location]` declaration tags)
and none of §3 (no proof sketches, against 8 proofs over ~20 tactic lines), and
met §1 only partially (copyright header in 1 of 9 files, repo-standard
`set_option`s in none, `import Mathlib.Tactic` in three, `finTwoEquiv_symm_eq_one_iff`
leaking into the root namespace).

`policy.md` outranks `ch6/REVIEW_CRITERIA.md`; the rubric has been amended to say
so (Blocking item 0), and References / source tags / proof sketches are exempt
from the comment-volume limits they would otherwise violate.

**U6 and U7 touch the same eight files, so one combined critic reviews both once
U7 lands** — reviewing U6 now would read files mid-edit.

Open U6 items for that critic: the `UHalt.lean` docstring trim (it cut prose the
U4 critic had endorsed, to satisfy a rule U6's own hoist pushed over the line);
whether `Lit.toCktLiteral` is the right name for the collision fix; and whether
`Language.unary_inPPoly` should follow `unary` into `UnaryLanguages.lean`.

### U8 — circuit encoding, and the clause-count half of Lemma 6.11 · DONE
File: `CircuitComplexity/Encoding.lean`

`ch6/NOT_FORMALIZED.md` is the standing ledger of what is deliberately left out;
read it before adding or removing scope.

Two AB gaps close together here, because they want the same object:

- **Def 6.9's encoding.** AB's CKT-SAT is a language of *encoded* circuits; ours
  is `Set ((n : ℕ) × Circuit n)`. An encoding makes `CktSat` a real
  `Language Bool`, as AB states it.
- **Lemma 6.11's clause-count half.** With an encoding there is an input length,
  so the number of 3-clauses out can be bounded polynomially in it. This needs a length
  lemma for `SATTo3SAT.to3SAT`, which that file does not currently provide.

AB specifies an encoding on p. 112 while motivating Def 6.14 — adjacency matrix
plus gate-label array, vertices `[S]`, first `n` inputs, last the output — but
that form needs vertex identities our tree-shaped `Circuit` does not have, so U8
serialises the tree structurally instead and records the divergence. §6.2 will
still need AB's form, or a DAG circuit type; see `ch6/NOT_FORMALIZED.md`.

**The time half stays blocked.** `≤p` needs a machine model; this unit delivers a
polynomial *clause-count* bound and must not claim more. `policy.md` §2 requires the
divergence be recorded, and every previous unit that overclaimed here was
rejected for it.

## Deferred follow-ups (not blocking any unit)

| Item | Why deferred |
|---|---|
| `andGateOp` (`SizeClasses.lean:56`) and `notGateOp` (`UnaryLanguages.lean:61`) duplicate the anonymous AND and NOT terms inlined in `AC_GateOps` at `ACpGates.lean:29-30` | Relocating them means editing 842 lines of proved Razborov–Smolensky code owned by another concern. `andGateOp_mem_AC_GateOps` and `notGateOp_mem_AC_GateOps` already tie each to its inlined twin (both close by `rfl`, so the terms are verified identical). |
| `Circuit.eval_lit`, `Circuit.eval_node_true_iff`, `Circuit.eval_node_false_iff` (`CircuitSat.lean:58,63,71`) are general facts about `Basic.lean`'s `Circuit.eval` | The U3 agent owns only `CircuitSat.lean`, so it could not put them in `Basic.lean`. Verified they duplicate nothing elsewhere in `TCSlib/`. Relocate in the cross-track pass. |
| **`FeedForwardCircuit.lean:92–95` describes a map that does not exist** | Its prose claims tree → DAG "the embedding **is faithful** … size at most `C.size * C.depth` after inserting identity wires to pad shorter branches". The code does none of that: `Circuit.toFeedForward` (declared `:250`) hides the whole circuit in one opaque layer-0 gate op `{ ι := Fin n, func := C.eval }` (`:258`) with `GateOp.id` wires above — no padding, no structural embedding, and `size = C.depth + 1` independent of `C.size`. Several units cite this map as the `CircuitFamily` ↔ `Circuit` bridge; U11's critic is the first to have read it. Under `BooleanAnalysis/`, so off-limits without the user's say-so. |
| No bridge from `PPoly.lean`'s `ACP.CircuitFamily` (`FeedForward (Fin 2)`) to `BoolCircuit.Circuit` | Both directions fail. `ACP.FeedForward.toCircuit` (`FeedForwardCircuit.lean:216`) is over `FeedForward Bool`, needs an `IsAndOrGate` hypothesis that is false for a general `AC_GateOps` circuit (which contains `id` and `NOT`, for which `Circuit` has no node), and its `(k+1)^depth` size bound is exponential. `Circuit.toFeedForward` is the row above. Until that gap is closed, U3's `CktSat` and U0/U1's `P/poly` are about two unconnected circuit models. |
| Cross-track consistency pass | Per-file critics cannot see duplicated helpers or naming drift between parallel tracks. Run once U1–U4 land. |

## Judgment rule for the formalizer

Formalize a statement when it is (a) given a number by AB as a Definition,
Theorem, Lemma or Claim, **and** (b) either used later in the chapter or a
standalone mathematical fact worth having. Skip Notes, Remarks, Examples that
only illustrate, and anything whose statement AB leaves under-specified. When
skipping, append a row to the table above with the reason.
