# What is deliberately not formalized — Arora–Barak Chapter 6

A standing ledger. Every entry says *why*, so the loop does not silently revisit
a decision or quietly acquire a gap. Sources: AB Chapter 6 in full, pp. 105–122 (PDF 131–148).

Status: `JUDGMENT` = decided not worth formalizing · `BLOCKED` = wants machinery
this library does not have · `PARTIAL` = some of it is formalized, and the entry
says which part is not.

---

## §6.1, pp. 108–111 — the completed range

| AB item | Status | Reason |
|---|---|---|
| **Note 6.4**, straight-line programs | JUDGMENT | An alternative presentation of circuits AB never reuses; the only follow-up is Exercise 6.2. Formalizing it adds a second circuit model with no consumer. |
| **Example 6.3 part 2**, grade-school addition | JUDGMENT | Needs an encoding of `⟨m, n, m+n⟩` that AB never pins down. Unused later. |
| **Remark 6.7**, the circuit is logspace-computable | BLOCKED | A strengthening of Thm 6.6; also needs logspace computability (AB Def 4.16), which neither TCSlib nor Mathlib has usably. |
| **Theorem 6.6**, `P ⊆ P/poly` | BLOCKED | Needs a TM model, the class `P`, and Remark 1.7's oblivious-TM simulation. Recorded as a deferral in `SizeClasses.lean`; **no `sorry` stub**. |
| **Lemma 6.10**, CKT-SAT is NP-hard | BLOCKED | Needs `NP` and Theorem 6.6's machinery. |
| **"CKT-SAT is clearly in NP"** (p. 111) | BLOCKED | Needs `NP`. |
| **The alternative Cook–Levin proof** | BLOCKED | The stated purpose of §6.1.2, and it requires Lemma 6.10. We have 6.11 but not the theorem the section exists to re-prove. |
| **Lemma 6.11**, the `≤p` half | PARTIAL | Equisatisfiability is formalized (`mem_cktSat_iff_is3Satisfiable`), and as of U8 so is a **clause-count** bound linear in the encoded input (`length_to3SAT_toCNF_le`). Still missing: the polynomial-**time** content, which needs the machine model; and the output formula's **bit length**, which has no bound because `CktVar n` is indexed by all of `Circuit n` and so is infinite. Fixing the latter means re-indexing Tseitin variables by position rather than by subcircuit — a change to `CircuitSat.lean`'s `CktVar`. |
| **Properness of `P ⊆ P/poly`** (p. 110) | PARTIAL | Both ingredients exist — Claim 6.8, and an undecidable unary language — but `P ⊊ P/poly` is unstatable without `P`. `Language.exists_le_allOnes_inPPoly_not_computablePred` is the statable half. |
| **Definition 6.9's encoding** | PARTIAL | U8 gives `ACP.cktSatLang : Language Bool`, defined directly from `ACP.decodeSigma`. (A `Computability.FinEncoding` bundle, `ACP.circuitEncoding`, also exists, but is not in `cktSatLang`'s definitional path and currently has no consumer — it is there as the interface a future §6.2 would want.) `CktSat` stays a set of circuits deliberately: the Tseitin proof must not depend on an encoding. Still **not** formalized: AB's *adjacency-matrix* form and its `SIZE`/`TYPE`/`EDGE` accessors, since our `Circuit` is a tree with no vertex identities and so nothing indexes an `S × S` matrix. |
| **UHALT's numbering** | PARTIAL, and settled | AB decodes `n`'s binary expansion to `⟨M, x⟩`; we decode via `Nat.unpair` through `Denumerable.ofNat Nat.Partrec.Code`. **Verified not to matter:** `UHALT` occurs exactly three times in the whole book (pp. 110, 111, 113) and in all three is used only as "a unary undecidable language" — Example 6.17 is the last, and uses precisely that. The binary-expansion encoding is never used for anything. |
| **Claim 2.13** (`n2ⁿ`) | PARTIAL, formalized by U9 | AB cites it from Chapter 2 without proof, but Theorem 6.22 needs it, so `Universal.lean` proves it — with **our** constant `2ⁿ(n+1)+1`, not AB's `n2ⁿ`. The gap is that `Circuit.size` measures a different object: an unbounded-fan-in tree, charging for every literal occurrence and reusing nothing, but charging `1` for a `k`-ary gate where AB Def 6.1 charges `k-1` vertices. **The full accounting — AB's symbol count, AB's vertex count, ours, and the excess against each — is in `Universal.lean`'s `## Divergences` block, which is checked against the book; do not restate it here. (The tree-side count is proved; AB's two counts are checked against AB, not theorems here.)** **Not formalized:** Exercise 6.1's sharper `O(2ⁿ/n)`, a different construction. |
| Exercise 6.1's sharper `O(2ⁿ/n)` | JUDGMENT | A genuinely different and harder construction than Claim 2.13's; not needed by anything in range. |
| Fan-in/fan-out remarks, silicon-chip motivation, footnote 1, the "is `n¹⁰⁰` practical" discussion, Figure 6.1 | JUDGMENT | Prose and illustration. The substantive fan-in content is recorded as divergences in `PPoly.lean` and `CircuitSat.lean`. |

## §6.2, pp. 111–112 — blocked in full

Every item requires a machine model, so none of it can be attempted here. `P` is
the sibling branch's (vendored cslib multi-tape TM); see `ch6/PLAN.md`, Standing
conventions.

| AB item | Needs |
|---|---|
| **Def 6.12**, P-uniform circuit families | "a polynomial-time TM that on input `1ⁿ` outputs the description of `Cₙ`" |
| **Theorem 6.13**, P-uniform ⟺ `P` | `P` |
| **Def 6.14**, logspace-uniform families | implicit logspace computability (AB Def 4.16) |
| **Theorem 6.15**, logspace-uniform poly-size ⟺ `P` | `P` |

**The one machine-free piece of §6.2 was its circuit encoding**, and U8 built one
— but *not* AB's. AB describes, on p. 112 while motivating Def 6.14, an `S × S`
adjacency matrix plus a gate-label array with `SIZE(n)`, `TYPE(n, i)` and
`EDGE(n, i, j)` accessors. That form is unavailable to us: `BoolCircuit.Circuit`
is a tree with no vertex identities. `CircuitComplexity.Encoding` instead
serialises the tree structurally. When §6.2 becomes reachable it will need either
a DAG circuit type or AB's accessors reconstructed — neither exists.

## §§6.3–6.8, pp. 113–122 — surveyed in full

**Blocked** — each is an `iff` or an implication with a class this library cannot
define, so none can be attempted until the machine model lands:

| AB item | Needs |
|---|---|
| **Def 6.16**, `DTIME(T)/a(n)`; **Example 6.17** | a TM taking advice |
| **Theorem 6.18**, `P/poly = ⋃_{c,d} DTIME(nᶜ)/n^d` | `DTIME` |
| **Theorem 6.19**, Karp–Lipton (`NP ⊆ P/poly → PH = Σ₂ᵖ`) | `NP`, `PH` |
| **Theorem 6.20**, Meyer (`EXP ⊆ P/poly → EXP = Σ₂ᵖ`) | `EXP`, `Σ₂ᵖ`, and an oblivious-TM simulation |
| **Theorem 6.27**, `NC` ⟺ efficient parallel algorithms | a parallel machine model, which AB itself only sketches |
| **Def 6.31**, DC-uniform families | "a polynomial-time algorithm that given `n, i` computes the `i`th bit" |
| **Theorem 6.32**, `PH` ⟺ DC-uniform constant-depth exponential-size circuits | `PH` **and** DC-uniformity. AB does not prove it — it is left as Exercise 6.17. |
| §6.7.2, P-completeness | `P`, and logspace reductions |
| **Example 6.23**, parallel addition / matrix algorithms | prose about algorithms, no statement |

| AB item | Status | Reason |
|---|---|---|
| **Theorem 6.22**, `SIZE(T) ⊊ SIZE(T')` over `Language.InSIZE` | BLOCKED | Both transfers between `ACP.FeedForward` and `BoolCircuit.Circuit` fail, so U10's hardness cannot reach `InSIZE`'s model. The tree-model analogue is `ACP.treeSize_ssubset` in `Hierarchy.lean`, over `Language.InTreeSize` — **not** `Language.InSIZE`, and no theorem there is named for 6.22. `Hierarchy.lean`'s `## Divergences` has the reasons; do not restate them here. |
| **`NC⁰ ⊊ AC⁰`** (p. 118) and **`PARITY ∉ AC⁰`** (Ex 6.26) | BLOCKED | Forward references to Chapter 14, outside this range; AB states and proves neither here. The library's one constant-depth lower bound, `MODq_notin_AC0p_quantitative` (`TCSlib/BooleanAnalysis/RazborovSmolensky.lean:1203`), is a different statement over a different circuit type and does not discharge either. |
| **Defs 6.24 / 6.25 over AB's circuits** | PARTIAL | `NCAC.lean` formalizes `NC^d`, `AC^d`, `NC`, `AC`, `NC^i ⊆ AC^i ⊆ NC^{i+1}`, and `Parity.lean` `PARITY ∈ NC¹`, over `BoolCircuit.Circuit`, which is a tree — so every class there is AB's with fan-out restricted to 1 (formulas), where Def 6.1 circuits are DAGs. **Not formalized:** AB's DAG classes, and hence any comparison between them and these. `NCAC.lean`'s `## Divergences` says which levels the restriction is and is not expected to preserve — naming `NC¹` and `AC⁰` as the two boundaries, which differ — and flags those expectations as informal. |

**Formalized in wave 2:** Claim 2.13 (U9, `Universal.lean`), Theorem 6.21
(U10, `HardFunctions.lean`), the tree-model hierarchy (U11, `Hierarchy.lean` —
*not* Theorem 6.22, see its row above), and Defs 6.24/6.25 with the inclusions
(U12, `NCAC.lean`) and `PARITY ∈ NC¹` (`Parity.lean`).

U10's divergence from AB turned out to be the opposite of what was predicted
here. Our `S = 2ⁿ/(n+5)` is numerically *larger* than AB's `2ⁿ/(10n)`, because a
unary index costs `n` bits per leaf where AB's `9·S·log S` costs `≈ 9n` per gate.
What diverges instead is the model, and **the two families are not comparable**.
`Circuit.size` charges for every literal occurrence and reuses no gate, which
raises our count; but it charges **1** for a `k`-ary gate where Def 6.1 charges
`k - 1` vertices, which lowers it. A size-`S` tree embeds in a DAG of size
`≤ S + 2n`, and the reverse fails badly — so AB's statement is strictly stronger
at the `S ≈ 2ⁿ/n` in play, while at small `S` neither family contains the other.
(At `n = 3, S = 4`: `AND₃` is a size-4 tree here, and needs `≥ 5` vertices under
Def 6.1, so AB's family is empty there and ours is not.)
