# 12.2c tranche T1 — Item 7 (CH7-D1): one countdown block loop (`ClassNP/PolyTimeBlock{Loop,Tests,Majority}.lean`)

## Repository and branch — read this before anything else

- Clone `https://github.com/Shilun-Allan-Li/tcslib`; check out **`complexity/arora-barak-ch3-4`**,
  NOT `main`. Confirm `git merge-base --is-ancestor 1a0013d9750a6d760b6fd46b3c267fe18f08f4fa HEAD`; if it fails, **stop**.
- Branch off fresh (`refactor/12.2c-t1-blockloop`); record the base hash; never rebase.
- **Delivery by zip** (`12.2c-t1-blockloop.zip`): `REPORT.md`, the three full sources, a
  `git format-patch` series, a bundle, the sweep and axiom logs, the four screen outputs, and
  `SHA256SUMS`. Integration (no action for you): T1 (plan §4e), a side branch, a PR for the
  user, then a **separate audit gate**. The files are Aparna's (ch7); she agreed to this PR.

## What this is

A refactor, with no new mathematics and every public statement frozen. Read plan §4d item 7 and
§4e, `backlog.md` CH7-D1, the ledger's CH7-D1 row, `audits/ch7-fill-r2-findings.md` R2-2, and
`policy.md`.

- **The debt.** The OR, XOR-then-OR and majority loops re-prove one guard, countdown, length,
  orbit and emission lemma set. R2-2 puts Tests at **≥ 12/25**, Majority at **≥ 8/14** and Loop
  at ≥ 1/32. The auditor: it "can be shared while retaining separate OR/XOR/vote computations."
- **The design (binding).** The shared reasoning goes in `namespace Complexity.BlockLoop` in
  Loop (Task 1), plus an OR-flag engine in Tests (Task 2). Each loop keeps only its own
  content: the XOR test and mask, or the vote counters. The OR test becomes the XOR test with
  an all-`false` mask. Thin wrappers are deleted.

**Pre-ship check (maintainer, executed):** `audits/evidence/ch34-t1/Item7PreShip.lean.txt`
(with its `.out`) runs the three refactored files verbatim (Loop L22–748, Tests L749–928,
Majority L929–1136) inside `namespace Complexity.Item7Probe`, beside the imported originals:
**0 errors, 0 warnings, 0 sorries**. It contains 26 `rfl` checks `@Item7Probe.X = @Complexity.X`,
2 checks of the redefined privates against their base bodies, and 72 axiom prints (26 base, 46
new), all within the triple, with the 26 pairs identical. `Item7PreShip-HomeContext.lean.txt`
runs the same bodies with only Loop's eight imports: 0/0/0.

**The probe is the reference implementation.** Land it with `Item7Probe` mapped to `Complexity`.
The full target files, headers and module docstrings included, are
`audits/evidence/ch34-t1/Item7Ref-PolyTimeBlock{Loop,Tests,Majority}.lean.txt`. Shorten a proof
only if every check below still passes, and report each.

## Owned files (modify these and nothing else)

| File | Issue commit (lines, public / private) | Reference after |
|---|---|---|
| `ClassNP/PolyTimeBlockLoop.lean` | 500, 22 / 10 | 789, 39 / 11 |
| `ClassNP/PolyTimeBlockTests.lean` | 653, 3 / 22 | 228, 6 / 2 |
| `ClassNP/PolyTimeBlockMajority.lean` | 469, 1 / 13 | 243, 1 / 5 |

None has changed since `5ad155ee`. Net: −362 lines, −27 privates, +20 publics, all in
`Complexity.BlockLoop`, a namespace used nowhere else (repo and dependencies grepped).

## Task 1 — the generic layer (`PolyTimeBlockLoop.lean`)

After `polyTimeComputable_emitIter`, before `/-! ### Truncating bitwise XOR -/`, insert the
section `/-! ### The countdown block loop … -/` with `namespace BlockLoop`. It holds the 17
publics below, verbatim, and two private guards between `emit` and `polyTimeComputable_step`:
`polyTimeComputable_headNil : PolyTimeComputable (fun s => [isNilB (pairFstD s)])` and
`polyTimeComputable_countdownNil`, the same at `pairFstD (pairSndD s)`
(`:= polyTimeComputable_headNil.comp polyTimeComputable_pairSndD`). Each `…` is at these
probe lines:
`polyTimeComputable_step` 327–340, `polyTimeComputable_emit` 343–348, 
`polyTimeComputable_countdownInit` 352–357, `step_done` 360–364, `length_step_le` 371–417, 
`length_iterate_le_of_slack` 423–442, `sliceTakeAt_pairEncode_drop` 446–449, 
`sliceDropAt_pairEncode_drop` 453–458, `orbit` 464–482, `iterate_done` 486–501, 
`lt_polyBudget_of_le` 504–507, `flatMap_emit_orbit` 513–529, `loop_output` 535–547, 
`polyTimeComputable_of_loop` 553–565, `polyTimeComputable_countdown` 571–588.
```lean
/-- One round of a countdown block loop: on `pairEncode h (pairEncode cd r)` with `h` and
`cd` nonempty it returns `pairEncode (upd h r) (pairEncode (cd.drop 1) (nxt h r))`; a state
whose head (done or malformed) or countdown is empty goes to the absorbing `blockDone`. -/
def step (upd nxt : List Bool → List Bool → List Bool) (s : List Bool) : List Bool :=
  if isNilB (pairFstD s) then blockDone
  else if isNilB (pairFstD (pairSndD s)) then blockDone
  else
    pairEncode (upd (pairFstD s) (pairSndD (pairSndD s)))
      (pairEncode ((pairFstD (pairSndD s)).drop 1) (nxt (pairFstD s) (pairSndD (pairSndD s))))
/-- The chunk function of a countdown block loop: `out s` exactly when the head of `s` is
nonempty and its countdown is empty, and `[]` otherwise. -/
def emit (out : List Bool → List Bool) (s : List Bool) : List Bool :=
  if isNilB (pairFstD s) then []
  else if isNilB (pairFstD (pairSndD s)) then out s
  else []
/-- A countdown block loop's round `g = step upd nxt` is polynomial-time whenever its head
and remainder updates, read off the state, are (one `ite` on the disjoint guards). -/
theorem polyTimeComputable_step {g : List Bool → List Bool}
    {upd nxt : List Bool → List Bool → List Bool} (hg : g = step upd nxt)
    (hu : PolyTimeComputable (fun s => upd (pairFstD s) (pairSndD (pairSndD s))))
    (hn : PolyTimeComputable (fun s => nxt (pairFstD s) (pairSndD (pairSndD s)))) :
    PolyTimeComputable g := …
/-- The chunk function `emit out` is polynomial-time whenever `out` is. -/
theorem polyTimeComputable_emit {out : List Bool → List Bool}
    (ho : PolyTimeComputable out) : PolyTimeComputable (emit out) := …
/-- The initial state `pairEncode h₀ (pairEncode cd (r z))`, with unary countdown `cd` of
length `a'·(|x z|+1)^k'`, is polynomial-time whenever `x` and `r` are. -/
theorem polyTimeComputable_countdownInit (h₀ : List Bool) {x r : List Bool → List Bool}
    (hx : PolyTimeComputable x) (hr : PolyTimeComputable r) (a' k' : ℕ) :
    PolyTimeComputable (fun z => pairEncode h₀
      (pairEncode (List.replicate (a' * ((x z).length + 1) ^ k') true) (r z))) := …
/-- `blockDone` is absorbing for every countdown block loop. -/
theorem step_done {g : List Bool → List Bool}
    {upd nxt : List Bool → List Bool → List Bool} (hg : g = step upd nxt) :
    g blockDone = blockDone := …
/-- One round of a countdown block loop respects the slack measure `|s| + c·|cd s|`
(`cd s = pairFstD (pairSndD s)`), up to `max _ 2`, provided every live update satisfies
`2·|upd h r| + |nxt h r| ≤ 2·|h| + |r| + 2 + c`.
**Proof sketch.** The done branches give `blockDone`; a live round on `⟨h, ⟨cd, r⟩⟩` drops
one countdown symbol, two symbols of encoding and `c` of slack, paying for the growth. -/
theorem length_step_le {g : List Bool → List Bool}
    {upd nxt : List Bool → List Bool → List Bool} (hg : g = step upd nxt) (c : ℕ)
    (hlive : ∀ h r, h ≠ [] →
      2 * (upd h r).length + (nxt h r).length ≤ 2 * h.length + r.length + 2 + c)
    (s : List Bool) :
    (g s).length + c * (pairFstD (pairSndD (g s))).length ≤
      max (s.length + c * (pairFstD (pairSndD s)).length) 2 := …
/-- An orbit envelope from a slack step bound: if every step of `g` respects
`|s| + c·|cd s| ≤ max (·) 2`, then every iterate of `g` from `w` has length at most
`b·(|w|+1)^1` whenever `2 ≤ b` and `c + 1 ≤ b`, the shape
`Complexity.polyTimeComputable_emitIter` consumes (induction, then `|cd w| ≤ |w|`). -/
theorem length_iterate_le_of_slack {g : List Bool → List Bool} (c b : ℕ)
    (hb : 2 ≤ b) (hcb : c + 1 ≤ b)
    (hg : ∀ s, (g s).length + c * (pairFstD (pairSndD (g s))).length ≤
      max (s.length + c * (pairFstD (pairSndD s)).length) 2)
    (w : List Bool) (i : ℕ) :
    (g^[i] w).length ≤ b * (w.length + 1) ^ 1 := …
/-- Reading the `i`-th block: on `pairEncode x (u.drop (i·B))`, with `B = a·(|x|+1)^k`,
`sliceTakeAt a k` keeps `x` and the next `B` symbols. -/
theorem sliceTakeAt_pairEncode_drop (a k : ℕ) (x u : List Bool) (i : ℕ) :
    sliceTakeAt a k (pairEncode x (u.drop (i * (a * (x.length + 1) ^ k)))) =
      pairEncode x ((u.drop (i * (a * (x.length + 1) ^ k))).take (a * (x.length + 1) ^ k)) := …
/-- Advancing one block: on `pairEncode x (u.drop (i·B))`, with `B = a·(|x|+1)^k`,
`sliceDropAt a k` returns `pairEncode x (u.drop ((i+1)·B))`. -/
theorem sliceDropAt_pairEncode_drop (a k : ℕ) (x u : List Bool) (i : ℕ) :
    sliceDropAt a k (pairEncode x (u.drop (i * (a * (x.length + 1) ^ k)))) =
      pairEncode x (u.drop ((i + 1) * (a * (x.length + 1) ^ k))) := …
/-- Closed form of a countdown block loop's orbit up to countdown exhaustion: from
`⟨P 0, ⟨1^K, Q 0⟩⟩`, after `i ≤ K` rounds the state is `⟨P i, ⟨1^(K-i), Q i⟩⟩`, given
nonempty heads and the one-round recurrences of the head and the remainder (induction
on `i`: both guards fail and the countdown loses one symbol). -/
theorem orbit {g : List Bool → List Bool}
    {upd nxt : List Bool → List Bool → List Bool} (hg : g = step upd nxt)
    (P Q : ℕ → List Bool) {K : ℕ} {s₀ : List Bool}
    (h₀ : s₀ = pairEncode (P 0) (pairEncode (List.replicate K true) (Q 0)))
    (hP : ∀ i ≤ K, P i ≠ [])
    (hupd : ∀ i < K, upd (P i) (Q i) = P (i + 1))
    (hnxt : ∀ i < K, nxt (P i) (Q i) = Q (i + 1))
    {i : ℕ} (hi : i ≤ K) :
    g^[i] s₀ = pairEncode (P i) (pairEncode (List.replicate (K - i) true) (Q i)) := …
/-- Once a countdown block loop reaches a live state with empty countdown, every later
iterate is `blockDone`: one more round hits the countdown guard (`step_done`). -/
theorem iterate_done {g : List Bool → List Bool}
    {upd nxt : List Bool → List Bool → List Bool} (hg : g = step upd nxt)
    {s₀ p q : List Bool} {K : ℕ} (hp : p ≠ [])
    (hK : g^[K] s₀ = pairEncode p (pairEncode [] q)) {i : ℕ} (hi : K < i) :
    g^[i] s₀ = blockDone := …
/-- Budget domination: `a'·(n+1)^k' < a'·(m+1)^k' + 1` whenever `n ≤ m`. -/
theorem lt_polyBudget_of_le (a' k' : ℕ) {n m : ℕ} (h : n ≤ m) :
    a' * (n + 1) ^ k' < a' * (m + 1) ^ k' + 1 := …
/-- Single emission: if the orbit of `g` from `s₀` is `⟨P i, ⟨1^(K-i), Q i⟩⟩` with nonempty
heads for `i ≤ K` and `blockDone` afterwards, then over any round budget `N > K` the
concatenated chunks of `emit out` are the one chunk `out ⟨P K, ⟨[], Q K⟩⟩`: only round `K`
emits (`Complexity.flatMap_range_eq_single`). -/
theorem flatMap_emit_orbit {g out : List Bool → List Bool} {s₀ : List Bool}
    (P Q : ℕ → List Bool) {K N : ℕ}
    (horb : ∀ i ≤ K, g^[i] s₀ =
      pairEncode (P i) (pairEncode (List.replicate (K - i) true) (Q i)))
    (hdone : ∀ i, K < i → g^[i] s₀ = blockDone)
    (hKN : K < N) (hP : ∀ i ≤ K, P i ≠ []) :
    (List.range N).flatMap (fun i => emit out (g^[i] s₀)) =
      out (pairEncode (P K) (pairEncode [] (Q K))) := …
/-- The output of a countdown block loop from its recurrences: from
`s₀ = ⟨P 0, ⟨1^K, Q 0⟩⟩`, under the hypotheses of `orbit`, the concatenated chunks of
`emit out` over any round budget `N > K` are `out ⟨P K, ⟨[], Q K⟩⟩` (`orbit`,
`iterate_done`, `flatMap_emit_orbit`). -/
theorem loop_output {g out : List Bool → List Bool}
    {upd nxt : List Bool → List Bool → List Bool} (hg : g = step upd nxt)
    (P Q : ℕ → List Bool) {K N : ℕ} {s₀ : List Bool}
    (h₀ : s₀ = pairEncode (P 0) (pairEncode (List.replicate K true) (Q 0)))
    (hP : ∀ i ≤ K, P i ≠ [])
    (hupd : ∀ i < K, upd (P i) (Q i) = P (i + 1))
    (hnxt : ∀ i < K, nxt (P i) (Q i) = Q (i + 1)) (hKN : K < N) :
    (List.range N).flatMap (fun i => emit out (g^[i] s₀)) =
      out (pairEncode (P K) (pairEncode [] (Q K))) := …
/-- The headline assembly: if the round `g`, the chunk `e` and the initializer `init` are
polynomial-time, the orbit of `g` has a linear envelope, and the concatenated chunks of
`e` along the orbit from `init z`, over `a'·(|init z|+1)^k' + 1` rounds, are `f z`, then
`f` is polynomial-time (`Complexity.polyTimeComputable_emitIter` after `init`). -/
theorem polyTimeComputable_of_loop {g e init f : List Bool → List Bool}
    (hg : PolyTimeComputable g) (he : PolyTimeComputable e) (hinit : PolyTimeComputable init)
    (a' k' b : ℕ)
    (horbit : ∀ (w : List Bool) (i : ℕ), (g^[i] w).length ≤ b * (w.length + 1) ^ 1)
    (hf : ∀ z, (List.range (a' * ((init z).length + 1) ^ k' + 1)).flatMap
      (fun i => e (g^[i] (init z))) = f z) :
    PolyTimeComputable f := …
/-- **A countdown block loop is polynomial-time.**  For `g = step upd nxt` and `e = emit out`
run from `⟨h₀, ⟨1^(a'(|x z|+1)^k'), r z⟩⟩`: if the updates, `out`, `x`, `r` are polynomial-time,
the live updates obey the slack bound `c`, and the chunks along the orbit are `f z`, then
`f` is polynomial-time (`polyTimeComputable_of_loop`, `length_iterate_le_of_slack`). -/
theorem polyTimeComputable_countdown {g e x r f : List Bool → List Bool}
    {upd nxt : List Bool → List Bool → List Bool} {out : List Bool → List Bool}
    (hg : g = step upd nxt) (he : e = emit out) (h₀ : List Bool) (a' k' c : ℕ)
    (hu : PolyTimeComputable (fun s => upd (pairFstD s) (pairSndD (pairSndD s))))
    (hn : PolyTimeComputable (fun s => nxt (pairFstD s) (pairSndD (pairSndD s))))
    (ho : PolyTimeComputable out) (hx : PolyTimeComputable x) (hr : PolyTimeComputable r)
    (hlive : ∀ h q, h ≠ [] →
      2 * (upd h q).length + (nxt h q).length ≤ 2 * h.length + q.length + 2 + c)
    (hf : ∀ z, (List.range (a' * ((pairEncode h₀ (pairEncode
        (List.replicate (a' * ((x z).length + 1) ^ k') true) (r z))).length + 1) ^ k' + 1)).flatMap
      (fun i => e (g^[i] (pairEncode h₀ (pairEncode
        (List.replicate (a' * ((x z).length + 1) ^ k') true) (r z))))) = f z) :
    PolyTimeComputable f := …
```

## Task 2 — Tests

After `blockAt`, a second `namespace BlockLoop` holds three publics (probe lines:
`length_flag_le` 765–769, `any_range_succ_flag` 773–776, `polyTimeComputable_orLoop` 786–817):
```lean
/-- Replacing a nonempty word by the flag `[true]` does not lengthen it. -/
theorem length_flag_le {f : List Bool} (hf : f ≠ []) (b : Bool) :
    (if b then [true] else f).length ≤ f.length := …
/-- One OR round: raising the flag on the `i`-th test value extends the flag
`[(range i).any F]` to `[(range (i+1)).any F]`. -/
theorem any_range_succ_flag (F : ℕ → Bool) (i : ℕ) :
    (if F i then [true] else [(List.range i).any F]) = [(List.range (i + 1)).any F] := …
/-- **An OR-flag block loop computes the OR of its tests in polynomial time.**  Run from
`⟨[false], ⟨1^K z, r z⟩⟩`, `K z = a'·(|x z|+1)^k'`, the loop raising its flag when `t` holds
of the remainder and advancing the remainder by `nxt`.  If the remainders follow `Q z`
(`r z = Q z 0`, `nxt (Q z i) = Q z (i+1)`), `t (Q z i) = F z i`, `|nxt q| ≤ |q| + 2 + c`,
`|x z| ≤ |r z|`, and `t`, `nxt`, `x`, `r` are polynomial-time, then so is
`z ↦ [(range (K z)).any (F z)]`.
**Proof sketch.** `polyTimeComputable_countdown` with the flag update and `out = pairFstD`;
`loop_output` at heads `[(range i).any (F z)]`, by `any_range_succ_flag`. -/
theorem polyTimeComputable_orLoop {t : List Bool → Bool} {nxt x r : List Bool → List Bool}
    (Q : List Bool → ℕ → List Bool) {F : List Bool → ℕ → Bool} (a' k' c : ℕ)
    (ht : PolyTimeComputable (fun s => [t (pairSndD (pairSndD s))]))
    (hn : PolyTimeComputable (fun s => nxt (pairSndD (pairSndD s))))
    (hx : PolyTimeComputable x) (hr : PolyTimeComputable r)
    (hnlen : ∀ q, (nxt q).length ≤ q.length + 2 + c)
    (hxr : ∀ z, (x z).length ≤ (r z).length)
    (hQ0 : ∀ z, r z = Q z 0)
    (hadv : ∀ z i, i < a' * ((x z).length + 1) ^ k' → nxt (Q z i) = Q z (i + 1))
    (htest : ∀ z i, i < a' * ((x z).length + 1) ^ k' → t (Q z i) = F z i) :
    PolyTimeComputable (fun z => [(List.range (a' * ((x z).length + 1) ^ k')).any (F z)]) := …
```
- **`polyTimeComputable_blockXorAnyTest`** is one `orLoop` call (L833–873): `t`, `nxt`, `Q` give the
  XOR test on `⟨v, ⟨x, u.drop (i·B)⟩⟩`, the carried mask and the block advance, at slack `c = 2`.
- **`polyTimeComputable_blockAnyTest`** comes after it (L912–925). It is a `convert` of the XOR
  test composed with `z ↦ ⟨z, xorD ⟨1^B, 1^B⟩⟩`, using two new privates, `zipWith_xor_self` and
  `zipWith_xor_blockAt` (L878–899).

## Task 3 — Majority; Task 4 — Loop's transducer

- **Sanctioned private redefinitions** (same types, `rfl`-equal to the base):
  `majStep := BlockLoop.step (fun _ _ => [true]) (vote push)`,
  `majEmit := BlockLoop.emit (vote comparison)`; `anyStep`/`anyEmit`/`xorStep` go with their loops.
- **`majLoop_output`** (statement kept) is `BlockLoop.loop_output` with heads `[true]`, remainders
  `⟨⟨1^cT i, 1^(i-cT i)⟩, ⟨x, rem.drop (i·B)⟩⟩`, the vote recurrence and the `decide` arithmetic.
- **`polyTimeComputable_blockMajorityTest`** is one `BlockLoop.polyTimeComputable_countdown` call,
  with the vote-push `ite`, the swapped `lenLe` bit and the `length_majVote_le` bound inline.
- **Loop:** `polyTimeComputable_xorD` uses `polyTimeComputable_of_loop`; `length_xorPairStep_iterate`
  is deleted; `polyTimeComputable_xorPairStep` becomes two `have`s.

| Base member (unlisted privates unchanged) | Disposition |
|---|---|
| Tests: `anyStep`, `anyEmit`, `anyInit`, their 3 poly lemmas, `length_anyStep_le`/`_iterate`, `anyStep_done`/`_orbit`/`_orbit_done`, `anyLoop_output` (12) | **deleted**: the OR test is the zero-mask XOR test |
| Tests: `xorStep`, `xorInit`, `polyTimeComputable_xorStep`/`_xorInit`, `length_xorStep_le`/`_iterate`, `xorStep_done`/`_orbit`/`_orbit_done`, `xorLoop_output` (10) | **deleted**: they become `orLoop`'s `t`, `nxt`, `ht`, `hn`, `hx`, `hr`, `hnlen`, `Q`, `hQ0`, `hadv`, `htest` |
| Majority: `polyTimeComputable_majStep`/`_majEmit`/`_majInit`, `length_majStep_le`/`_iterate`, `majStep_done`/`_orbit`/`_orbit_done` (8) | **deleted**: they become `countdown`'s `hu`, `hn`, `ho`, `hx`, `hr`, `hlive`, and `loop_output`'s `hnxt` |
| Majority: `majStep`, `majEmit`; `majInit`, `length_majVote_le`; `majLoop_output` | redefined; unchanged; re-proved |
| Loop: `length_xorPairStep_iterate` | **deleted**: its one site uses `length_iterate_le_of_slack 0 2` |

## Ground rules (binding)

1. **Ownership.** The three files only; imports unchanged; escalate anything the spec cannot meet.
2. **Freeze.** Every base public keeps a byte-identical statement. Of the 26, 22 are
   byte-identical in full, including the six `def`s and `blockAt` (`Randomized/PolyTimeModel`
   unfolds `blockAt` with `simp`). `polyTimeComputable_xorD`, `_blockAnyTest`,
   `_blockXorAnyTest` and `_blockMajorityTest` are re-proved; only their **Proof sketch**
   paragraphs change.
3. **Module docstrings.** Sanctioned: in Loop, one *Main definitions* and one *Main results*
   bullet; in Tests, the overview and one *Main results* bullet; in Majority, the overview and
   the *Main definitions* line.
4. **Privates.** Add no more than the reference (Loop +2, Tests +2). List every added or deleted
   declaration, and every changed private statement (`majStep`, `majEmit`). Moving
   `blockAnyTest` after `blockXorAnyTest` is sanctioned.

## Duplication and census (binding)

Run this before and after, on all six files and on the first three alone:

```sh
python3 -I audits/evidence/retrofit/copy-text-screen.py <repo-root> TCSlib/Complexity/ClassNP/PolyTimeBlock{Loop,Tests,Majority}.lean \
  TCSlib/Complexity/ClassNP/PClosure.lean TCSlib/Complexity/TuringMachine/Build/EmitIter{Body,Embed}.lean
```

| Screen | Base: declarations / pairs / characters | Reference: declarations / pairs / characters |
|---|---|---|
| Six files | 104 / 125 / 47,734 | 94 / **41** / **10,045** |
| Three files | 60 / 102 / 41,608 | 50 / **18** / **3,919** |

- **Six files.** Cross-file pairs go from 64 to 2 (corrected from 65 at the gate), both pre-existing and outside the family
  (`PClosure::union_mem_P ← polyTimeComputable_or`, 68%, and `← _not`, 52%).
- **Three files.** The 18 are Loop's 17 old in-file pairs plus one recorded in-file
  near-duplicate, `BlockLoop.polyTimeComputable_step ← polyTimeComputable_xorPairStep`
  (87/148; shared `drop 1` vocabulary). **Tests and Majority appear in no pair.**
- **Rules.** The CH7-D1 pairs collapse, and no cross-file pair is new. Justify every other new
  in-file pair; 90% or more is a copy, so factor it.
- **Census** (R2-2 counting / the screen's cross-file union): Tests 12/25 and 22/25 → **0/8**;
  Majority 8/14 and 12/14 → **0/6**; Loop 1/32 and 6/32 → **0/50**. Also rerun R2-2's rename
  method: `sed` the `maj*` names and `blockMajorityTest` to their `any` names, then run the
  three-file screen. Quote everything in `REPORT.md`, which states **"new copies: none"**.

## Environment and verification

- Lean 4 v4.25.0, mathlib pinned; `lake exe cache get`; **never `lake build`**. Check with
  `scripts/lean_check_tree.sh`.
- **Bootstrap** from `briefs/orders/ch34-t1-blockloop.txt`: the upstream closure plus the
  **24-module replay set**. The set is the three owned files, `PClosure`,
  `Randomized/PolyTimeModel`, `PolyHierarchy/{Padding,Normalize,Levels,Collapse}`, 11
  `CircuitComplexity/{KarpLipton*,Meyer*}` modules, and the facades `ClassNP`,
  `PolyHierarchy`, `CircuitComplexity` and `Randomized`.
- **Final.** The owned files: 0 errors and 0 sorry warnings. Every later module: 0 errors,
  with sorry warnings exactly the base's.
- **Axioms**, for all 46 publics: the 26 base ones byte-identical to the base, the 20 new ones
  within the triple, and no `sorryAx`.
- **Lint:** `python3 scripts/campaign_style_lint.py` on `TCSlib/Complexity/ClassNP`, 0 FAIL.
- **Out of scope** (record, do not fix): item 6 (`Build/EmitIter*`, which keeps its path and
  `exists_emitIterTM`); the internal pairs of `PClosure` and `EmitIter`; Loop's old in-file
  pairs, e.g. `length_xorPairStep_le`/`length_sliceDropAt_le`.

## REPORT.md checklist

- [ ] Base hash and ancestor check; Tasks 1–4; per-file line, public and private deltas.
- [ ] Added and deleted declarations; changed private statements (before and after); the
      docstring edits, quoted; any proof that deviates from the probe.
- [ ] The four screen outputs, the census, the rename rerun, and "new copies: none".
- [ ] Escalations or "none"; sweep tail; 46 axiom prints; lint line; diff only in the owned files.

## Known pitfalls at this pin (from the probe)

- **Pass `(g := majStep V a k)` explicitly.** `hg := rfl` then recovers `upd`/`nxt` by
  δ-unfolding, which works only because `majStep` *is* `BlockLoop.step …`.
- **`rw [loop_output …]` cannot match through `def`s.** Use
  `have hout := loop_output (g := …) (s₀ := …) …; rw [hout]`, or `(…).trans ?_`.
- **λ-arguments arrive as β-redexes**: `simp only [BlockLoop.sliceTakeAt_pairEncode_drop]` reduces
  them, `rw` does not. **`isNil` exposes `decide (· = [])`**: `unfold step isNilB`, then case on the
  `decide`s. **`omega`** handles `max`, treats `c * m` as an atom: supply `c * (m+1) = c * m + c`.
- **Vote recurrence.** Rewrite the one-round count identity first, then the `show`
  subtraction; `if_neg` on `hcnt` leaves a `+ 0` that `Nat.add_zero` misses.
- **Screen magnets (measured).** Keep `polyTimeComputable_xorPairStep` as two `have`s and
  `polyTimeComputable_emit` with `hnone` and the guards. Their one-line forms pair cross-file
  with the headlines at 50–78%.
