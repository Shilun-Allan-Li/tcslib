# EF-H1 · `ef-h1-arith` · final

**Final head `0a73fc9c1a743954e30676982ed721ba7e573679`** on local branch `fill/ef-h1-arith`
(unchanged since checkpoint 1, exchange commit `9a5cc15ac5078c4d8700acee75fd1bb414ff75bc`), base REC
`cf6a2266e9556ca8ad61e56f7232266ccc6d4e62` (tree `d52cf05bb20c08b6547468d1bd489f1cf0d2e442`).
Worker: Claude (cloud), lead only; no sub-agents were used.

## 0. Headline: E-SCOPE on the field theorems

Everything this job can prove under Rule 10 is proved and compiles; the brief's headline
theorems are **blocked by nine missing readers in frozen files** (E-SCOPE, §6). In detail:

| Brief target | State at this checkpoint |
|---|---|
| `polyTimeComputable_sizeStr : PolyTimeComputable sizeStr` | **proved** (File A) |
| `polyTimeComputable_{mul,add,sub,divMod,le,modExp}Str` | proved in **re-paired form** `PolyTimeComputable fun z => f ⟨pairFstD z, pairSndD z⟩` (File A); the step to `PolyTimeComputable f` is **E-SCOPE** |
| `polyTimeComputable_xgcdStr` | proved in re-paired form (File B, extended Euclid, every modulus); final step **E-SCOPE** |
| `def PrimesInP`, `primesInP_iff` | **proved** (File C) |
| `polyTimeComputable_primeStr_of_primesInP` and converse | **E-SCOPE**; the half that needs no reader is proved: `polyTimeComputable_primeStr_iff_bitsVal` |
| `ArithmeticFP.ofPrimesInP`, `arithmeticFP_iff_primesInP` | **E-SCOPE** (needs all of the above) |

**Why.** `Arithmetic.lean` publishes readers of `mulStr`, `addStr`, `subStr`, `divModStr`,
`xgcdStr`, `modExpStr`, `leStr` **only on encoded pairs** (`mulStr_pairEncode a b`, …). A field
`PolyTimeComputable mulStr` is about every word, malformed ones included, and the only way to
read `mulStr z` on a word that is not `pairEncode a b` is its body: a foreign read (Rule 10;
the seals fail on it — control NEG4 below). `sizeStr_eq` and `primeStr_eq` are every-input
readers, so `sizeStr` goes through. Likewise `Randomized.PRIMESBin` (`Primality.lean:63`) and
`Randomized.PRIMES` (`PrimalityMath.lean:77`) publish no membership reader, so `PRIMESBin ∈ P`
cannot be related to any primality test without unfolding them; both are in
`TCSlib/Complexity/**`, read-only for wave 1.

**What I deliver for it.** The nine requested readers are one-line `rfl`/`Iff.rfl` lemmas
(§6). With them, every remaining target is a one-liner over the theorems of this series. This
delivery carries a separate, **compiled scope-request overlay** under
`evidence/scope-request/` (two commits on a local branch `scope/ef-h1-readers` on top of the
fill head; **not** part of `patches/`): the nine readers, the seven missing field theorems,
the `PRIMESBin` bridge, `ArithmeticFP.ofPrimesInP` and `arithmeticFP_iff_primesInP`, with H1-P2
passing and standard axioms (§7a). It can land as soon as Seyoon rules (question EF-H1-W1).
Nothing in the fill series reads a foreign body.

## 1. Base and inputs

- Inputs: all nine SHA-256 of COMMON §1 match at records pin
  `54dcb3021a389831e7f94c3f82616cb7594fa574` (`rulings.md`, `COMMON.md`, `EF-H1/brief.md` read).
- `git rev-parse cf6a2266… cf6a2266…^{tree}` = the REC pair above; `git diff --name-only cf6a2266
  b1219429 -- TCSlib TCSlib.lean lakefile.lean lake-manifest.json lean-toolchain` is empty.
- Information only: records tip now `83375341b75f71bab3e6f20f94991cf8ad69141b`;
  `git merge-tree --write-tree <head> <tip>` = `397f4eaf1aae460e92c80405fa182b5b353d5545` (clean).

## 2. Environment and pool

- Preflight (`evidence/logs/preflight.log`): `nproc` 4; no cgroup memory limit, `MemAvailable`
  15,802,576 kB (15.07 GiB ≥ 4 GiB); disk 19.98 GiB free on ext4 ≥ 12 GiB. Toolchain v4.25.0
  installed after the preflight; 18.9 GB free before the cache step (≥ 8 GiB).
- Cache: store absent before the first fetch (`cache-store.log`). First attempt passed 99 roots
  including `Std.Sat.CNF` and the tool stopped (`unknown module prefix 'Std'`,
  `cache-get-attempt1.log`); the addendum's recipe takes `import Mathlib` lines only, so the
  retry used the 98 Mathlib roots: 2,876 files downloaded and decompressed, rc 0. 0 zero-size
  oleans; packages: all present ones match the manifest, ABSENT `doc-gen4`, `UnicodeBasic`,
  `BibtexQuery`, `MD4Lean` (`cache-check.log`); cache probe `import
  Mathlib.Algebra.BigOperators.Field` rc 0.
- Bootstrap: the 183-module closure of the three new files' imports and the `Candidates` facade
  (`evidence/build/order-base.txt`), pool 3 in dependency order: 182 OK; the one FAIL is the
  facade, which I had already edited to import the not-yet-built new modules (sequencing, not a
  base failure); it passes at the head (C1). Heaviest: `ClassP/BinaryArith/DetMod` 1,250 s,
  2.49 GB.
- Pool (`evidence/logs/pool.log`): 3 = min(4, ⌊15.07/4⌋); raised to 4 (= `nproc`) for my own
  checks beside the bootstrap, MemAvailable never under 13.8 GB. Peak RSS of one Lean process
  3.29 GB (the facade). One ENOSPC (a `git clone`, no Lean running): the full exchange
  checkout took 7.7 GB; I removed my two extra worktrees and re-created the exchange checkout
  sparse (my inbox path only); 14.2 GB free afterwards.
- Final sweep: pool 4; peak RSS of one process 3.77 GB (`audits/pass-shelat/Checks`),
  MemAvailable never under 11.5 GB. I stopped my pool driver (PID 15320) once every
  checkable module had finished (it waited on modules downstream of the PFR failures).
- `lake build` never run; no unfiltered cache get; every module through
  `scripts/lean_check_tree.sh`; Python as `python3 -I`.

## 3. Commits (`COMMITS.tsv`, `patches/`)

| # | Commit | Content |
|---|---|---|
| 1 | `4f9bba64dc323d2d0cc765fbf1befacd7e8227d9` | File A `Candidates/ArithmeticDischarge.lean` |
| 2 | `8d26ba1d56f26076df67da927ed591471632d17c` | File B `Candidates/ExtendedEuclidMachine.lean` |
| 3 | `58165f504ca6bf3c46f6936f1f5e7071d38f4bf9` | File C `Candidates/PrimesInP.lean` |
| 4 | `bba10dd8aab995d8334869186850ed4fa162a127` | facade `Candidates.lean`: 3 imports, 3 `## Contents` entries |
| 5 | `0a73fc9c1a743954e30676982ed721ba7e573679` | File B: readers `xgcdCoefStep_eq`, `xgcdLoopStep_eq`, `xgcdLoopInit_eq`, `xgcdLoopInv_iff` |

All unsigned (`%G?` = N; `gpgsig` count 0). 840 inserted lines, nothing deleted.

## 4. Target map

| Brief target | Declaration(s) |
|---|---|
| `mulStr`, `addStr`, `subStr`, `divModStr`, `leStr` | `polyTimeComputable_{mul,add,sub,divMod,le}Str_pairEncode` (A) |
| `modExpStr` | `polyTimeComputable_modExpStr_pairEncode` (A; triple re-paired) with `modExpModulus`, `_eq`, `_spec`, `polyTimeComputable_modExpModulus` |
| `sizeStr` | `polyTimeComputable_sizeStr` (A) — **the target itself** |
| `xgcdStr` | `polyTimeComputable_xgcdStr_pairEncode` (B), from `xgcdLoopOut_spec`, `xgcdInvWord_spec`, `polyTimeComputable_xgcdLoopOut` |
| `PrimesInP`, `primesInP_iff` | as named (C) — **the targets themselves** |
| bridge | `primeBit_eq_primeStr_fromLEPoly`, `polyTimeComputable_primeStr_iff_bitsVal` (C); rest E-SCOPE |
| `ofPrimesInP`, `arithmeticFP_iff_primesInP` | E-SCOPE |

Glue helpers (A): `polyTimeComputable_toLE_pairFstD`, `_pairSndD`, `_pair`, `toLE_pair_eq`,
`fromLEPoly_var_bits`, `polyTimeComputable_fromLEPoly_var`.

**The xgcd loop (B).** State `⟨b, ⟨⟨r', r⟩, ⟨s' mod b, s mod b⟩⟩⟩`; one round is Mathlib's
`Nat.xgcdAux` step (`Nat.xgcdAux_rec`) with the coefficient kept modulo `b`
(`xgcd_coef_residue`), states with `r = 0` fixed. Start `⟨b, b, a mod b, 0, 1 mod b⟩` (the
arguments of `Nat.xgcd (a mod b) b`); invariant `XgcdLoopInv` = "Mathlib's recursion from this
state ends where it ends from the start". Potential: `extEuclidCalls r' r + 1`
(`NumberTheory/Euclid.lean`), which a round lowers by one (`extEuclidCalls_of_mod_ne_zero`) and
which starts ≤ `2|b| + 1` by **`extEuclidCalls_le` [PS10, Claim 43.3]**; so `2(|z|+1)` rounds of
`BinArith.polyTimeComputable_iterate`, states ≤ `11(|z|+1)` bits. At the end `s' =
Nat.gcdA (a mod b) b` (`Nat.xgcd_zero_left`, `Nat.xgcdAux_val`, `Nat.xgcd_val`), and
`xgcdInvWord_spec` identifies it with `((a : ZMod b)⁻¹).val` for every `b` (`b = 0`: the sign,
`Int.natAbs_sign`; `b = n+1`: Mathlib's `ZMod.inv` by `rfl`, `ZMod.val_intCast`,
`ZMod.val_natCast`). No Fermat inverse anywhere (brief).

## 5. Statement changes

1. The six pair fields and `xgcd` are stated in re-paired form
   `PolyTimeComputable fun z => f (pairEncode (pairFstD z) (pairSndD z))` (for `modExpStr` the
   triple `⟨pairFstD z, ⟨pairFstD (pairSndD z), pairSndD (pairSndD z)⟩⟩`) instead of
   `PolyTimeComputable f`. Reason: Rule 10 and the missing every-input readers (§0, §6). Not a
   weakening of the mathematics: with `f_eq` the targets follow in one line each (the overlay
   will show it compiled), and the H1-P1 probe checks `f z = machine z` on every tested word.
2. The bridge is split: the reader-free half `polyTimeComputable_primeStr_iff_bitsVal`
   (`primeStr` poly ⇔ little-endian test poly) is in the series; the `PRIMESBin` half waits for
   `mem_PRIMESBin`/`mem_PRIMES`.
3. Additional public declarations beyond the brief's list: the glue helpers and loop pieces
   listed in §4 (50 public declarations at source in all; StmtDump in
   `evidence/probes/StmtDump.log`).

## 6. Scope requests (E-SCOPE)

| # | File (frozen) | Proposed reader (one line each) |
|---|---|---|
| S1–S7 | `Cryptography/Candidates/Arithmetic.lean` | `mulStr_eq`, `addStr_eq`, `subStr_eq`, `divModStr_eq`, `xgcdStr_eq`, `modExpStr_eq`, `leStr_eq` : `f z = <its body>` `:= rfl` (every word) |
| S8 | `Complexity/Randomized/PrimalityMath.lean` | `Randomized.mem_PRIMES (N : ℕ) : N ∈ PRIMES ↔ N.Prime := Iff.rfl` |
| S9 | `Complexity/Randomized/Primality.lean` | `Randomized.mem_PRIMESBin (x : List Bool) : x ∈ PRIMESBin ↔ bitsVal x ∈ PRIMES := Iff.rfl` |

Exact texts: `evidence/scope-request/patches/0001-*.patch` (S1–S9), files at the overlay head in
`evidence/scope-request/src/`. None of the nine names exists
anywhere at the base, IO, #377's head or S2-A's branch (C10).

## 7. Checks

- **C1** (`evidence/build/summary.txt`): the four modules at the head: rc 0, 0 errors (both
  forms), 0 `sorry` warnings, source SHA-256 = `git show HEAD:<path>`.
- **C2** downstream sweep: the facade is imported by `TCSlib.lean` and
  `audits/pass-shelat/Checks.lean`.
  Full sweep of their 1,449-module closure at the head (`build/order-root.txt`, pool 4, after a
  second narrowed cache fetch for the 380 Mathlib roots of the closure: 731 files, rc 0,
  `logs/cache-get-root.log`; packages re-checked, `cache-check-root.log`):
  **1,428 OK**, among them the three new files, the facade and **`audits/pass-shelat/Checks`
  rc 0** (the facade's importers other than the root); **3 FAIL, all `unknown module prefix 'PFR'`**
  (`CommunicationComplexity/NewmanTheorem/{Newman, Entropy/Basic, FuncDisjointnessLowerBound/
  HardSample}` import the `PFR` package, whose oleans no Mathlib cache provides and which only
  a `lake build` of the package could produce — banned); **18 not run** because they import
  those (the rest of `NewmanTheorem` and the root **`TCSlib`**). Per the addendum (item 8) no
  check ran against a missing prerequisite. So **the root module `TCSlib` is unchecked here**;
  the facade itself and `Checks` (which imports it) pass. 0 errors in every OK log; the 192
  `sorry` warnings of the sweep are all in untouched modules
  (`build/C2-rootsweep-summary.txt`, `logs/rootsweep/`, `logs/rootsweep-pool.log`).
- **C3** `decls2.py`: 50 ADDED, nothing else (`checks/C3-decls2.txt`); StmtDump: 61 public
  constants (50 declarations + 11 `_proof_N` auxiliaries).
- **C4** no `sorry`/`admit`/`native_decide`/`axiom`/`opaque` (one hit: the word "axiom" in
  `PrimesInP`'s docstring prose); no existing file but the facade changed, so the base's
  `sorry` set is unchanged.
- **C5** `#print axioms` of all 50: every one ⊆ {`propext`, `Classical.choice`, `Quot.sound`};
  0 `sorryAx` (`probes/C5-axioms-summary.txt`).
- **C6** Rule 10 (`evidence/seals/`): canonical seals (every ordinary TCSlib definition of the
  full import closure defined in another module, matchers included, `_private` names
  unnameable and left out; A = `PolyExpr.eval` excluded, B = sealed; coe = strict here since no
  FinDist coercion instance is in the ordinary-definition lists), `-DmaxErrors=0`: **coe-A,
  coe-B, strict-A, strict-B: all three files PASS** (443/444/1,111–1,112 names). Collector-only
  seal (gate-04 collector) PASS. My own three files are foreign to each other (B's list seals
  A's `modExpModulus`; C's seals A's and B's definitions). Paired controls
  (`controls-{Unsealed,Sealed}.log`): unsealed all 8 pass; sealed, NEG1 (`modExpModulus`, A),
  NEG2 (`xgcdState`, B), NEG3 (`PrimesInP`, C), NEG4 (`mulStr`, base: the scope request) each
  fail exactly once, POS1–POS4 (readers) pass. Explicit-unfold scan: 0 foreign
  (`unfold-scan.txt`; control with `rw [… toLE …]` gives exactly 1). **Reader census** (foreign
  definitions read, collector lists): `BinArith.{add,sub,le,mul,div,mod,gcd,powMod}` via
  `*_pairEncode` (`AddSub.lean:147,152,202`, `Mul.lean:113`, `Div.lean:58,62`,
  `ModPow.lean:57,261`) and `polyTimeComputable_*`; `LogProg.bitsVal` via `bitsVal_bits`
  (`Machines/Bin.lean:67`), `bitsVal_lt_two_pow` (`:86`), `bitsVal_toLE`; `pairFstD`/`pairSndD`
  via `pairFstD_pairEncode`/`pairSndD_pairEncode` (`PolyTimePairing.lean:233,237`),
  `length_pairSndD_le`; `pairEncode` via `length_pairEncode` (`Encoding.lean:220`);
  `PolyExpr.eval` via `eval_var` (`PolyExpr.lean:119`); `toLE` via `toLE_eq_natBits`,
  `bitsVal_toLE`, `length_toLE_le` (`Encoding/BinaryArith.lean:72,94,102`); `fromLEPoly` via
  `fromLEPoly_pairEncode` (`:216`); `natToList`/`listToNat` via `listToNat_natToList`,
  `natToList_mod_two_pow`, `listToNat_lt_two_pow` (`Arithmetic.lean`); the bundle's functions
  via `*_pairEncode` (`Arithmetic.lean:338–452`; `primeStr_eq` at `:455`), `sizeStr_eq` (`:369`), `primeStr_eq` (`:455`);
  `extEuclidCalls` via `extEuclidCalls_of_mod_ne_zero`, `extEuclidCalls_le` (`Euclid.lean:116,175`);
  `PolyTimeComputable`, `P`, `PRIMESBin` in statements only. **MISSING**: S1–S9 (§6).
- **C7** facade: base 68 → head 80 lines, 0 non-insert differences, the 12 inserted lines are
  the 3 imports and the 3 `## Contents` entries (9 lines); control (one altered character) → 1
  difference. `git diff --stat` lists only the brief's four files.
- **C8** `style_lint.py` on the four files: 0 findings. Campaign lint `--check8b`: base
  92 FAIL / 103 WARN over 531 files (= the maintainer's REC figures), head 92 / 103 over 534;
  FAIL and WARN line sets identical (`lint/C8-diff.txt`).
- **C9** sizes: A 236 lines (max width 99), B 496 (100), C 96 (97), facade 79 (95).
- **C10** no new full or short name is declared in `TCSlib/` or `audits/` at REC, IO
  `5ed465f6…`, #377 `7563734a…` or S2-A `c119a3c4…` (66 names incl. the overlay's; regex
  control on `mulStr_pairEncode` hits). Note: #377's head has moved to `e8553378…`; I checked the
  pinned `7563734a…`.
- **C11** §8.
- **C12/H1-P1** (`probes/H1P1.{lean,log}`, `#eval`): each string function against the machine
  composition its proof uses, on all 961 pairs of words of length ≤ 4 plus all 127 words of
  length ≤ 6 (malformed pairs, zero moduli), in both the re-paired and the raw form: **0
  mismatches for each of the eight functions and both primality directions**; `modExpStr` on
  4,463 inputs (triples of words ≤ 3, words ≤ 6, pairs ≤ 4); `xgcdStr` on `⟦b⟧ ∈ {0, 1, 2, 4, 6,
  9, 12}` (width 4; `0` also at widths 0, 2) × `⟦a⟧ < 16`: 144/144 rows agree, e.g.
  `8⁻¹ mod 12 → 11` (Mathlib's `gcdA` residue for a non-unit), `7⁻¹ mod 12 → 7`, `b = 0 → sign`.
  Kernel `decide`: `mulStr` and `leStr` instances pass; `xgcdStr` does not reduce in the kernel
  (well-founded recursion), so it is `#eval` only.
- **H1-P2** consumer smoke test: needs `ofPrimesInP` (E-SCOPE); it passes on the overlay (§7a).
- **C13** `git am` of `patches/` at the base with `COMMITS.tsv`'s committer data: 5/5 hashes
  reproduced; `src/` equals the head byte for byte (`checks/C13-reproduction.txt`).

## 7a. The scope-request overlay (`evidence/scope-request/`)

Local branch `scope/ef-h1-readers` from the fill head `0a73fc9c…`:

| # | Commit | Content |
|---|---|---|
| R1 | `b3eba3914d1b3532b01b8fe2fbcfaeb068d2f3b2` | S1–S9: `Arithmetic.lean` +44 lines (7 `_eq` readers), `PrimalityMath.lean` +3 (`mem_PRIMES`), `Primality.lean` +4 (`mem_PRIMESBin`) |
| R2 | `f5e67909ff8a61f67f254217e8de90782a0eb4f6` | the targets: `polyTimeComputable_{mul,add,sub,divMod,modExp,le}Str` (A), `polyTimeComputable_xgcdStr` (B), `primeBit_eq_indicator`, `primesInP_iff_polyTimeComputable_primeBit`, `polyTimeComputable_primeStr_of_primesInP`, `primesInP_of_polyTimeComputable_primeStr`, `ArithmeticFP.ofPrimesInP`, `arithmeticFP_iff_primesInP` (C); module docstrings updated |

- Patches: `scope-request/patches/` (`git format-patch 0a73fc9c..f5e67909`).
- Build (own olean tree; 170 unaffected modules seeded from the lead tree, sources and
  upstreams byte-identical, list `seed-list.txt`): the 16 affected modules rebuilt in order,
  all rc 0 (`build-pool.log`), i.e. every existing consumer of `Arithmetic.lean` and
  `Primality.lean` in the closure (`Concrete`, `Factoring`, `RSA`, `Rabin`, `DiscreteLog`,
  `DiscreteLogHardcore`, `DDH`, `ElGamal`, `Encoding/BinaryArith`) is unaffected; summary at
  the overlay head `build/summary.txt` (7 changed modules rc 0, 0 errors, 0 `sorry`).
- `decls2.py` against the fill head: 22 ADDED, nothing else.
- Reproduction: `git am` of the two patches at the fill head with `COMMITS.tsv`'s committer data
  gives both hashes; `src/` equals the overlay head (`C13-reproduction.txt`).
- Seals coe-A and strict-B on the three new files at the overlay head: PASS.
- **H1-P2** (`H1P2.lean`, `H1P2.log`): `ArithmeticFP.ofPrimesInP h` elaborates where
  `factoringCollection_oneWay`, `rsaCollection_oneWay`, `dlCollection_oneWay` and
  `polyTimeComputable_expEval` expect `H : ArithmeticFP`; `#print axioms` of the 13 new targets:
  all exactly `[propext, Classical.choice, Quot.sound]`.

## 8. Overlap and reuse

Searches (`checks/C11-searches.txt`, at REC and IO; plus the C10 scans): `toLE (pairFstD|Snd…`
(12/8 hits, all `Encoding/DyadicArithmetic.lean` inside proofs of `polyTimeComputable_addPoly`
etc.: local `have`s, no public helper to cite — near-relative, same composition style, the
brief's precedent); `fromLEPoly .var` (0 at REC; 2 at IO in `CoinSampling/Efficiency.lean`,
inline); `gcdA|xgcdAux|Nat.xgcd` (1 hit, a docstring): **no machine computes Bézout
coefficients**; `PolyTimeComputable (…Str)`: only the bundle's fields and `Factoring.lean`'s
hypothesis; `PrimesInP`/`PRIMESBin ∈`: none; `powMod … 2 ^`: one private lemma in
`DiscreteLogHardcore.lean:1053` (different statement).

Must-reuse items and where used: `BinArith.add/sub/le/mul/div/mod/powMod/gcd` with their
`*_pairEncode` readers and `polyTimeComputable_*` (A, B); `polyTimeComputable_iterate`,
`iterate_invariant`, `iterate_measure_eq_zero` (B); `toLE`, `toLE_eq_natBits`, `bitsVal_toLE`,
`length_toLE_le`, `fromLEPoly`, `fromLEPoly_pairEncode`, `polyTimeComputable_fromLEPoly` (A, B, C);
`mulStr_pairEncode` and the other `*_pairEncode`, `listToNat_natToList`, `natToList_mod_two_pow`
(A, B, C); `extEuclidCalls_le` [PS10, Claim 43.3] (B); Mathlib's `Nat.xgcdAux_rec`,
`Nat.xgcd_zero_left`, `Nat.xgcdAux_val`, `Nat.xgcd_val` (B); `PRIMESBin` (C). Also reused, found
by my search: **`BinArith.polyTimeComputable_powerOfTwo`** (`ClassP/BinaryArith/Unary.lean:43`,
`bits (2^{|z|})`) for the zero-modulus case of `modExpStr` (my first draft built that word
from zeros and a normalizer; replaced before commit), `BinArith.polyTimeComputable_isZero`,
`polyTimeComputable_ite`, `polyTimeComputable_pairConcat`, `polyTimeComputable_unaryPoly`,
`BinArith.polyTimeComputable_slot2/slot3`.

Not reused, with reason: `GcdInv`, `gcdMeasure`, `gcdInv_step` (`ModPow.lean:279–306`, which the
brief suggests for the round bound). `gcdStep` has no reader, so the loop's `⟨r', r⟩` slot cannot
be identified with a `gcdStep` state without unfolding it, and `GcdInv`/`gcdMeasure` have no
readers either; the textbook call count `extEuclidCalls` with its published equations and
`extEuclidCalls_le` gives the bound instead (and matches the cited [PS10, Claim 43.3]).
`extEuclid_spec`/`extEuclid_inv` are not used: the field's value is Mathlib's `ZMod.inv`, so the
agreement is proved with Mathlib's `Nat.xgcd` (brief).

Near-relatives (disclosed, no copy): `xgcd_coef_residue` is a three-line `Int.ModEq` computation
(Mathlib's `Int.mod_modEq`, `ModEq.add/sub/mul_left`); `length_xgcdState_le` is a length count
over `length_pairEncode`; `primeBit_eq_primeStr_fromLEPoly` uses `fromLEPoly_pairEncode` rather
than re-deriving `listToNat w.reverse = bitsVal w` (which `Encoding/BinaryArith.lean` proves
only inside a proof). No private declarations; no copies.

## 9. Attribution

Only ingested anchors: [PS10] Algorithm 43.2, Claim 43.3 (`pass-shelat-2010-ch2.raw.md`
l. 987, 1005), Algorithm 45.5, Theorem 45.6 (l. 1082, 1094), p. 33 ("primality testing can be done
in polynomial time", l. 512–520) and the closing remark of §2.6.5 on AKS (l. 1286–1288, p. 50 of
that text). **Anchor correction:** the brief's [PS10] "p. 33 remark (AKS)" is two places: p. 33
says only that primality testing is polynomial-time; the AKS sentence is in §2.6.5. [AB09]:
the AKS sentence is block **`pdf-26d95080dbde-p003-b004`** (the brief guessed `b003`, which is
Definition 7.4); the ingested draft numbers that subsection **7.2.1**, while TCSlib's
`Primality.lean` (and I) cite it as §7.2.2 (the published numbering); chapter notes
`p017-b001` ("later AKS proved PRIMES ∈ P") confirmed. Glue declarations say "Glue".

## 10. Questions for Seyoon

**EF-H1-W1. The nine missing readers (E-SCOPE).**
- **A (recommended).** Land S1–S9 (one `rfl`/`Iff.rfl` line each, in `Arithmetic.lean`,
  `PrimalityMath.lean`, `Primality.lean`) and then this job's overlay commit with the seven
  `polyTimeComputable_*Str`, `polyTimeComputable_xgcdStr`, the bridge, `ArithmeticFP.ofPrimesInP`
  and `arithmeticFP_iff_primesInP` (delivered compiled with the final). The two Complexity
  readers touch read-only Arora–Barak files: owner agreement needed.
- **B.** Land only S1–S7 now (Candidates); keep the `PRIMESBin` bridge for later, with
  `ofPrimesInP` stated from `PolyTimeComputable primeStr` (ruling Q-H1-1 B's form) meanwhile.
- **C.** Grant a Rule-10 exception for these `rfl` reads in the new files (not recommended).

**EF-H1-W2. The root sweep's PFR gap.** `TCSlib.lean` cannot be elaborated on a fill host
without `PFR` oleans.
- **A (recommended).** The maintainer's landing replay (which has PFR built) checks `TCSlib`;
  this delivery's C2 stands for the 1,428 other modules.
- **B.** Authorize a narrowed build of the `PFR` package for wave-1 fills (an exception to the
  `lake build` ban).

**EF-H1-W3. Anchor corrections** (§9): accept [PS10, p. 33, §2.6.5] and [AB09, §7.2.2]
(block `p003-b004`).

## 11. Evidence manifest

`evidence/SHA256SUMS` lists every evidence file; the top-level `SHA256SUMS` lists every
delivered file. Main items: `logs/` (preflight, cache, pool, bootstrap per module, dev logs),
`build/` (order, summary, per-module logs), `checks/` (C3, C4, C7, C9, C10, C11, C13,
merge-tree), `probes/` (H1P1, StmtDump, Axioms, C5 summary), `seals/` (results, candidate
lists per variant, controls, unfold scan, tools used), `lint/`, `tools/` (my scripts),
`scope-request/` (the overlay: patches, COMMITS.tsv, src, build, seals, H1-P2, reproduction).
