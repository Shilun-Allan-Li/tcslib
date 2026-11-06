# Library re-derivation sweep of `Deepen.lean`

Target: `TCSlib/Complexity/SpaceComplexity/SavitchARM/Deepen.lean` in worktree `wt-196`, branch
`lean/ch34-deepen-landing`, head `a46e04a9` (847 lines; the brief said 845). All line numbers below
are lines of that source file. No tracked file was edited and nothing was committed or pushed:
`git status --short` in `wt-196` is empty before and after. The scratch Lean files are in
`wt-196/rvprobe/dpsweep/`, which is git-excluded through `rvprobe/` in `.git/info/exclude`. Lean was
run only through `leanelab.sh`, one elaboration at a time.

Not re-reported (already dispositioned): `size_facts` (658, 750, 776), `length_bits_le_log` (411),
`dpSt*` against `RegExt.update`/`Fin.append`, and the private `bits_succ_le` of another file.

## Result in one paragraph

Five inline proofs re-establish one published core/Mathlib lemma each:

* **G1**: `dp_mem` re-proves `decide_eq_true_iff`.
* **G2**: `dp_run`'s `hn` re-proves `Nat.size_le.mp`, with the same proof term Mathlib uses.
* **M1–M3**: three sites `le_trans (by omega) (Nat.le_mul_of_pos_left _ hc)` re-prove Mathlib's
  `le_mul_of_one_le_of_le`, with the same `b ≤ c ≤ a * c` argument.

All five replacements were applied together in one scratch copy (`DpC.lean`, `copyC.diff`). It
elaborates with **exit 0 and no messages**, the same as an unmodified baseline copy (`base.log`).

Three further changes are **optional** (S1, S2, G2b; not hits). Copy D (`DpD.lean`, `copyD.diff`)
contains them together with the five hits, and it also elaborates with exit 0 and no messages.

Everything else is an idiom (it already cites the relevant library lemma), or no library lemma
states it.

## Snapshot deviation (please read)

The brief names `oleans-ldwa3`. That directory existed when I started: the first baseline
elaborated against it with exit 0. Between 02:26 and 02:45 it was removed by another process; it is
not in `$TCSLIB_SCRATCH` any more, and every later run against it failed with
`unknown module prefix 'TCSlib'`. I did not rebuild or restore anything.

I switched to `oleans-ldp`. According to `fills/replay/replay-ldp.sh`, that snapshot was made by
`cp -R oleans-ldwa3 oleans-ldp`, with fresh `.olean`s added only for `SavitchARM/Deepen`,
`Savitch` and `SpaceComplexity` at `302119dc`. Two checks make it equivalent here:

* `git diff --name-only 302119dc a46e04a9` lists only `Savitch.lean` and `SavitchARM/Deepen.lean`.
  Neither is an import of `Deepen`.
* None of my files imports `Deepen`. Each is standalone, with `Deepen`'s three imports.

So for every module these files load, `oleans-ldp` is exactly `oleans-ldwa3`. Every result below
(baseline included) was re-run against `oleans-ldp`. The command was:

```
bash /home/user/tcslib/devtools/seyoon/leanelab.sh /home/user/tcslib-scratch/wt-196 \
  /home/user/tcslib-scratch/oleans-ldp rvprobe/dpsweep/<File>.lean
```

Each command was prefixed by `. /home/user/tcslib-scratch/env.sh`, and the scripts were run with
`python3 -I`. Each log ends with the line `-- exit=N, T s (snapshot oleans-ldp)`.

## Method

1. **Enumeration.** I read the whole file. `all_sites.txt` (from `grep -nE`, 224 lines) lists every
   `have`, `obtain`, `private theorem`, `calc` step and `rw`/`simp only`/`simp_all` argument list.
   The anonymous `have :=` sites are 119, 413 (mid-line), 837 and 839. All four are plain
   citations (`r.isLt`, `logSpace_le_size_succ n`, `ha.2 r`, `Nat.two_pow_pos _`). The only
   `obtain … : stmt` is 736 (`b = false`, TCSlib content). I kept the core/Mathlib-only statements,
   generalised where needed.

   For the TCSlib-headed facts I computed the import closure (`closure.txt`, 116 modules) and
   searched the tree at the head (`git grep a46e04a9`) for a published lemma stating them:
   * `logSpace` lower bound: none.
   * `n < 2 ^ |bits n|`: only outside the closure (see the notes).
   * indicator iff: only outside the closure.
   * clear/copy chains, block bound: none.
   * Codec-oracle bridges: only the parallel lemmas for a different oracle.
2. **In-context probe (copy A).** `mk_copyA.py` replaces each candidate proof in place by
   `exact?` tagged `DPSWEEP:<id>`.
   * Because the file sets `maxHeartbeats 0`, an unbounded `exact?` ran for 21 min without
     output. A tactic-level `set_option maxHeartbeats … in` did not bound it.
   * So copy A was split. `DpA1` and `DpA2` cover the probes up to `dp_prep` and finished in
     about 20 s each.
   * The 13 later probes were run one file each (`DpSA*.lean`, logged in `copyS.log`), with the
     file-level limit set to `maxHeartbeats 1000000`.
   * `copyA3.log` and `copyA4.log` are the aborted grouped runs, kept only as a record. A3 hit
     the 1500 s cap (exit 124); I stopped A4 after 632 s (exit 130). Neither produced any output.
3. **Generalised probe (file B).** `DpB.lean` has 25 standalone `example`s under the module's
   three imports (`copyB.log`, 37 s).
4. **Normalised cores (file B2).** `DpB2.lean` holds the "core" the inline argument proves, after
   the one obvious hypothesis rewrite, probed with `exact?`. The open statements are probed with
   `apply?` (`copyB2.log`, 13 s). The log is 196 KB because of the `apply?` listings; its useful
   lines are quoted below.
5. **Judgement.** I used the previous sweep's rule. A site is a **hit** when the inline proof
   re-establishes the content of one published lemma whose statement is the fact or a direct
   specialisation of it. It is an **idiom** when the proof already cites the relevant library
   lemma and only adapts its shape, or when a lemma does only part of the job.
6. **Replacement test (copy C / copy D).** `mk_copyC.py` applies the hits (copy C), and with
   `--optional` also the optional items (copy D). Each old text must occur exactly once. No line
   over 100 characters is added; the ten long lines are pre-existing.

## Candidates and results

A = in-context `exact?` (copy A / single files), B = generalised `example`, B2 = normalised core.
✗ = could not close the goal; "t/o" = heartbeat timeout in context (in `whnf`/`isDefEq` on the
`2 ^ (W * W)` terms), so B/B2 decide.

| id | line | owner | statement (generalised) | A | B / B2 | disposition |
|---|---|---|---|---|---|---|
| A01 | 117–121 | `dpρ_ne` | `n ≤ r'.val → Fin.castLE h r ≠ r'` | ✗ | B01 ✗; D10 `(castLE h r).val = r.val` is `rfl` | no library lemma |
| **A04** | 204–206 | `dp_mem` (after `rw [dpOrc, indicator_eq_decide]`) | `decide p = true ↔ p` | finds `decide_eq_true_iff` (instance to pin) | B04 same; **D03 `decide_eq_true_iff`** | **hit G1** |
| A02 | 279–281 | `dpSt_upd_ρ` `e` | `r' = castLE h r ↔ ⟨r'.val, _⟩ = r` | `eq_iff_eq_of_cmp_eq_cmp rfl` | B02 same | idiom: a definitional trick, not a statement of the fact (inline is `Fin.ext_iff` ×2 + `rfl`) |
| A03 | 298–301 | `dpSt_upd_own` `e` | `r' = r ↔ ⟨r'.val - 18, _⟩ = i` | ✗ | B03 ✗ | no library lemma |
| A28 | 319 | `dp_bd_blk`, anonymous | `¬ r'.val < 18 → ∀ r, dpρ r ≠ r'` | ✗ | (B01) | no library lemma; it is the file's own `dpρ_ne r (by omega)` (in-file reuse, out of scope) |
| — | 312 | `dp_bd_blk` (private thm) | off-range agreement + on-range bound ⇒ bound | – | B21 ✗; tree grep: none | no library lemma |
| A05 | 390 | `dp_cT_run` `rw [zero_add, one_mul]` | `(0 + 1) * a = a` | ✗ | B05 ✗ | idiom (two core rewrites, no single lemma) |
| — | 402–404 | `dp_cT_run` `rw […]; congr 3; ring` | `a + b + (j+1)*b = a + (j+2)*b` | – | B24 ✗ | idiom (`ring`) |
| A06a | 409/413 | `dp_bits_logSpace` conj. 1 | `logSpace n ≤ 1 + |bits n|` | ✗ | B07, B07b ✗; D04 `logSpace_le_size_succ` | idiom: already cites `logSpace_le_size_succ` (+ `omega` for `add_comm`) |
| A06c | 409/413 | `dp_bits_logSpace` conj. 3 | `n < 2 ^ |bits n|` | ✗ | B06 ✗ | idiom: already cites `Nat.lt_size_self` through `Nat.size_eq_bits_len`. Becomes unused after G2 (optional G2b). |
| A08 | 458 | `dp_prep` `o1b` | `(if p i then 0 else g i) ≤ B` | ✗ | B20 ✗ | no library lemma |
| A09 | 492 | `dp_prep` `o4W` | `update o1 0 _ 1 = 0` | `rfl` | – | definitional, no library lemma |
| A10 | 504–513 (+ 577–583, 799–806) | `dp_prep` `o5S` etc. | `c ≠ a → c ≠ b → update (update f a x) b y c = f c` | `exact hS` (defeq) | B12 ✗; D08 `apply?`: none | no library lemma (`Function.update_of_ne` chains) |
| — | 469, 520, 539 … | `zero_add` rewrites | `0 + s = s` | – | B23 `Nat.zero_add` | idiom (the rewrite *is* the lemma) |
| A11 | 615–627 | `dp_fit` `hiff` | `(∃ u, 0 ≤ u ∧ u < n ∧ P u) ↔ ∃ u < n, P' u` | ✗ | B18 ✗; D07 `apply?` partial only | idiom (rintro bridge through `dp_initO`/`dp_accO`), no single lemma |
| **A12** | 657 | `dp_block` `hsw` | `1 ≤ c → s ≤ c * (s+ℓ+1)` | ✗ | B08 ✗; **D02 `le_mul_of_one_le_of_le ha h`** | **hit M1** |
| A13 | 724–727 | `dp_body` `hBB` | `a ≤ b → 2^(a*a) ≤ 2^(b*b)` | ✗ | B09 ✗ | idiom: cites `Nat.pow_le_pow_right` + `Nat.mul_le_mul h h`. Optional S1 is `Nat.mul_self_le_mul_self`. |
| — | 721, 728 | `hWs`, `hw` | `Nat.mul_le_mul_left/…` applications | – | – | idiom (citations) |
| A14 | 744–746 | `dp_body` `hs` | `s ≤ sp` from the edge bit | ✗ | – | TCSlib content (`noEdge_of_lt`), not a library fact |
| A16 | 747–753 | `dp_body` `hsB` | `s + 1 ≤ 2^(W*W)` | t/o | B22 ✗; D12 `apply?` partial | idiom (h1–h4 + `omega`); contains M2 |
| **(A15)** | 751–752 | `dp_body` `hsB.h4` | `1 ≤ c → s+1 ≤ c * (s+1+…+1)` | (inside A16) | **D02** | **hit M2** |
| **A17** | 774–775 | `dp_run` `hW1` | `1 + |bits n| ≤ (k+1) * (…)` | ✗ | **D02** | **hit M3** |
| **A18** | 777–778 | `dp_run` `hn` | `|bits n| ≤ m → n < 2^m` | ✗ | B10 ✗; **D01 `Nat.size_le.mp h`** | **hit G2** |
| A19 | 791–793 | `dp_run` `e21` | `a ≠ b → update (update f a x) b y a = x` | `rfl` | B11 ✗; D09 `apply?`: none | no library lemma (definitional on literals) |
| A20 | 830 | `deepen_contract` `hls` | `1 ≤ logSpace n` | `tsub_add_cancel_iff_le.mp rfl` | B13 same; tree grep: no published lemma (NARMExample/NARMLogspace also inline it) | not a library fact; `omega` one-liner |
| A21 | 833–835 | `deepen_contract` `hW3` | `W ≤ 3 (k+1) X` | ✗ | – | idiom (`mul_comm`/`mul_assoc` + `Nat.mul_le_mul_left`) |
| A22a | 836–840 | `deepen_contract` `hlt` | `a ≤ 2^m → a + 1 < 2^(m+2)` | t/o | B14 ✗; D05 `apply?` partial only | no library lemma |
| A22b | 838 | `hlt` `e` | `2^(m+2) = 4 * 2^m` | t/o | B15 ✗; D06 `Nat.pow_add 2 m 2` | idiom: already `rw [pow_add]; ring` |
| A24 | 842 | `deepen_contract` `h1` | `a ≤ b → a*a ≤ b*b` | `Nat.mul_le_mul hW3 hW3` (the inline term) | B16 same | idiom. Optional S2: `Nat.mul_self_le_mul_self hW3` (core, whose body is this term). |
| A25 | 843 | `deepen_contract` `h2` | `1 ≤ X * X` | `NeZero.one_le` | B17 same; D11 `Right.one_le_mul h h` | idiom: cites `Nat.one_le_iff_ne_zero` + `positivity` |
| A26 | 844 | calc step 1 | `a ≤ b → 1 ≤ c → a + 2 ≤ b + 2c` | t/o | B19 ✗ | `omega` one-liner, no library lemma |
| — | 845 | calc step 2 | `ring` identity | – | – | `ring` |
| — | 208–224 | `dp_rel`/`dp_initO`/`dp_accO` | Codec-oracle bridges for `dpOrc N ∘ σ` | – | tree grep | not a re-derivation: `rel_orcN`/`initO_orcN`/`accO_orcN` (`SavitchARM/Correct.lean:55–71`) are for the different oracle `orcN : Fin 4 → …`; these are generic in `σ` and cite `rel_iff_orc`/`initO_iff_orc`/`accO_iff_orc` |
| — | 349, 379 | `dp_cb_run`, `dp_cT_run` | clear chain / repeated copy | – | tree grep | no published counterpart (`ARMLoops` has `move/copy/shl/sub/halve_run` only; `FragDec.clr_run` is a TM-level lemma) |
| — | 335, 343, 115, 436, 437, 397, 628, 692 | wrappers / one-term citations | `copy_run`, `shl_run`, `Fin.castLE_injective`, `Nat.le_mul_of_pos_left`, `Nat.lt_two_pow_self`, `Function.update_of_ne`, `decide_eq_decide` | – | – | citations |

## Genuine hits and tested replacements (copy C)

| hit | line | what the inline proof re-derives | tested replacement |
|---|---|---|---|
| G1 | 204–206, `dp_mem` | `⟨of_decide_eq_true, decide_eq_true⟩` assembles the iff `decide_eq_true_iff` from its two directions | `exact @decide_eq_true_iff _ (Classical.dec _)` (the instance must be pinned; plain `exact decide_eq_true_iff` fails to synthesise `Decidable (V ∈ dpAs N j)`, as A04/B04 report) |
| G2 | 777–778, `dp_run` `hn` | `(lt_size_self).trans_le (Nat.pow_le_pow_right _ h)` is verbatim Mathlib's proof of `Nat.size_le.mp` (`Mathlib/Data/Nat/Size.lean:92–93`); conj. 3 of `dp_bits_logSpace` is `Nat.lt_size_self` | `have hn : x.length < 2 ^ dpW N sp x := Nat.size_le.mp (by rw [← Nat.size_eq_bits_len]; omega)` |
| M1 | 657, `dp_block` `hsw` | `le_trans (b ≤ c) (c ≤ a * c)` is Mathlib's `le_mul_of_one_le_of_le` (`Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean:849`, the same calc) | `le_mul_of_one_le_of_le hc (by omega)` |
| M2 | 751–752, `dp_body` `hsB.h4` | same | `le_mul_of_one_le_of_le hc (by omega)` |
| M3 | 774–775, `dp_run` `hW1` | same | `le_mul_of_one_le_of_le (by omega : 1 ≤ codeK N + 1) (by omega)` |

G1 and G2 are clear. M1–M3 are the borderline class, like the previous sweep's G4: each inline
proof is two citations chained by `le_trans`. They are included because the chain is exactly the
published lemma's proof and `exact?` names it on the normalised core (D02). The maintainer can take
G1/G2 alone. The hunks are independent, since each keeps its `have` statement unchanged.

## Optional (copy D = copy C + these; not hits)

| id | line | change | why optional |
|---|---|---|---|
| S1 | 727 `hBB` | `Nat.mul_le_mul (hWs s hs) (hWs s hs)` → `Nat.mul_self_le_mul_self (hWs s hs)` | the inline already cites a library lemma; core's `Nat.mul_self_le_mul_self` (`Init/Data/Nat/Lemmas.lean:742`) is defined as exactly that term. `exact?` itself proposes the inline term (A24/B16). Cosmetic. |
| S2 | 842 `h1` | `Nat.mul_le_mul hW3 hW3` → `Nat.mul_self_le_mul_self hW3` | same |
| G2b | 406–413, 829 | with G2, conjunct 3 of `dp_bits_logSpace` (`n < 2 ^ |bits n|`, i.e. `Nat.lt_size_self`) has no remaining use; drop it (and its docstring clause), and `.2.1` → `.2` at 829 | dead-code clean-up after G2, not a re-derivation |

## Elaboration outputs

| file | content | result |
|---|---|---|
| `base.log` | unmodified copy `DpBase.lean` (`cmp`-identical to the source) | exit 0, no messages, 9 s |
| `copyC.log` | `DpC.lean`: G1, G2, M1–M3 | **exit 0, no messages**, 8 s |
| `copyD.log` | `DpD.lean`: copy C + S1, S2, G2b | **exit 0, no messages**, 7 s |
| `copyA1.log`, `copyA2.log`, `copyS.log` | in-context probes | as in the table |
| `copyB.log`, `copyB2.log` | generalised / core probes | as in the table |

`copyC.diff` (5 hunks, 7 lines changed) and `copyD.diff` are unified diffs against the target file.

## Notes

* **Out-of-closure duplicates (not citable from `Deepen` without a new import).**
  * `Complexity.LogProg.lt_two_pow_bits` (`Randomized/SpaceAmplifyPoly.lean:249`) states
    conjunct 3 of `dp_bits_logSpace`. The private `qy_lt_two_pow_bits`
    (`Diagonalization/NTimeDiagonalizer.lean:3258`) states it too.
  * `indicator_eq_true_iff` (`ClassPSPACE/TQBFHardBridge.lean:46`, `Randomized/PTMEquiv.lean:109`)
    states `dp_mem`'s content.
  * Neither module is in `Deepen`'s import closure, so G1/G2 use the core/Mathlib lemmas instead.
* **No `1 ≤ logSpace n` lemma is published.** `Machines/NARMExample.lean:98` and
  `Machines/NARMLogspace.lean:92` inline it too. A shared `one_le_logSpace` in
  `SpaceComplexity/Basic.lean` would be a separate change.
* **`Language` membership has no `Decidable` instance.** Every `decide_eq_true_iff`-style
  replacement in this area needs `(Classical.dec _)`.

## Files

* `README.md` (this file); `copyC.diff`, `copyD.diff`.
* `mk_copyA.py` (an optional third argument selects probes) and `mk_copyC.py` (`--optional` gives
  copy D).
* `all_sites.txt`, `closure.txt`; `copyA1_tags.tsv`, `copyA2_tags.tsv`, `copyS*_tags.tsv`,
  `copyB_tags.tsv` (probe line maps).
* Logs: `base.log`, `copyA1.log`, `copyA2.log`, `copyS.log`, `copyB.log`, `copyB2.log`,
  `copyC.log`, `copyD.log`. The aborted runs are `copyA3.log` and `copyA4.log`.
* Scratch Lean (git-excluded), in `wt-196/rvprobe/dpsweep/`: `DpBase.lean`, `DpA1.lean`,
  `DpA2.lean`, `DpA3.lean`, `DpA4.lean`, `DpSA*.lean`, `DpB.lean`, `DpB2.lean`, `DpC.lean`,
  `DpD.lean`.
