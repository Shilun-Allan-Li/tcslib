# Probes (check 7), gsw-6b statements — sub-agent `probe`

**Head.** Final runs at the statement head 8f92fe7d53967bc488a4075fb38210e7d40b9031 (O2 head
5bd5ada5f42c5e1228ea84ad70f4d8c52a3644fd), oleans `/home/user/oleans/probe` = copy of the lead's tree built from
sources identical to 8f92fe7d (NOTES.md §6). Each probe: `python3 -I tools/lead/pool_run.py <label> <log> -- bash
tools/probe/run_probe.sh <file>` (plain `lean <file>`, no `-o`); raw logs `<probe>.log`, pool lines (rc, max RSS,
seconds) in `final-runs*.txt`; long `#eval`s also stream `<probe>.progress`.
**Methods.** Kernel `decide` (every such theorem's `#print axioms` is listed: standard axioms only, unless noted) or
`#eval` (evidence only, never a proof); **no `native_decide`** anywhere. Errors in both forms
(`^\S+\.lean:\d+:\d+: error`): 0 in every final log except the negative control P3x (exactly its 4 expected errors).
**Strict evaluators.** `#eval` of the library's closure-folding `homEvalPBP` is exponential in the program length;
probes evaluate probe-local strict versions (`EvalA.snippet`, `Boot.snippet`, `Level.snippet`, `Tab.snippet`:
array accumulator, tabulated program maps) that are **proved equal** to the library definitions through their
readers only (`evalA_eq`, `tabB_eq`, `formulaA_eq`, `bootNANDA_eq`, `bootGateA_eq`, `fheEvalA_eq`, `levelGateA_eq`,
`leveledEvalA_eq`, `leveledEvalCircuitA_eq`; all standard axioms except `leveledEvalCircuitA_eq`, which inherits
`sorryAx` from 6a's `toNANDForm`/`layerNAND` statements). So each `#eval` evaluates the library definition itself.
**Not kernel-reducible:** anything built from `Nat.clog` or `barrington` (well-founded recursion): `decryptFormula`,
`nandFormula`, `decDepth`, `homEvalFormula`, `bootNAND`, `fheEval`, `leveledEval` — `#eval` only
(`P4_kernel_attempt.log`: `decide +kernel` on G6/G7 gets stuck).

| probe | statement(s) probed | parameters | method | outcome |
|---|---|---|---|---|
| P1 `P1_Selector` | `select` on noise-free bits: `select P (b•G) (u•G) (v•G) = ((1−b)u + bv)•G` (∀ bits), also via `encrypt` under the zero key; exact `select P (b•G) U V = (1−b)•U + b•V` on fixed non-ciphertext `U, V` | `n=1, m=2, ℓ=3`, `q ∈ {4,5,8}` (`N=6`) | kernel `decide` | **true** (`sel_bits_q4/q5/q8`, `encrypt_zero_pk_q5`, `sel_encrypt_zero_pk_q5`, `sel_exact_q5/q8`) |
| P1 `P1_Selector` | G1 `Encrypts.select`: conclusion `Encrypts P t ((1−b)u+bv) (βV + 2(Nβ)) (select P C U V)` for ciphertexts with explicit errors under `t = (−3,1)` | `n=1, m=2, q=256, ℓ=8` (`N=16`, bound 67 < 128), β=2, βV=3, 8 bit triples × 2 error patterns + a worst-case pattern | kernel `decide` of a witness check proved sound (`encrypts_of_check` via `encrypts_iff`) | **true**; observed noise 8–19 (bound 67); worst-case construction (`U` all-ones decomposition, `C` errors `+2`) reaches 32 = N·β (`g1_tight`: bound 31 refuted), so G1's bound is valid and loose by ≈ N·β (true worst case is N·β + βV) |
| P2a `P2a_PBP` | G2 noise-free: `homEvalPBP P B (x•G) (Pi.single s₀ G) i = (decide (B.yield x s₀ = i))•G` | width-3 permutation program, length 3, 2 inputs; `n=1,m=2,q=5,ℓ=3`; all `x, s₀, i` | kernel `decide +kernel` (max RSS 5.6 GB) | **true** (`g2_noisefree`; `B3_perm` proved) |
| P2b `P2b_PBPNoise` | G2 with noise: noise ≤ `B.length·2·N·β` = 96 | same program; `q=256, ℓ=8` (`N=16`), input errors ±1 (β=1), start 0, all `x, i` | inputs' hypotheses by kernel `decide`; conclusion's witness check by `#eval` (strict evaluator) | **true** in all 12 cases, observed noise 5–12 (bound 96). A kernel-`decide` version reached 13.2 GB and was OOM-killed (`P2b_kernel_attempt.out`) |
| P2c `P2c_Formula` | G3 `homEvalFormula` noise-free: coordinate `σ 0` = `(c.eval x)•G`, coordinate 0 = `(!c.eval x)•G`, other coordinates 0, `decrypt` (secret 2) of the output = `c.eval x` | `n=1,m=2,q=5,ℓ=3`; 7 formulas: two depth-2 XORs (`∧` of `∨`s, `∨` of `∧`s; Barrington length 16), `x₀∧x₁`, `x₀∨¬x₁` (length 4), fan-in-1 node, both constants; all 4 inputs | `#eval` (strict evaluator on the tabulated program, proved equal) | **all 5 checks true in all 28 cases** (`P2c_Formula.final-partial.txt`, streamed at 8f92fe7d). The noise part (G3's bound `4^d·2Nβ` at `q = 4096`, `N = 24`) was stopped after 21 CPU-minutes to free the pool (a `q = 65536` attempt earlier also stopped): G3's noise bound has no numeric probe; G2's noise bound (P2b) and G1's (P1) do |
| P3 `P3_DecodeInterval` | O2 `decode_iff_mem_Ico` at `LWE.Parameters ⟨1,1,q⟩`, every residue | every `2 ≤ q ≤ 63` | kernel `decide` (62 theorems `o2_q2`…`o2_q63`) | **true**, 62/62, standard axioms |
| P3 | same | every `64 ≤ q ≤ 2000` (1,937 moduli) | `#eval` mismatch count | **0 mismatches** (and 0 over `2 ≤ q ≤ 63`) |
| P3x `P3x_Control` | negative control: wrong upper end `≤ decodeHi`, wrong lower end `decodeLo − 1 ≤` | `q ∈ {63, 8}` | kernel `decide` | all 4 refuted ("decide proved that the proposition … is false"), exactly 4 errors |
| P4 `P4_DecryptFormula` | G5 `vecMul_secretVector_eq_sum`, every secret and ciphertext | `TP 1 2 1` (`N=2`, 16 C × 2 s), `TP 0 4 2` (16 C) | kernel `decide +kernel` | **true** (`g5_B`, `g5_C4`) |
| P4 | proposed owner-side `decrypt_eq_decode_dotProduct` (census MISSING) | same | kernel `decide +kernel` | **true** (`dot_B`, `dot_C4`) |
| P4 | G5, G6 `decryptFormula_eval`, `decrypt_eq_decode_dotProduct`, every secret | `TP 1 2 1` all C (32 checks), `TP 0 4 2` all C (16), `TP 1 3 2` 200 pseudo-random C (600), `TP 1 4 2` 40 C (160), `TP 1 5 3` 6 C (30), `TP 1 8 3` 4 C (32) | `#eval` | **0 mismatches** in each |
| P4 | G7 `nandFormula_eval`; G8 depth `≤ decDepth P + 1`, fan-in `≤ 2` | `TP 1 2 1` all 256 pairs (512 checks), `TP 1 3 2` 40 pairs, `TP 1 4 2` 8 pairs, `TP 1 5 3` 2 pairs | `#eval` | **0 mismatches / 0 violations**; max depth vs `decDepth+1`: 11 vs 16, 24 vs 27, 24 vs 27, 29 vs 32 |
| P5a `P5_Bootstrap` | G9's object `bootNAND` (key-switching form with `t' = t`): `bootNAND evk C₁ C₂ = (!(dec C₁ && dec C₂))•G` and decrypts to it | `A0 = (n=0, m=2, q=2, ℓ=1)` (`N=1`; augmented formula depth 10, Barrington program 49,024 instructions); evaluation key = `evalKey` of the honest noise-free key; all 4 pairs of `1×1` ciphertexts | `#eval` (strict evaluator, proved equal; 16.7 min) | **true for all 4 pairs** (NAND truth table `1,1,1,0`) |
| P6a `P6a_LeveledKeys` | `literalCts` decrypts to `litInput x` under `s_0` (∀ x, j) | `n=1, m=2, q=2, ℓ=1` (`N=2`), honest noise-free keys `s_0=0`, `s_1=1` | kernel `decide +kernel` | **true** (`literal_ok`) |
| P6a | L1's object: `levelKey … 0 j` decrypts under `s_1` to `keyBits s_0 j` (∀ j) | same | kernel `decide +kernel` | **true** (`levelKey_ok`); under `s_0` it gives `[true,false]` ≠ `keyBits s_0 = [false,true]` (keys differ in effect) |
| P6a | the level-1 gate's message: `nandFormula (lit0) (lit1)` on `keyBits s_0` = `NAND(x0,x1)` | same, all 4 inputs | `#eval` | **true** for all 4; the inputs decrypt *wrongly* under `s_1` (e.g. `(1,1) ↦ (false,true)`), so the key chain is exercised. A full `leveledEval` gate at these parameters (one `bootNAND`, 196,096 Barrington instructions) did not finish in 29 CPU-minutes (killed): distinct-key end-to-end runs are out of reach of `#eval`; P6b runs them at `n = 0` |
| P7 `P7_Constants` | G8 `decDepth_le` closed form | 1,746 GSW parameter sets: `n ≤ 8`, `ℓ ≤ 40`, `q ∈ {2, 3, 2^(ℓ−1)+1, 2^ℓ−1, 2^ℓ}` | `#eval` | **0 violations**, min slack 13 |
| P7 | no term linear in ℓ | `n=1, q=2^ℓ, ℓ = 1, 2, 4, …, 4096` | `#eval` | `decDepth` = 15, 26, 35, 46, 57, 68, 75, 86, 97, 104, 115, 126, 137: +7…+11 per doubling of ℓ (logarithmic) |
| P7 | G13 `bootNoise_le` | same grid × β ∈ {0,1,5,1000} (6,984) | `#eval` | **0 violations** |
| P7 | G13's derivation: (i) `2^⌈log₂ y⌉ < 2y` (1 ≤ y ≤ 100000); (ii) `4^(9a+2b+22) ≤ 4^33·N^18·X^4` on the grid; (iii) `8·4^33·2 = 2^70` (pBoot's constant) | — | `#eval` | (i) 0 violations, (ii) 0 violations, (iii) true |
| P7 | G16 `bootRatio_le_poly` with the explicit `pBoot` | families F1 (`n=κ+1, q=2^(κ+2), ℓ=κ+2`) and F2 (`n=2κ, q=3^(κ+1), ℓ=2κ+2`, loose bounds), κ ≤ 30, B ∈ {1,3} | `#eval` | **0 violations** (124 checks); min rhs/lhs ≈ 1.8·10^18 (F1) |
| P7 | G17's hypothesis `pBoot(κ)·B < q(κ)` is satisfiable | F1, B = 1 | `#eval` | first κ in {100,…,1500}: **600** (non-vacuous) |
| P8 `P8_Asymptotic` | every asymptotic definition/statement (A1, A3, `WeakCircularSecureFamily` + reader (A2), `ReductionEfficient`, `LeveledReductionEfficient`, `RatioBounded`, G16, G17 pure/leveled, encodings) instantiated | sample families Fc (constant `n=1,m=2,q=5,ℓ=3`) and F1, `L = var + 1` | elaboration (`example`/`#check`) | **all elaborate**; `ofFamily_lwe`/`_width` used as stated; `(ofFamily F κ).columns` = 6 (Fc), 4 (F1,κ=0), 49 (F1,κ=5); `pBoot` evaluates; `pBoot Fc` = `2^70·3·6^19·12^4·2` (true); `Fc.RatioBounded (fun _ => 1) (.const 5)` **proved** through `ratioBounded_iff` |

## Nothing false

No probe found a statement false: every kernel `decide` succeeded with standard axioms, every `#eval` check
printed 0 mismatches / `true`. The negative controls (P3x; P1's `g1_tight`) fail exactly as expected.

## Unevaluable or only partially evaluated (precisely)

* **`homEvalFormula`, `bootNAND`, `fheEval`, `leveledEval(Circuit)`** are not kernel-reducible (`Nat.clog`,
  `barrington`: well-founded recursion) — `#eval` only.
* **Bootstrapping cost.** One bootstrapped gate is Barrington's program for the augmented decryption
  formula: at the smallest parameters `A0 = (n=0, m=2, q=2, ℓ=1)` depth 10, 49,024 instructions, ≈ 2–4 min of
  `#eval` (P5a: 4 gates in 16.7 min); at `n=1, q=2, ℓ=1` depth 11, 196,096 instructions, one gate did not
  finish in 29 CPU-minutes (killed, `scratch/boot2.*`). At `q = 5, ℓ = 3` the formula has depth 29 (2.2·10⁶
  nodes): no bootstrapped gate is evaluable there. Hence P5/P6 run at `A0`, where the secret is the empty
  vector (key separation is checked separately in P6a at `n = 1` without Barrington).
* **P2c's G3 noise part** (q = 4096) and the earlier q = 65536 attempt were stopped (21 CPU-min) to free the pool.
* **P5b, P6b** were capped at 25 minutes each (lead's order): see their rows for the inputs evaluated.
* A first version of P2b (kernel `decide` of G2's witness check at q = 256) was OOM-killed at 13.2 GB.

## Files

Probe sources `P*.lean` (each self-contained; snippets `EvalA.snippet` (with `Tab.snippet`), `Boot.snippet`,
`Level.snippet` are the shared evaluator code pasted into them), logs `P*.log`, streamed progress `*.progress`,
pool lines `final-runs*.txt`, `P2b_kernel_attempt.out`, `P4_kernel_attempt.log` (the stuck G6/G7 kernel
attempt), `P2c_Formula.final-partial.txt`. `scratch/`: timing experiments (`boot*.lean`: bootstrapped-gate
timings; `bl.lean`: Barrington construction times; `timing/`: the evaluator bisection). Generator:
`tools/probe/mk_p3.py` (P3, P3x). P6b's header comment was corrected after its capped run (no code change):
it now says the AND/xor/odd circuits are not run.

## P5b and P6b (rows added by the lead after the sub-agent stopped)

| probe | statement(s) probed | parameters | method | outcome |
|---|---|---|---|---|
| P5b `P5b_FheEval` | G10's object `fheEval` on `xorPad` (6 NAND gates incl. one of fan-in 0 and one of fan-in 1, the padding `(G, G)`, `(a, a)`): output `= (Cc.eval x)•G` and decrypts to `Cc.eval x` | `A0 = (n=0, m=2, q=2, ℓ=1)`, honest noise-free evaluation key | `#eval` (strict evaluator `fheEvalA`, proved equal: `fheEvalA_eq`, standard axioms) | **partial**: input `(true, false)` true on both checks. The sub-agent's run was capped at 25 min (no input finished); the lead's uncapped run (22:34Z) was killed by a container restart after this input; not re-run (over an hour per input) |
| P6b `P6b_LeveledCircuits` | L2's object `leveledEval` on `twoC.layerNAND`, `twoC = NAND(x₀, NAND(x₁))` (layering needs a parity twin; 9 gates, depth 2): output `= (C.eval x)•G` under the key of level 2, decrypts to `C.eval x`; `twoL = twoC.layerNAND` is layered, NAND-form, depth 2, and `twoC` is not layered | `A0`, three honest noise-free keys | `#eval` (`leveledEvalA_eq`, standard axioms) for the run; kernel `decide` for `twoL_ok` | **true on all 4 inputs** (lead's uncapped run, 3,104 s, rc 0, `P6b_LeveledCircuits.uncapped.log`); `twoL_eq : twoL = twoC.layerNAND` by `rfl` (uses `sorryAx` through 6a's admitted N12/N13 proof fields, as expected). `xorL`, `oddL` (6a's P9 circuits) were built and checked structurally but not run |
