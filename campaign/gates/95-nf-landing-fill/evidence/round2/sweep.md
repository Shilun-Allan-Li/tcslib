# Gate 95 (PR #191, `ClassNP/NDNormalForm`): the inline-step sweep at the repaired head

Evidence (run by a sub-agent of the cloud maintainer session, reviewed by the maintainer) for findings 1, 3 and 5 of `campaign/gates/95-nf-landing-fill/findings.md`.
Text-only (no build). Candidate enumeration plus inspection, not an exhaustive search.

- **Repaired head** (local): `10c015177fde0f9f2b020c010cf44f0f3b3dd37f`, file blob
  `ad4202caae768181dfb38f0dec71fd293543c165` (3,272 lines).
- **Landed head** (`origin/pr/191` = `origin/lean/c1-nf-landing`):
  `e8994dc115fd61a940509516b658a9975edbb71a`, file blob `9474847a83af572f66bd4218fe78fc3b18f5c852`
  (3,289 lines; the blob the auditor read).
- The repair changes only this file (`git diff --stat e8994dc1 10c01517`: 1 file, +43 −60):
  `nf_pack` (RN-1), `nf_aReturn`, `nf_bClear`, `nf_region` (finding 1) and the headline's
  docstring (finding 4).
- Published API read at `10c01517`: `TuringMachine/BufferWords.lean` (`bufferTape_append_shift`
  47, `_append_mid` 58, `_drop` 69, `_take` 83, `_eq_none_of_not_mem` 94, `_unary` 107),
  `TuringMachine/Simulation.lean` (`bufferTape_nil` 634, `_nat` 640, `_left` 644, `_eq` 649,
  `_of_neg` 655), `TuringMachine/CfgFacts.lean` (`Cfg.inputSymbol_congr` 51,
  `Cfg.mapState_eq_of_fields` 69, `Cfg.mapState_const_eq_mapState_sigma` 87,
  `Cfg.mapState_sigma_state_ne` 101, `length_flatMap_uniform` 113),
  `Build/Contract/Basic.lean` (`Segment` 420, `segment_iff` 428, `Segment.trans` 460,
  `Segment.take`/`drop` 487/494, `Segment.time_eq` 509), `Build/Seam.lean`
  (`phaseHostTM_run_le` 876, `phaseHostTM_run` 898), `Build/EmitIterEmbed.lean` (`SafeRun.trans` 94,
  not in NF's import closure), `Finite.lean` (`MultiTapeTM.exists_first_halt` 218),
  `Nondeterministic.lean` (`NDTM.runWith_append` 172, `runWith_of_halt` 218),
  `ChoiceWords.lean` (`Turing.run_take_of_halted` 107), `Randomized/PTM.lean`
  (`Turing.FinNDTM.runWith_eq_runWith_take` 148).

## Commands

Every command was run as `. /home/user/tcslib-scratch/env.sh; …`. `S` is
`$TCSLIB_SCRATCH/agents/sweeps`.

```sh
cd /home/user/tcslib
git show 10c015177fde0f9f2b020c010cf44f0f3b3dd37f:TCSlib/Complexity/ClassNP/NDNormalForm.lean \
  > $S/raw/NDNormalForm-10c01517.lean.txt
git show e8994dc115fd61a940509516b658a9975edbb71a:TCSlib/Complexity/ClassNP/NDNormalForm.lean \
  > $S/raw/NDNormalForm-e8994dc1.lean.txt
git diff e8994dc1 10c01517 -- TCSlib/Complexity/ClassNP/NDNormalForm.lean   # the repair
# counts at both heads (PCRE, so `\b` is a word boundary)
cd $S/raw
for F in NDNormalForm-e8994dc1.lean.txt NDNormalForm-10c01517.lean.txt; do
  for p in 'bufferTape_eq\b' 'bufferTape_eq[],]' 'bufferTape_nat' 'List\.getElem\?_' \
    'getElem\?_append|getElem_append|getElem\?_drop|getElem_drop|getElem\?_take|getElem_take' \
    'Nat\.exists_eq_add_of_le' 'runFrom_add' 'runFrom_of_halt' 'runWith_append' 'runWith_of_halt' \
    'lt_trichotomy' 'Nat\.find' 'Cfg\.ext' 'obtain ⟨\w+, rfl⟩ : ∃ \w+, \w+ = .*\+'; do
    printf '%-60s %s\n' "$p" "$(grep -cP "$p" $F)"; done; done
# the hits, with line numbers
F=NDNormalForm-10c01517.lean.txt
grep -nE 'bufferTape|List\.getElem\?_|getElem_append|getElem\?_append|getElem_drop|getElem\?_drop|getElem_take|getElem\?_take|drop_append|take_append|List\.get\?|getElem!|drop_drop' $F
grep -nE 'List\.(take|drop)_[A-Za-z_]+' $F
grep -nE 'runFrom_add|runWith_append|runWith_of_halt|Nat\.find|Cfg\.ext' $F
grep -nP 'obtain ⟨\w+, rfl⟩ : ∃ \w+, \w+ = .*\+' $F
grep -nE 'exists_add_of_le|Nat\.le\.dest|le_iff_exists_add|Nat\.add_sub_of_le|Nat\.sub_add_cancel|← MultiTapeTM\.runFrom_add|exists_first_halt|runFrom_state_ne_none|runFrom_output' $F
grep -n 'Cfg\.mapState_[a-zA-Z]*\|Segment\|segment_iff' $F
# published forms that might apply, and NF's import closure (text-only, at the repaired head)
cd /home/user/tcslib; C=10c015177fde0f9f2b020c010cf44f0f3b3dd37f
git grep -nE '^(protected )?theorem (NDTM\.)?runWith_[A-Za-z_]*|theorem [A-Za-z_.]*first[A-Za-z_]*' $C -- 'TCSlib/Complexity/TuringMachine/*.lean'
git grep -nE 'theorem [A-Za-z_.]*(runWith|runFrom)[A-Za-z_]*(take|of_halt|halt)[A-Za-z_]*' $C -- 'TCSlib/*.lean'
git grep -n 'run_take_of_halted' $C -- 'TCSlib/*.lean'
git grep -nE '^(theorem|lemma|def|structure) [A-Za-z_.]*(SafeRun|safeRun|Guard|guard_|_trans\b)' $C -- 'TCSlib/Complexity/TuringMachine/**/*.lean'
python3 -I - $C <<'EOF'   # BFS over `import TCSlib.…` lines from NDNormalForm, read with `git show $C:<path>`
import sys,subprocess,re
T=sys.argv[1]
def imports(mod):
    r=subprocess.run(['git','show',f'{T}:'+mod.replace('.','/')+'.lean'],capture_output=True,text=True)
    return None if r.returncode else [m.group(1) for m in re.finditer(r'^import\s+(\S+)',r.stdout,re.M)]
seen=set(); st=['TCSlib.Complexity.ClassNP.NDNormalForm']
while st:
    m=st.pop()
    if m in seen: continue
    seen.add(m); im=imports(m)
    if im: st.extend(i for i in im if i.startswith('TCSlib'))
for t in ['TuringMachine.Build.EmitIterEmbed','TuringMachine.ChoiceWords','Randomized.PTM','TuringMachine.Finite']:
    print(t, 'TCSlib.Complexity.'+t in seen)
print(len(seen))
EOF
# -> EmitIterEmbed False, ChoiceWords False, PTM False, Finite True; 30 modules
```

The owner of each hit and the `Cfg.ext` block extents were read with two `python3 -I` one-off
scripts over the same file (declaration header search upward; block = the indented lines under
`apply Cfg.ext`, with a `mapState` test on the block's text). Every hit below was then read in
context. The line maps between the heads are exact (repaired = landed + offset, cumulative): +1
after `nf_aReturn` (1041), −4 after `nf_bClear` (1150), −2 after `nf_region` (2305); the time-split and `Cfg.ext` lists below were
grepped at both heads and match one for one.

## Counts

| Sign (pattern) | landed `e8994dc1` | repaired `10c01517` | old sweep (`4354cbeb`, `evidence/sweep.txt`) |
|---|---|---|---|
| `bufferTape_eq` as a word | 0 | 0 | 0 (`bufferTape_eq[],]`) |
| `bufferTape_nat` | 7 | 3 | not swept |
| `List.getElem?_*` (any) | 13 | 10 | not swept |
| append/drop/take indexing (`getElem?_append…`, `getElem?_drop`, `getElem?_take…`) | 5 | 4 | not swept |
| `Nat.exists_eq_add_of_le` | 0 | 0 | 0 |
| `runFrom_add` | 34 | 34 | not swept (finding 5 (2)) |
| `runFrom_of_halt` | 0 | 0 | 0 |
| `runWith_append` | 3 | 3 | not swept |
| `runWith_of_halt` | 2 | 2 (one is docstring 3230) | not swept |
| `lt_trichotomy` | 0 | 0 | 0 |
| `Nat.find` | 4 | 4 (one site) | 4 |
| `Cfg.ext` | 12 | 11 | 12 |
| `obtain ⟨v, rfl⟩ : ∃ v, u = a + v` time splits | 13 | 13 | not swept (finding 5 (3)) |

The landed-to-repaired drops are exactly the repair: four `bufferTape_nat` and three
`List.getElem?_*` (`_drop`, `_eq_none` twice) leave `nf_bClear`, `nf_aReturn` and `nf_region`, and
one `Cfg.ext` leaves `nf_pack`. A plain `grep -E bufferTape_eq` also matches the three
`bufferTape_eq_none_of_not_mem` citations (1045, 1290, 2305); none unfolds `bufferTape_eq`.

## Findings 1 and 3: the four repaired sites

| Site (repaired line; landed) | Now | Published lemma | Status |
|---|---|---|---|
| `nf_bClear`, `hw` (1153; 1150–1156) | `rw [h, FinTM.bufferTape_drop R i h0, add_comm]` | `FinTM.bufferTape_drop` (BufferWords 69) | finding 1 (a) closed: the `bufferTape_nat`×2 + `List.getElem?_drop` + `congr 1; omega` steps are gone |
| `nf_aReturn`, `hw` (1045–1046; 1044–1045) | `FinTM.bufferTape_eq_none_of_not_mem s (z := (s.length : ℤ)) (by omega), FinTM.bufferTape_nil` | `FinTM.bufferTape_eq_none_of_not_mem` (BufferWords 94) | finding 1 (b) closed |
| `nf_region`, `p = L` (2305–2310; 2309) | `rw [hpL, FinTM.bufferTape_eq_none_of_not_mem]`, side goal `rw [List.length_ofFn]; omega` | same | finding 1 (c) closed |
| `nf_pack`, `hinit` (64–69; 62–69) | `exact (Cfg.mapState_eq_of_fields _ e _ …).symm`, the five field goals by `Cfg.init_*` | `Turing.Cfg.mapState_eq_of_fields` (CfgFacts 69) | finding 3 closed; the five-line `Cfg.ext`/`Cfg.mapState_*` block is gone |

The other RN-1 and F2 sites cite `CfgFacts`: `nf_retag` (999,
`Cfg.mapState_const_eq_mapState_sigma`), `nf_tagged_ne_park` (1005,
`Cfg.mapState_sigma_state_ne`), `nf_tag` (1301, `Cfg.mapState_eq_of_fields`), `nf_stream_length`
(2332, `length_flatMap_uniform`), `Cfg.inputSymbol_congr` (1474, 1670). `nf_entry` (1290) cites
`bufferTape_eq_none_of_not_mem` (the `4354cbeb` re-point). The remaining `Cfg.mapState_*` uses
(74–80, 2389, 2396, 2601, 2690, 2765) read one field each; none is a renaming block. **No RN-1
member is left in NF.**

## Buffer and list hits: dispositions

| Line (repaired) | Declaration | Text | Disposition |
|---|---|---|---|
| 1045 | `nf_aReturn` | `bufferTape_eq_none_of_not_mem` | citation (above) |
| 1153 | `nf_bClear` | `bufferTape_drop` | citation (above) |
| 1290 | `nf_entry` | `bufferTape_eq_none_of_not_mem` | citation |
| 2300 | `nf_region` (`p = -1`) | `FinTM.bufferTape_left` | published equation (Simulation 644); idiom |
| 2305 | `nf_region` (`p = L`) | `bufferTape_eq_none_of_not_mem` | citation (above) |
| 2313 | `nf_region` (`p = m < L`) | `FinTM.bufferTape_nat, List.getElem?_ofFn` | the buffer of `List.ofFn …` read inside the word by the published equation and a core lemma; no `BufferWords` identity covers `ofFn` words; idiom |
| 2432 | `nf_V_tail` | `rw [hA, hA0, zero_add, FinTM.bufferTape_nat]` | converts the stream `bufferTape s p` to `s[p]?` to meet `nf_leaf_run_wk`'s list-lookup hypothesis; published equation; idiom |
| 2717 | `nf_V_char` | same, for `nf_leaf_run_in` | idiom |
| 239 | `nf_display_flag` | `List.getElem?_eq_getElem` | core, on the display list; idiom |
| 285 | `nf_display_firstStop` | `getLastD_eq_getLast?, getLast?_eq_getElem?, length_take, getElem?_take_of_lt` | last bit of a prefix of the display, by core list lemmas (core's `List.getLast?_take`, `Init/Data/List/Nat/TakeDrop.lean` 77, is an equal-length alternative); not a TCSlib lemma; idiom |
| 338–340 | `nf_firstStop_records` | the same chain, and `getElem?_eq_getElem` | idiom |
| 1595–1596, 1601 | `nf_stream_cons` | `getElem?_append_left` / `getElem?_append_right` on `List.ofFn rec ++ rs.flatMap List.ofFn` | **append indexing by hand, at the list level.** It is the list-lookup analogue of `FinTM.bufferTape_append_shift`/`_append_mid` (BufferWords 47/58), but its interface is `T (h + p) = l[p]?` for `p < |l|`, not `bufferTape`, so those lemmas do not apply; each conjunct is one core lemma. Idiom, not a re-derivation |
| 2893 | `nf_split` | `List.getElem?_eq_getElem` | idiom |
| 345, 662, 668, 673, 702, 2942, 2951–2952, 3097, 3103, 3108, 3120, 3124, 3159 | choice-word and stream prefixes | `List.take_length`, `take_zero`, `take_succ_eq_append_getElem`, `take_take`, `take_append_drop` | prefix arithmetic on choice words by core lemmas; idiom |

## Run, halting and first-exit hits: dispositions

| Line | Declaration | Text | Disposition |
|---|---|---|---|
| — | — | `Nat.exists_eq_add_of_le`, `runFrom_of_halt`, `lt_trichotomy` | 0 hits |
| 668 | `nf_sweep_control_prefix` | `List.take_succ_eq_append_getElem hlt, NDTM.runWith_append, NDTM.runWith_cons, NDTM.runWith_nil` | one more choice bit: `runWith (w.take (n+1)) = stepWith w[n] (runWith (w.take n))`. No published `runWith_concat`; the same three-equation composition appears in at least ten files (`Codec/Bridge` 106, `ExpBFS/Radius` 154/266, `ConfigGraph` 292, `NDHost` 358, `BPLInPCount` 116, …). Idiom |
| 2951–2953 | `nf_vrun_of_ok` | same composition | idiom |
| 3099–3103 | `nf_forward` | `Nat.find hex`, `find_spec`, `find_min`, `find_min'` | first halting time of a choice word. The published `MultiTapeTM.exists_first_halt` (Finite 218) is deterministic; no NDTM form exists. NF cont1 review F8 (X10) row candidate, FH-1's kind; gate 95 F9 (1) names the twin in `ExhaustiveReplay` (2179–2189). Not a re-derivation |
| 3123–3124 | `nf_forward`, `hout` | `NDTM.runWith_append w₀ (w.drop t₀)`, `List.take_append_drop`, `NDTM.runWith_of_halt _ hspec` | output after the first halt (gate 93's third sign). The two published forms need **every** branch of the prefix length halted: `Turing.run_take_of_halted` (ChoiceWords 107, `hall`) and `Turing.FinNDTM.runWith_eq_runWith_take` (Randomized/PTM 148, `HaltsWithin`). NF has one branch's halt (`hspec`), so neither applies, and neither module is in NF's import closure (30 modules); their proofs' inner step is these two lines. No single-branch public form; F8/F9 row candidate. Not a re-derivation |
| 3230 | headline docstring | `Turing.NDTM.runWith_of_halt` | text |
| 3208–3218 | `nf_backward_host` | `segment_iff`, `Segment.time_eq` | first-exit uniqueness through the published lemma (gate 93's first sign); citation |

### `runFrom_add` (34 lines)

- **21 endpoint compositions** (1091, 1231, 1233, 1723, 1739, 2174, 2226, 2241, 2270, 2274, 2544,
  2548, 2562, 2577, 2580, 2763, 2821, 2828, 2831, 2843, 2846): `runFrom c (T₁ + T₂)` rewritten
  through the phase or record endpoints. This is the published `MultiTapeTM.runFrom_add` itself
  (the first component of `Segment.trans`); idiom.
- **13 lines inside the time splits** (1110, 1261, 1266, 1719, 2145, 2232, 2236, 2567, 2571, 2575,
  2749, 2837, 2841): disposed below.

## Finding 5 (3): the time splits, one disposition each

Shape: `by_cases hu1 : u ≤ T₁` (or `<`), then `obtain ⟨v, rfl⟩ : ∃ v, u = (T₁ + 1) + v :=
⟨u - (T₁ + 1), by omega⟩` and `rw [MultiTapeTM.runFrom_add, <endpoint>]`, carrying a "no verdict"
or "no exit" guard across a window boundary. The closest published form is the second component
of `Turing.Segment.trans` (Contract/Basic 460, "no state in `F` before `t + v`"); `SafeRun.trans`
(EmitIterEmbed 94) avoids one state only and is not in NF's import closure. Neither is cited because NF's
windows are not `Segment`-typed: the phase windows come from `phaseHostTM_run`/`_run_le` as
pointwise run equations (`∀ u ≤ T, host.runFrom … u = (phase.runFrom c u).mapState …`), and the
leaf windows from `nf_leaf_record_in`/`_wk`/`nf_leaf_block`/`nf_leaf_run_in`/`_wk` as guards
`∀ u < T, ∀ s, state = some s → nf_leafExit N s = none` with an existential `T`. Citing
`Segment.trans` would mean restating each window as `Segment V F (fun _ => True)` (with `F` the two
park states, or the exit states) and converting the guard forms, at about the cost of each split.
I agree with the auditor's reading: **idiom, not a re-derivation**.

| # | Landed line (finding 5) | Repaired line | Declaration | Machine and windows | Guard carried | Disposition |
|---|---|---|---|---|---|---|
| 1 | 1107 | 1108 (`runFrom_add` 1110) | `nf_aReturn` | phase host `nf_V`: `aFwd j` (`hpA`, `u ≤ 1`) → redirect → `aBack j` (`hpB`) | no `⟨.park, b⟩` before `\|s\| + 6` | idiom (phase windows) |
| 2 | 1263 (+ nested 1269) | 1259, nested 1265 (`runFrom_add` 1261, 1266) | `nf_bClear` | phase host: `bFwd j` → `bBack j` → `bClr j` (`hpA`, `hpB`, `hpC`) | no park before the three phases' total | idiom (phase windows) |
| 3 | 1722 | 1718 (1719) | `nf_leaf_run_in` | one machine, `nf_leaf N none`: a record (`2k + 4` steps, `hpre`) then the recursive tail (`hpre'`) | no leaf exit before `2k + 4 + T'` | idiom; **not across a phase redirect** (finding 5's wording) but across a record boundary of one machine |
| 4 | 2148 | 2144 (2145) | `nf_leaf_run_wk` (`hpre2`) | one machine, `nf_leaf N (some t)`: record (`hpreR`) then block (`hpreB`, 2 steps) | no leaf exit before `2k + 4 + 2` | idiom; one machine, record/block boundary |
| 5 | 2235 | 2231 (2232) | `nf_leaf_run_wk` (cons case) | record (`hpreR`) then block (`hpre4`, 4 steps) | no leaf exit before `2k + 4 + 4` | idiom; one machine |
| 6 | 2238 | 2234 (2236) | `nf_leaf_run_wk` (cons case) | block end (`hrun4`) then recursive tail (`hpre'`) | no leaf exit before `2k + 4 + 4 + T'` | idiom; one machine |
| 7 | 2568 (+ nested 2572, 2576) | 2566, nested 2570, 2574 (2567, 2571, 2575) | `nf_V_tail` | phase host: replay `rep (some t)` (`hwin₁`) → `aReturn` (`h3win`) → `bClear` (`h5win`) → recursive tail (`hf2`) | no park before the total | idiom (phase windows) |
| 8 | 2750 | 2748 (2749) | `nf_V_char` (`hwin01`) | phase host: control sweep (`hwin0`) → replay `rep none` (`hwin1`) | no park before `2\|s\| + 3 + T₁` | idiom (phase windows) |
| 9 | 2837 (+ nested 2842) | 2835, nested 2840 (2837, 2841) | `nf_V_char` | phase host: [sweep + replay] (`hwin01`) → `aReturn` (`h3win`) → tail (`hf2`) | no park before the total | idiom (phase windows) |

The finding lists nine sites; the file has 13 split lines, the four nested ones (repaired 1265,
2570, 2574, 2840) sitting inside sites 2, 7 and 9. Sites 3–6 are inside one leaf machine, not
across a phase redirect.

## Finding 3: the eleven `Cfg.ext` blocks, one disposition each

None of the eleven blocks mentions `mapState` (script check over each block's text), so none is
RN-1's kind (`Cfg.mapState_eq_of_fields` covers renamings only). Each compares a configuration
given by a published step or run lemma (`scanTM_run_ofCfg`, `step_of_tapeAction_move`, the
`guessRunCfg_*`/`streamStartCfg_*`/`Cfg.init_*` field equations) with a stated record update, field
by field (`Function.update` head arithmetic, `moveInputPos_zero`). No published lemma states these
endpoints.

| # | Landed | Repaired | Declaration | Equation compared | Disposition |
|---|---|---|---|---|---|
| 1 | 571 | 571 | `nf_sweep_run` | `scanTM_run_ofCfg`'s endpoint (`scanResult_fold`) = `streamStartCfg x 0 (.done …) s` | configuration-record equation; idiom |
| 2 | 1283 | 1279 | `nf_entry` | `guessRunCfg (P.initCfg x) 0 s q = streamStartCfg x 0 q s` | record equation through published field equations; the public `guessRunCfg_clean` (NDHost 1513) is the embedded form (capture tape, `embedSilentCfg`) and does not state this one; idiom |
| 3 | 1364 | 1360 | `nf_leaf_prefix`, `m = 0` | `runFrom d 0` = the record update at `m = 0` | idiom (leaf-run endpoint) |
| 4 | 1390 | 1386 | `nf_leaf_prefix`, `m + 1` | one `step_of_tapeAction_move` step = the update at `m + 1` | idiom (leaf-run endpoint) |
| 5 | 1485 | 1481 | `nf_leaf_record_in` | the record's last-bit step | idiom (leaf-run endpoint) |
| 6 | 1728 | 1724 | `nf_leaf_run_in` | record then tail endpoint | idiom (leaf-run endpoint) |
| 7 | 1851 | 1847 | `nf_leaf_block`, last record | block step endpoint | idiom (leaf-run endpoint) |
| 8 | 1899 | 1895 | `nf_leaf_block`, next record (`h4`) | the two head adjustments | idiom (leaf-run endpoint) |
| 9 | 1961 | 1957 | `nf_leaf_record_wk` | step into the block | idiom (leaf-run endpoint) |
| 10 | 2179 | 2175 | `nf_leaf_run_wk`, `nil` | endpoint | idiom (leaf-run endpoint) |
| 11 | 2246 | 2242 | `nf_leaf_run_wk`, `cons` | endpoint (`Function.update_idem`) | idiom (leaf-run endpoint) |

This matches the auditor's classification (`nf_sweep_run`, `nf_entry` and nine leaf-run
endpoints). The twelfth landed block (`nf_pack`, 64) is gone (finding 3).

## Result

- **No hit at the repaired head is a re-derivation of a published lemma.** Finding 1's three sites
  cite `FinTM.bufferTape_drop` / `FinTM.bufferTape_eq_none_of_not_mem`, and `nf_pack` cites
  `Cfg.mapState_eq_of_fields`; NF has no RN-1 member left.
- Row candidates already on record, unchanged: the NDTM first halt and the output after it in
  `nf_forward` (cont1 review F8, gate 95 F9 (1)). The new observation is that two all-branch public
  forms (`Turing.run_take_of_halted`, `Turing.FinNDTM.runWith_eq_runWith_take`) exist, so a
  single-branch form would be their common core.
- Finding 5 (2) and (3) are answered: `runFrom_add` and hand-indexing patterns are swept, and the
  nine time splits (13 lines) and eleven `Cfg.ext` blocks each have a disposition. A wording
  correction for the records: four of the nine splits are inside one leaf machine, not across a
  phase redirect.
- Raw files: `raw/NDNormalForm-10c01517.lean.txt`, `raw/NDNormalForm-e8994dc1.lean.txt`.
