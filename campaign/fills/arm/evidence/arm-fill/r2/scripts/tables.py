"""Markdown tables of the round-2 classified ledger (evidence file ledger-r2-tables.md).
Reads work/{pairs.tsv, classify.tsv, ledger2-decls.tsv, ledger2-perfile.json, manual.tsv,
families.out, tipspans.out-equivalent (recomputed here from pairs.tsv is not possible), ...}.
The per-family factoring texts and the per-row resolutions are the pack author's (named here,
not derived). usage: python3 -I tables.py <workdir> <out.md>"""
import json, os, sys
wk, dst = sys.argv[1:3]
rows = [l.rstrip('\n').split('\t') for l in open(os.path.join(wk, 'pairs.tsv'), encoding='utf-8')][1:]
cls = {c[0]: c for c in (l.rstrip('\n').split('\t') for l in open(os.path.join(wk, 'classify.tsv'), encoding='utf-8')) if c[0] != 'pid'}
decls = [l.rstrip('\n').split('\t') for l in open(os.path.join(wk, 'ledger2-decls.tsv'), encoding='utf-8')][1:]
pf = json.load(open(os.path.join(wk, 'ledger2-perfile.json')))
man = [l.rstrip('\n').split('\t') for l in open(os.path.join(wk, 'manual.tsv'), encoding='utf-8') if l.strip() and not l.startswith('#')]
TIPLINE = {('TCSlib/Complexity/TuringMachine/Build/Catalog.lean', 'f2_loopDebit_iterate_length'): '6235-6239',
           ('TCSlib/Complexity/TuringMachine/Build/Embed.lean', 'embedThroughHalt'): '750-796'}
sh = lambda p: p.replace('TCSlib/Complexity/', '')
GRP = {'P1': '(1) payback PR, decided', 'P1+': '(1) payback PR, row added by this ledger (to be acknowledged)',
       'A2a': 'ARM-2 (a)', 'A2b': 'ARM-2 (b)', 'X': 'not real duplication'}
OWN = {'P1': 'maintainer; after the B6 hosts (PR #92, open); the PR\'s own full gate',
       'P1+': 'maintainer; after the B6 hosts (PR #92, open); the PR\'s own full gate',
       'A2a': 'the user\'s refactor, coordinated with Hydroxyi before any brief; not scheduled; a PR plus its gate (zone rules)',
       'A2b': 'the user\'s refactor, coordinated with Hydroxyi before any brief; not scheduled; a PR plus its gate (zone rules)'}
U = {
 'arm_decides_space': ('the bank collection and precondition plumbing of `arm_decides`: decider choice, `bankTMMs`, the `PreS`-to-`Pre` case split over all fourteen instruction kinds, `cleanRun_mono (bank_cleanRun …)`, `length_callSegs_le`, the `arm_space` cell arithmetic', 'one decision-bridge core over a step-semantics interface, width and oracle-space bound as parameters (`arm_decides` and `arm_decides_space` its instances)'),
 'marm_dtime': ('the same plumbing: decider choice with the summed constants `cs`, the `PreS` case split, `cleanRun_mono`, the call-segment bound', 'the same bridge core, with the time conclusion from `runFrom_count_eq`'),
 'narm_decides': ('decider choice, the summed constants and the `log_poly_bound` arithmetic of the logarithmic width', 'the nondeterministic bridge as an instance of the core (through `detPart`, ARM-2\'s direction)'),
 'npre_of_npreS': ('the `PreS`-to-`Pre` case split and the call-segment length bound, 87% of its body', 'a public "syntactic precondition gives the bank precondition" lemma factored out of `arm_decides`'),
 'narm_decides_space': ('bank setup (`kD`, the oracle), `arm_space` and the cell arithmetic', 'the bridge core'),
 'narm_decides_poly': ('the reduction of a polynomial value bound to a logarithmic digit width (`log_poly_bound`, `length_bits_le_log`), 90%', 'one width-reduction lemma used by both'),
 'decChain': ('the counted chain induction of the private `arm_increments`, run with `dec`', 'one parameterized chain lemma in `InputAccess`, public'),
 'runFrom_count_eq': ('the windowed tape-code injectivity sub-argument of `coreCode_inj` (cells outside the window are blank; the index shift `(z + B).toNat`)', 'expose that sub-argument of `coreCode_inj` as a lemma and cite it'),
 'spaceUsedWith_le_of_ranges': ('the `Finset.Icc` cardinality bound over visited head positions', 'one ranges lemma over a family of visited positions, with `runFrom` and `runWith` instances'),
 'MReach.trans': ('the run-splitting composition (`run_add`, `Nat.lt_or_ge`), 99%; the library already repeats it in `Parse2`, `ParseCmp`, `DblLang`', 'reachability once over an arbitrary step relation (trans, halt, mono), instantiated per machine model'),
 'MReach.halt': ('the same composition into a halting run, 99%', 'the same reachability kit'),
 'length_lbStep': ('the pair-decoding case split bounding a pair step\'s length by `max |s| 2`; also 163 characters of `length_pair_components_le`', 'one shared pair-step length helper in `PolyTimeBlockLoop`'),
}
G = {
 'G-oracle': 'the oracle-answer lemma of the input bit and length languages at a canonical query restates `QueryReshape`\'s private `drop_bit`: make one public form (in `InputAccess`) and cite it',
 'G-canon': 'the two directions of `QueryReshape`\'s private `drop_canon`: promote it',
 'G-pairidx': 'a `pairEncode` index fact inside `Mult`\'s private `mult_addresses` (and `QueryReshape.comp_suffix_address`): one public index lemma',
 'G-outsum': 'the empty-output sibling of ConfigGraph\'s public `outSummary_eq_accept_iff`, same proof: home it beside its sibling',
 'G-prefix': 'the agree-on-a-prefix strengthening of `QBF.prefixTruth_congr`, same induction: home it in `Formulas/QBF`, the old lemma a corollary',
 'G-rep': 'the unary-scaling closure fact of CookLevin\'s private `clA5Times_native`, same induction: one public closure lemma',
 'G-vword': 'arity-2 and arity-3 copies of `InputAccess.vword_whole₁` (identical proof): one arity-generic lemma in `InputAccess`, with D7',
 'G-tseitin': 're-proves DAGCircuitSat\'s private `eval_tseitinGates_values` inline: export it with D4',
 'G-reachkit': 'twin of `ARMProof.AHalt.mono`: with the reachability kit',
 'G-bits': 'generalizes `Machines/Parse.canon_eq_bits` by the same induction: one lemma, the canonical case a corollary',
 'G-foldr': 'a fourth copy of a list lemma that Hydroxyi\'s `TreeDAG`, `DAGTransform` and `DAGFanin` already hold privately: one public list lemma',
 'G-flatten': 'the equal-length-block index fact of `PSubsetPPolyConfigCircuit`\'s private `getD_flatMap_chunk` (and of `Path.getD_flatMap_rows`, finding 12): one public list lemma',
}
K = {
 'K1': 'Per-machine register kit copied verbatim: the blocks `cpI`, `shI`, `dmI`, `mvI`, their run lemmas `cp_run`, `dm_run`, `sh_run`, and `Bd.toV` with the scoped `regs` macro, in `TQBFARM/Machine`, `SavitchARM/{Machine,Run}`, `ExpBFS/{Machine,Run}`, `PathHardMachine`. Factoring: one block kit (blocks as functions of register names and label maps, run lemmas once) and one register-record tactic.',
 'K2': 'Decider banks and their oracle lemmas restated per machine: the input bank (`TQBFARM/Machine.decs`, `Codec/Run.codecAs`, `PathWalkMachine.pathAs`), the code bank (`SavitchARM/Correct.decs`, `ExpBFS/Main.decs`, `PathHardRegs.As`), and `orc_bit`/`orc_len` in five files and inline in three theorems. Factoring: a public input bank in `InputAccess` and a code bank in `Codec`, each with its oracle lemmas.',
 'K3': 'The decision bridges\' bank-setup and precondition plumbing (`arm_decides_space`, `marm_dtime`, `narm_decides_space`, `npre_of_npreS`, 76–88% shared among themselves and re-deriving `arm_decides`). Factoring: ARM-2\'s single bridge theorem over one step-semantics interface.',
 'K4': 'The `detPart` compile bridge written twice (`NARMCompile` and `MARMCompile`: transition agreement, the overridden start step, the live and halting splices, the box). Factoring: one "compile with overridden states" bridge parameterized by the extra instructions.',
 'K5': 'The one-step `NHalts` argument re-proved inside `NTerm.nhalts` (and the det/choose siblings). Factoring: one one-step lemma over the choice-indexed successor; `NTerm.nhalts` cites it.',
 'K6': 'The four code languages written out separately: the definitions, four identical membership proofs, the canonical-decoding `*Lang_iff` lemmas, the decider proofs (`validLang_mem`, `acceptLang_mem`, `initLang_mem`, and `stepLang_mem` against `one_run`), `PreChk` inside `ValidChk`. Factoring: one parameterized code language with generic membership and decoding lemmas, and one decider lemma.',
 'K7': '`Codec/Layout.layout_run` and `Layout2.layout2_run`, 4,139 shared characters. Factoring: one layout run parameterized by the field layout.',
 'K8': '`Codec/Parse.parse_run` and `parse_run₂` (1,615 shared). Factoring: the common parse phases once.',
 'K9': 'Missing internal citations: `mem_iff_codeChain` re-derives the window argument of `ExpBFS.inWin_runWith_of_decides`; `validChk_iff` re-proves `word_split`. Factoring: cite.',
 'K10': 'MARM loop and step proofs: the counting scans of `ExpBFS/Relax`, `Search` and `Main`; `Run`\'s write loops, the register-clear blocks `d1_run`/`fz_run`/`nz_run`, and the per-instruction step lemmas. Factoring: a generic counted MARM loop, a clear block, and one deterministic-step lemma in `Machines/MARM`.',
 'K11': 'ARM transfer loops: `ARMLoops`\' `move_run`, `move2_run`, `dmove_run`, `sub_run`, `halve_run`, `shl_run` share one induction; `ARMWidthExample.d1_loop`/`d2_loop` re-prove `dmove_run`/`move_run` without importing `ARMLoops` (by inspection). Factoring: one parameterized transfer loop; the example cites `ARMLoops`.',
 'K12': 'Inductive counting: `guloop`/`gvloop` (1,274 shared) and `gwalk_spec` repeating `gwalk_loop`\'s closing argument. Factoring: a generic guess loop; `gwalk_spec` a corollary.',
 'K13': 'PATH walk endpoint comparisons and phases (`ps_tcmp`/`ps_scmp`, `ps_tphase`/`ps_sphase`). Factoring: one endpoint-field comparison parameterized by the field encoding.',
 'K14': 'Savitch recursion tails (`tail0F`/`tail1F`/`tail1T`, and `desc2`\'s inline tail) and stack pushes and pop (`pushU_run`/`pushV_run`/`pop_run`). Factoring: one tail lemma and one push lemma parameterized by the register.',
 'K15': '`PathHardRegs.eq_qk`/`eq_yid`: register-record reconstruction field by field. Factoring: one `toV` extensionality lemma.',
 'K16': '`TQBFARM/Walk.node_run`/`qlook_run`: one copy block inlined twice. Factoring: one labelled block with its run lemma.',
 'K17': 'TQBF hardness: the shared `vwid` bound argument (`vlen_le_vwid`/`configBound_le_two_pow`), the ∀/∃ block duals (`prefixTruth_replicate_all`/`_ex`), `pt_drop`/`pt_take`. Factoring: one bound lemma, one block lemma over the quantifier, one `PrefixByLength` combinator lemma.',
 'K18': 'The reachability kit: `MReach.trans`/`halt` and `MHalt.mono` against `AReach.*` (and the `Parse2`, `ParseCmp`, `DblLang`, `ARMRun` twins), and the same-file `MReach.halt`/`trans`. Factoring: reachability once over an arbitrary step relation (ARM-2 (a)).',
 'K19': '`NARMRun.NGood.mono`/`seg`: the halting-padding key twice. Factoring: one padding lemma, with `narun_append_of_halted`.',
 'K20': '`Codec/Layout.two_pow_bits_le` = `Parse.bitsVal_le_of_width`\'s proof; `SavitchARM.Rel` = `ExpBFS/Relax.stp` (the code-step relation; `Codec.StepRel` exists). Factoring: cite one.',
 'K21': 'The `InputAccess` chain and stride decoders: `incChain`, `decChain`, `decodeStride_loop` (D7). Factoring: one parameterized stride decoder and chain lemma in `InputAccess` (decided).',
}
o = open(dst, 'w', encoding='utf-8')
w = lambda s='': o.write(s + '\n')
w('# ARM fill gate, round 2: the classified duplication ledger (tables)')
w()
w('Generated by `scripts/tables.py` from the round-2 work files; every count is MEASURED by the scripts named in `NOTES.md`; classes, groups, factorings and resolutions are the pack author\'s (rules and overrides in `scripts/classify.py`). Lines are at the received tree `8c23f3bc`, which equals the tip for every added file and for every library file cited here except the two marked (tip lines in brackets). Groups follow the user\'s dedup decisions (backlog §1 ARM-1 and ARM-2 at `e831b5b0`).')
w()
w('Groups: **P1** the payback PR, decided; **P1+** a row this ledger adds to the payback list (copies of campaign code, or riding with D4), to be acknowledged; **A2a** ARM-2 (a), re-derivations of Hydroxyi\'s earlier library; **A2b** ARM-2 (b), duplication inside the new files; **X** not real duplication.')
w()
# library copy-side declarations
lib = {}
for c in rows:
    if c[1] != 'lib': continue
    k = (c[2], c[3]); lib.setdefault(k, []).append(c)
dd = {(d[0], d[1]): d for d in decls}
w('## 1. Copies of existing library material, by copy-side declaration')
w()
w('Classes: D disclosed (D1–D7, by the disclosure table), U undisclosed substantive, G small genuine helper duplication, N incidental. A declaration\'s class is its highest over its pairs; its other pairs are listed with their own classes.')
w()
order = {'D': 0, 'U': 1, 'G': 2, 'N': 3}
def dclass(ps):
    return min((cls[p[0]][2] for p in ps), key=lambda x: order[x])
items = sorted(lib.items(), key=lambda kv: (order[dclass(kv[1])], -max(int(p[13]) for p in kv[1])))
w('| Copy side (file:lines; code lines; body chars) | Class | Family | Group | Source (file:lines; body chars) and shared characters, each pair with its class |')
w('|---|---|---|---|---|')
for (p, n), ps in items:
    c0 = ps[0]; dc = dclass(ps)
    fam = next(cls[x[0]][3] for x in ps if cls[x[0]][2] == dc)
    grp = next(cls[x[0]][4] for x in ps if cls[x[0]][2] == dc)
    srcs = []
    for x in sorted(ps, key=lambda x: -int(x[13])):
        tl = TIPLINE.get((x[7], x[8]))
        srcs.append(f'`{sh(x[7])}:{x[9]}`{" [tip " + tl + "]" if tl else ""} `{x[8]}` ({x[11]}): {x[13]} {cls[x[0]][2]}')
    w(f'| `{sh(p)}:{c0[4]}` `{n}` ({c0[5]}; {c0[6]}) | {dc} | {fam} | {grp} | ' + '; '.join(srcs) + ' |')
w()
w('Manual entries (below the screen\'s 60-character floor or outside its population; kept visible, counted in A4+):')
w()
w('| Class | Copy | Shared (chars) | Group | Basis |')
w('|---|---|---|---|---|')
for m in man:
    w(f'| {m[0]} | `{sh(m[1])}` `{m[2]}` | {m[3]} | {m[4]} | {m[5]} |')
w()
w('## 2. The twelve undisclosed substantive copies')
w()
w('| Copy (file:lines) | Source counterpart (file:lines) | Shared chars | What is shared | Shared contract that removes it | Group |')
w('|---|---|---|---|---|---|')
for (p, n), ps in items:
    if dclass(ps) != 'U': continue
    best = max((x for x in ps if cls[x[0]][2] == 'U'), key=lambda x: int(x[13]))
    g = cls[best[0]][4]
    w(f'| `{sh(p)}:{best[4]}` `{n}` | `{sh(best[7])}:{best[9]}` `{best[8]}` | {best[13]} | {U[n][0]} | {U[n][1]} | {g} |')
w()
w('## 3. Small genuine helper duplication (library side): proposed shared helpers')
w()
w('| Family | Copy-side declarations | Proposed shared helper | Group |')
w('|---|---|---|---|')
gf = {}
for (p, n), ps in items:
    if dclass(ps) != 'G': continue
    f = next(cls[x[0]][3] for x in ps if cls[x[0]][2] == 'G'); gf.setdefault(f, []).append(f'`{sh(p)}` `{n}`')
for f, v in gf.items():
    w(f'| {f} | {"; ".join(v)} | {G[f]} | {next(cls[x[0]][4] for x in rows if x[0] in cls and cls[x[0]][3] == f)} |')
w()
w('## 4. Logical families of the internal and same-file pairs (S/G pairs only)')
w()
w('| Family | Pairs (category class: count) | What is repeated, and the proposed factoring | Group | Owner; window; gate |')
w('|---|---|---|---|---|')
for k in sorted(K, key=lambda s: int(s[1:])):
    ps = [c for c in cls.values() if c[3] == k]
    cnt = {}
    for c in ps: cnt[(c[1], c[2])] = cnt.get((c[1], c[2]), 0) + 1
    grps = sorted({c[4] for c in ps})
    w(f'| {k} | ' + ', '.join(f'{a} {b}: {v}' for (a, b), v in sorted(cnt.items())) + f' | {K[k]} | {"/".join(grps)} | {OWN[grps[0]]} |')
w()
w('## 5. Round 1\'s 45 internal components and the 61 same-file components')
w()
w('From `families.txt` (members, pair counts S/G/N, family class, representative pair, logical family):')
w()
fo = open(os.path.join(wk, 'families.out'), encoding='utf-8').read().split('\n')
for line in fo:
    if line.startswith('## Logical'): break
    if line.startswith('## '): w('### ' + line[3:]); w(); w('| id | members | pairs (S/G/N) | family class | representative pair | logical family |'); w('|---|---|---|---|---|---|'); continue
    if line.startswith('id |') or not line.strip(): continue
    parts = line.split(' | ')
    w('| ' + ' | '.join(parts) + ' |')
    if False: pass
w()
w('## 6. Per-file totals (A1 round 1; A3 classified, cross-file; A4 classified, same-file included; A4+ with the manual entries)')
w()
w('Each cell: whole-body characters % / whole-body code lines % / shared-text characters % / shared-text code lines % (prorated). Bold: past one fifth.')
w()
w('| File (body chars; code lines) | A1 | A3 | A4 | A4+ |')
w('|---|---|---|---|---|')
for p in sorted(pf['A1']):
    r = [pf[a][p] for a in ('A1', 'A3', 'A4', 'A4+')]
    if not any(x['n'] for x in r): continue
    f = lambda v: f'**{v:.1%}**' if v > 0.2 else f'{v:.1%}'
    w(f'| `{sh(p)}` ({r[0]["chars"]}; {r[0]["code"]}) | ' + ' | '.join(f'{f(x["pwc"])} / {f(x["pwl"])} / {f(x["psc"])} / {f(x["psl"])}' for x in r) + ' |')
w()
w('## 7. The ledger rows in A4+ (every counted declaration, with its class and group)')
w()
w('| Declaration | Lines | Code lines | Body chars | Shared chars | Class | Group |')
w('|---|---|---|---|---|---|---|')
for d in decls:
    w(f'| `{sh(d[0])}` `{d[1]}` | {d[2]} | {d[3]} | {d[4]} | {d[5]} | {d[6]} | {d[7]} |')
print('tables written')
