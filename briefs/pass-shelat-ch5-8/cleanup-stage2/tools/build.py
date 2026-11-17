"""Build the cleanup Stage 2 scope (static: git objects, python3 -I). Writes scope.tsv and summary json."""
import csv, json, re, sys, collections, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from reloc import TIP, src, mapline, enclosing, find_decl, DECL

S = sys.argv[1]           # scratchpad
OUT = sys.argv[2]         # output dir
REC = '/home/user/tcslib/briefs/pass-shelat-ch5-8'
CHECKBASE = '01cc6259480ccc9372181cd4d18d4511c87aa048'   # Stage 1 check tree (repoint.tsv, addendum lines)
INVBASE = 'f472accd5e000a53d0fbe02b5414435429ce4a70'     # DW-10 issue base (= PS10 base b76f804b in Lean)
PS10BASE = 'b76f804b4615123e6084a00d23fd9e6ff88fac92'

items = []


def add(**kw):
    d = dict(id='', source='', owner_file='', tip_line='', declaration='', kind='', statement_change='no',
             freeze_ref='-', depends_on='-', est_lines=0, job='', target='-', notes='-')
    d.update(kw)
    items.append(d)


def full(p):
    p = p.strip()
    return p if p.startswith('TCSlib/') else 'TCSlib/Cryptography/' + p


def parse_locs(s):
    """'a.lean:1, :2; b.lean:3' -> [(path,[lines])]"""
    out = []
    for part in re.split(r';\s*', s):
        part = part.strip()
        m = re.match(r'(\S+\.lean)((?::\d+(?:-\d+)?(?:,\s*:\d+(?:-\d+)?)*)?)', part)
        if not m:
            continue
        path = full(m[1])
        lines = [int(x.split('-')[0]) for x in re.findall(r':(\d+(?:-\d+)?)', m[2])]
        out.append((path, lines))
    return out


def decl_extent(rev, path, L):
    s = src(rev, path)
    if not s or L is None:
        return 0
    i = L
    while i < len(s):
        t = s[i]
        if DECL.match(t) or t.startswith('/--') or t.startswith('/-!') or t.startswith('end ') or t.startswith('section') or t.startswith('namespace'):
            break
        i += 1
    return i - L + 1


def kind_of_decl(rev, path, L):
    s = src(rev, path)
    if not s or L is None:
        return None, False
    m = DECL.match(s[L - 1])
    if not m:
        return None, False
    return m[1], 'private' in s[L - 1].split(m[1])[0]


# ---------------------------------------------------------------- 1. Stage 1 re-point table + addendum
JOBMAP = {}  # path prefix -> job, filled later by assign()

rp = list(csv.reader(open(f'{S}/s1/repoint.tsv'), delimiter='\t'))[1:]
ad = list(csv.reader(open(f'{REC}/cleanup-stage1/final-r1/stage2-addendum.tsv'), delimiter='\t'))[1:]

DL_OF = [  # (regex on row text, DL id)
    (r'IterateFind', 'DW-9/DW-5'), (r'S1-0[4]|expect_simulate_abs|freshImpl|tapeImpl|ovr', 'DL-40'),
    (r'extTape', 'DL-40/DL-59'), (r'length_le_length_encodeLog|zipWith|recBits|eval_toOracleAdversary', 'DL-40'),
    (r'ofFn_blocks_symm', 'DL-35'), (r'expect_sample_eq_uexp|FromDiscreteLog copies', 'DL-41'),
    (r'decide_fnForge', 'DL-44'), (r'splitBits', 'DL-41/DL-44'), (r'cost_zero', 'DL-42'),
    (r'encodeMsgs|msgAt|pairSndD|DL-49|appendCoins|flatMap_range|iterSnd|zeros_poly|padTo|ofFn_padFin', 'DL-49'),
    (r'encodeList_eq_flatMap', 'DL-46'), (r'headD|getD|NextBit', 'DL-47'), (r'length_ofFn_coins|NUPPT.length', 'DL-48'),
    (r'signedPredictor|splitLen', 'DL-48'), (r'foldr_pairEncode_nil|blk', 'DL-45'),
    (r'statClose', 'DL-51'), (r'FinDist|tupleEquiv|mixture|bitsTo', 'DL-39'), (r'DL-43', 'DL-43'),
    (r'ext_of_fields', 'DL-42'), (r'DL-52', 'DL-52'),
]


def dl_for(text):
    for rx, d in DL_OF:
        if re.search(rx, text):
            return d
    return '?'


n = 0
for row in rp:
    loc, what, to, srcn = row
    if 'later window' in to or 'forbidden now' in loc:
        continue  # GSW/Complexity copies: out of Stage 2 (CS1-Q12, GSW out of scope)
    dl = 'DL-49' if 'ComposeSecurity' in loc else dl_for(what + ' ' + to + ' ' + loc)
    for path, lines in parse_locs(loc):
        base = INVBASE if 'IterateFind.lean' in path and 'issue-base' in what else CHECKBASE
        if 'IterateFind.lean' in path:
            base = 'daa6e173cdd94cad1475b9a96eca613bce53ba61'  # repoint.tsv gives IterateFind lines at the issue base daa6e173 (= #347 head = tip for this file)
        tl = [mapline(base, path, L) for L in lines]
        enc = [enclosing(TIP, path, L) for L in tl if L]
        decl = ','.join(sorted({e[0] for e in enc if e})) if enc else ''
        dk, priv = (None, False)
        if tl and tl[0]:
            dk, priv = kind_of_decl(TIP, path, tl[0])
        txt = what + ' ' + to
        if 'IterateFindHost' in path:
            kind = 'delete'
        elif 'lamport_codec_ext' in what and 'Lamport.lean' in path:
            kind = 'delete'
        elif 'move' in txt and 'ext_of_fields' in txt:
            kind = 'promote'  # verbatim move (CS1-Q3)
        elif 'added to Games/Probability' in to:
            kind = 're-point'
        elif dk in ('def', 'abbrev', 'structure') and not priv:
            kind = 're-point (definition body)'
        elif priv or 'delete' in to or 'unused' in what:
            kind = 'delete'
        else:
            kind = 're-point'
        sc = 'body (definitional)' if kind == 're-point (definition body)' else 'no'
        n += 1
        add(id=f'S2-RP-{n:03d}', source=f'{dl}; repoint.tsv ({srcn})', owner_file=path,
            tip_line=','.join(str(x) if x else '?' for x in tl), declaration=decl or what[:60], kind=kind,
            statement_change=sc, freeze_ref='Q-DEF (proposed)' if sc != 'no' else '-',
            est_lines=(decl_extent(TIP, path, tl[0]) + 2 if kind == 'delete' and tl and tl[0] else 4 * max(1, len(lines))),
            target=to[:160], notes=what[:160])

for row in ad:
    loc, what, to, srcn = row
    if to.startswith('none') or to.startswith('no Stage 2 row') or 'optional re-derivation' in to:
        continue  # CS1-Q10 notes / DL-53 deferred / optional: listed in the plan, no work item
    if 'DL-55' in what or 'DL-56' in what:
        continue  # expanded below with the ledger rows
    if 'the seven approved DL-35 changes' in what or 'EnsembleLemmas.blocks -> FunFamily.blocks' in to or 'CS1-F04' in srcn:
        continue  # expanded below (the fourteen)
    dl = 'DL-49' if ('msgAt' in what or 'encodeMsgs' in what or 'emitLoop' in what or 'henc' in what) else ('DL-40/DL-44' if 'prfAdv' in what else '?')
    for path, lines in parse_locs(loc):
        tl = [mapline(CHECKBASE, path, L) for L in lines]
        enc = [enclosing(TIP, path, L) for L in tl if L]
        decl = ','.join(sorted({e[0] for e in enc if e}))
        dk, priv = kind_of_decl(TIP, path, tl[0]) if tl and tl[0] else (None, False)
        kind = 'delete' if priv else 're-point'
        n += 1
        add(id=f'S2-RP-{n:03d}', source=f'{dl}; stage2-addendum.tsv ({srcn.split(" ")[0]})', owner_file=path,
            tip_line=','.join(str(x) if x else '?' for x in tl), declaration=decl, kind=kind,
            est_lines=(decl_extent(TIP, path, tl[0]) + 2 if kind == 'delete' else 4 * len(lines)), target=to[:160], notes=what[:160])

# ---------------------------------------------------------------- 2. the fourteen DL-35 blocks changes + alias removal
FOURTEEN = [
    ('CS1-Q2 #1', 'Asymptotic/EnsemblesLemmas.lean', 815, 'statement', 'EnsembleLemmas.exists_copiesRed'),
    ('CS1-Q2 #2', 'Asymptotic/EnsemblesLemmas.lean', 433, 'statement', 'EnsembleLemmas.ofFn_blocks_symm'),
    ('CS1-Q2 #3', 'Asymptotic/EnsemblesLemmas.lean', 427, 'statement', 'EnsembleLemmas.take_drop_ofFn_blocks'),
    ('CS1-Q2 #4', 'ZeroKnowledge/CommitmentLemmas.lean', 486, 'statement', 'CommitmentLemmas.ComLoop.emit_init_of_lt'),
    ('CS1-Q2 #5', 'Encryption/PrivateKey/OracleFromPRF/Handler.lean', 139, 'body', 'PRFGame.pkTapes'),
    ('CS1-Q2 #6', 'Asymptotic/Ensembles.lean', 223, 'body', 'Ensemble.copies'),
    ('CS1-Q2 #7 (seventh)', 'Encryption/PrivateKey/EncryptThenTag/Handler.lean', 178, 'body', 'ETTGame.dTape'),
    ('S1-final Q2 #8', 'Encryption/PrivateKey/EncryptThenTag/CPAHandler.lean', 180, 'body', 'bTapeOf'),
    ('S1-final Q2 #9', 'Encryption/PrivateKey/EncryptThenTag/CPAReduction.lean', 90, 'body', 'bTapes'),
    ('S1-final Q2 #10', 'Encryption/PrivateKey/EncryptThenTag/Reduction.lean', 89, 'body', 'dTapes'),
    ('S1-final Q2 #11', 'Encryption/PrivateKey/EncryptThenTag/CPAHandler.lean', 185, 'statement', 'bTapeOf_eq'),
    ('S1-final Q2 #12', 'Encryption/PrivateKey/EncryptThenTag/CPAReduction.lean', 94, 'statement', 'bTapes_eq'),
    ('S1-final Q2 #13', 'Encryption/PrivateKey/EncryptThenTag/Reduction.lean', 93, 'statement', 'dTapes_eq'),
    ('S1-final Q2 #14', 'Encryption/PrivateKey/EncryptThenTag/Handler.lean', 183, 'statement', 'dTape_eq'),
]
for i, (ref, p, L, what, name) in enumerate(FOURTEEN, 1):
    path = full(p)
    tl = find_decl(TIP, path, name) or mapline(CHECKBASE, path, L)
    add(id=f'S2-BK-{i:02d}', source=f'DL-35; {ref}', owner_file=path, tip_line=str(tl), declaration=name,
        kind='alias change', statement_change=what + ' (EnsembleLemmas.blocks / private blocks -> FunFamily.blocks, definitional)',
        freeze_ref=ref, est_lines=4, target='FunFamily.blocks', notes=f'{what} of {name}; gate checks each (CS1-Q2, Stage 1 final Q2)')
PROOF_USES = [('Asymptotic/Ensembles.lean', [514, 550, 551, 552]), ('Encryption/PrivateKey/OracleFromPRF/Handler.lean', [150, 160]),
              ('Asymptotic/EnsemblesLemmas.lean', [835, 850]), ('Encryption/PrivateKey/EncryptThenTag/CPAReduction.lean', [352]),
              ('Encryption/PrivateKey/EncryptThenTag/Reduction.lean', [327]), ('ZeroKnowledge/ThreeColoring/ColRepSound.lean', [184, 187])]
k = 14
for p, Ls in PROOF_USES:
    path = full(p)
    tl = [mapline(CHECKBASE, path, L) for L in Ls]
    k += 1
    add(id=f'S2-BK-{k:02d}', source='DL-35; proof uses (Stage 1 handover 1, CS1-F04)', owner_file=path,
        tip_line=','.join(map(str, tl)), declaration=','.join(sorted({enclosing(TIP, path, x)[0] for x in tl if x and enclosing(TIP, path, x)})),
        kind='re-point', est_lines=2 * len(Ls), target='FunFamily.blocks, FunFamily.blocks_apply', notes='proof/docstring uses of the aliases')
for p, Ls, names in [('Asymptotic/Ensembles.lean', [214, 218], 'private blocks, blocks_eq'),
                     ('Asymptotic/EnsemblesLemmas.lean', [400, 404, 407, 413], 'EnsembleLemmas.blocks, blocks_eq, blocks_apply, blocks_symm_apply (public; decls2 REMOVED, approved CS1-Q2)')]:
    path = full(p)
    tl = [mapline(CHECKBASE, path, L) for L in Ls]
    k += 1
    add(id=f'S2-BK-{k:02d}', source='DL-35 / DL-9 / DL-38 B3; CS1-Q2', owner_file=path, tip_line=','.join(map(str, tl)),
        declaration=names, kind='delete', statement_change='removal (public alias)' if 'public' in names else 'no',
        freeze_ref='CS1-Q2' if 'public' in names else '-', depends_on='S2-BK-01..' + f'{k-1:02d}',
        est_lines=sum(decl_extent(TIP, path, x) for x in tl if x) + 4, notes='alias removal after the fourteen')

# ---------------------------------------------------------------- 3. ledger rows not in the tables
LEDGER = [
    # (src, path, decl, kind, stmt, target, note, est)
    ('DL-55', 'Encryption/PublicKey/TrapdoorPredictor.lean', 'decide_singleton_eq_true', 'promote', 'move (verbatim, new low-level home; name per brief)', 'Foundations/BitLists.lean (in both closures; same full name, so a verbatim move in one change)', 'verbatim move TrapdoorPredictor -> Foundations/BitLists (REMOVED/ADDED pair, CS1-Q3 precedent)', 10),
    ('DL-55', 'Pairing/Assumptions.lean', 'bdhAssumption_of_dbdhAssumption', 're-point', 'no', 'promoted decide_singleton_eq_true', 'T1 inline verdict identity (Gate 44 G44-01)', 4),
    ('DL-56', 'AdvancedEncryption/IdentityBased/BonehBoyenMachine/Words.lean', 'poly_rU', 're-point', 'no', 'Games.polyTimeComputable_rU', 'reader in Games/Efficiency if the recorded obstruction needs one', 6),
    ('DL-56', 'AdvancedEncryption/IdentityBased/BonehBoyenMachine/Words.lean', 'poly_rZ', 're-point', 'no', 'Games.polyTimeComputable_rZ', '-', 6),
    ('DL-56', 'AdvancedEncryption/IdentityBased/BonehBoyenMachine/Words.lean', 'poly_rW', 're-point', 'no', 'Games.polyTimeComputable_rW', '-', 6),
    ('DL-56', 'AdvancedEncryption/IdentityBased/BonehBoyenMachine/Words.lean', 'poly_rS', 're-point', 'no', 'Games.polyTimeComputable_rS', '-', 6),
    ('DL-57', 'AdvancedEncryption/IdentityBased/Defs.lean', 'IBEScheme (new sidSpec_dom_*/sidSpec_rng_*/zeroBits_eq_cast)', 'promote', 'no (additive)', 'IBEScheme.*', 'promote the scheme-generic facts (bb1-sim fill ruling Q1)', 40),
    ('DL-57', 'AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Lazy.lean', 'sidSpec_rng_one', 're-point', 'no', 'IBEScheme.sidSpec_rng_one', 'bb1-sim fill copies (sidSpec_dom_*, sidSpec_rng_*, zeroBits_eq_cast): locate exact homes in the brief', 20),
    ('DL-57', 'AdvancedEncryption/IdentityBased/BonehBoyenMachine/Oracles.lean', "sidSpec_rng_one'", 'delete', 'no', "IBEScheme.sidSpec_rng_one", "T4 private sidSpec_rng_one', sidSpec_rng_two'", 16),
    ('DL-59', 'Games/Tapes.lean', 'extTape, extTape_of_lt, extTape_of_not_lt, extTape_update', 'promote', 'statement (universe generalisation Type -> Type*)', 'Games.extTape at Type*', 'one family in Games/Tapes (DL-59); new public API of #355 restated', 8),
    ('DL-59', 'Pseudorandom/Functions/LazySampling.lean', 'extendStream, extendStream_def, extendStream_update_of_ne, extendStream_update_self', 're-point (definition body)', 'body (definitional) + new import Games.Tapes', 'Games.extTape', 'Garg-adopted file; alias kept only if an out-of-campaign consumer needs it', 16),
    ('DL-60 B3', 'ZeroKnowledge/EncodingMachines.lean', 'padTo family (S1-27)', 're-point', 'no (proof-only; state through List.takeD only if body change approved)', 'List.takeD / takeD_length / takeD_eq_take / takeD_left\'', 'B3 with DL-53', 20),
    ('DL-60 B4', 'ZeroKnowledge/Interaction.lean', 'Strategy.pairFstD_encodeMsgs', 're-point', 'no', 'Strategy.msgAt_encodeMsgs (S1-26) at i = 0', 'B4 with DL-49', 4),
    ('DL-60 B4', 'ZeroKnowledge/GraphIsomorphism/EfficiencyRep.lean', 'pairSndD_encodeMsgs', 're-point', 'no', 'S1-20 Strategy.iterate_pairSndD_encodeMsgs at i = 1', 'B4 with DL-49 (GI.pairSndD_encodeMsgs)', 4),
    ('DL-40', 'Encryption/PrivateKey/EncryptThenTag/Forgery.lean', 'abs_expect_sub_le_expect', 'delete', 'no', 'ProbComp.abs_expect_sub_le_expect (Games/Probability, #351)', 'the ETT averaging-bound copy (cleanup-stages Stage 2 line)', 18),
    ('DL-43', 'Games/Probability.lean', 'ProbComp.mul_prob_le_expect (new)', 'promote', 'no (additive exception, CS1-Q9)', 'new', 'header pinned in the Stage 1 brief handover 2', 14),
    ('DL-43', 'Authentication/Signatures/Lamport/Planted.lean', 'signatureBlock', 're-point (definition body)', 'body (definitional)', 'FunFamily.blocks n n σ i (blocks_apply)', 'LamportFill.signatureBlock (DL-9 class); locate exact home in the brief', 6),
    ('DL-42', 'Authentication/Signatures/HashAndSign/CodecReaders.lean', 'splitBits_pad_concat', 're-point', 'no', 'Games.padFin_append_split', 'corollary re-derived', 6),
    ('DL-42', 'Authentication/Signatures/Lamport.lean', 'lamport_forgerCodec', 're-point', 'no', 'PRFMAC.forgerCodec_eq_bitCodec form / Games/Machines codec fact', 'fold once both units landed (they have)', 6),
    ('DL-46', 'Encryption/PrivateKey/FromPRF/ReductionMachine.lean', 'adviceBound', 'delete', 'removal (unused public def, frozen-file exception DL-46)', '-', 'DL-46: remove unused frozen items', 6),
    ('DL-38', 'Encryption/PublicKey/AdaptiveCPA/Handler.lean', 'acHandler_impl_forward', 're-point', 'no', 'InteractiveHandler.impl_of_query', 'opportunistic fold', 8),
    ('DL-38', 'Encryption/PrivateKey/OracleFromPRF/Handler.lean', 'pkHandler_finish', 're-point', 'no', 'InteractiveHandler.finish_of_ret', 'opportunistic fold', 8),
    ('DL-38', 'Encryption/PrivateKey/OracleFromPRF.lean', 'local have (= polyTimeComputable_ansRead)', 're-point', 'no', 'Games.polyTimeComputable_ansRead', 'opportunistic fold; locate in brief', 4),
    ('DL-38', 'NumberTheory/Primality.lean', 'ofFn_chunk', 'delete', 'no', 'FunFamily.ofFn_blocks', 'corollary', 8),
    ('DL-38', 'ZeroKnowledge/ThreeColoring/ColRepSound.lean', 'drop_take_ofFn_blockRead', 're-point', 'no', 'FunFamily.ofFn_blocks', 'corollary', 6),
    ('DL-38', 'Candidates/Factoring.lean', 'fac_ofFn_halves', 'delete', 'no', 'FunFamily.ofFn_blocks / OneWay ofFn_block_eq_take_drop', 'corollary (DL-23 overlap)', 10),
    ('Stage 2 nits', 'SecureComputation/Yao/HybridProof/BobIO.lean', 'outputBit_layout', 're-point', 'no', '-', 'unnecessary simpa (linter warning, Gate 42 pack-r2 §148); also a DL-47 getD chain', 2),
    ('Stage 2 nits (CS1-C1-F10)', 'Games/Tapes.lean', 'module docstring', 'citation fix', 'no', '-', 'add freshImpl_apply, tapeImpl_apply to ## Main results', 2),
]
k = 0
for srcn, p, name, kind, stmt, to, note, est in LEDGER:
    path = full(p)
    L = find_decl(TIP, path, name.split(',')[0].split(' ')[0].split('(')[0].replace("'", "'")) if name[0].isalpha() else None
    k += 1
    add(id=f'S2-DL-{k:02d}', source=srcn, owner_file=path, tip_line=str(L) if L else '?', declaration=name, kind=kind,
        statement_change=stmt, freeze_ref=('Q-DEF (proposed)' if 'body' in stmt else ('DL-59 (proposed Q)' if 'universe' in stmt else ('DL-46' if 'removal' in stmt else '-'))),
        est_lines=est, target=to, notes=note)

# ---------------------------------------------------------------- 4. DW-9 host lemmas (Q9)
for name in ['host_dispatch', 'host_branch', 'host_halt']:
    pass  # covered by the IterateFindHost repoint row (delete) and DW-10 STATEMENT rows NEW:9..11

# ---------------------------------------------------------------- 5. DW-10 readers and seal items
rd = list(csv.DictReader(open(f'{REC}/cleanup-dw10/final-r1/stage2-readers.tsv'), delimiter='\t'))
reader_id = {}
for i, r in enumerate(rd, 1):
    rid = f'S2-RD-{i:02d}'
    for it in r['item_ids'].split(','):
        reader_id.setdefault(it.strip(), []).append(rid)
    home = r['home']
    w6 = r['w6_dependent'] == 'yes'
    add(id=rid, source='DW-10 stage2-readers.tsv' + ('; Q11 provider (handed-off file)' if r['home_tier'] == 'HANDED' else ''),
        owner_file=home if not w6 else home + ' (re-homed onto the canonical definition by W6)', tip_line='new',
        declaration=r['reader'], kind='add reader', statement_change='no (new declaration)',
        depends_on='S2-W6-*' if w6 else '-', est_lines=8, target='-',
        notes=('statement complete' if r['statement_complete'] == 'yes' else 'statement to be fixed in the brief (F07)') + f"; {r['n_items']} items")
s2 = list(csv.DictReader(open(f'{REC}/cleanup-dw10/final-r1/stage2-seal-items.tsv'), delimiter='\t'))
for i, r in enumerate(s2, 1):
    L = find_decl(TIP, r['owner_file'], r['declaration'])
    w6 = r['w6_dependent'] == 'yes'
    deps = list(reader_id.get(r['item_id'], []))
    if w6:
        deps.append('S2-W6-*')
    if r['fix_kind'] == 'ADD-PROVIDER-READER':
        deps = reader_id.get(r['item_id'], deps)
    kind = 'seal fix (after shadow retirement)' if r['fix_kind'].startswith('BRIDGE') else 'seal fix (proof-only)'
    add(id=f'S2-SL-{i:03d}', source=f"DW-10 {r['item_id']} ({r['fix_kind']}; {r['known_record'] if r['known_record'] != '-' else 'inventory'})",
        owner_file=r['owner_file'], tip_line=str(L), declaration=r['declaration'], kind=kind,
        depends_on=';'.join(deps) if deps else '-', est_lines=3 if r['channel'] == 'unfold' else 4,
        target=r['fix'][:160], notes=f"{r['channel']}; {r['fix_confidence']}" + ('; maintainer correction ' + r['maintainer_correction'] if r['maintainer_correction'] != '-' else ''))

# ---------------------------------------------------------------- 6. W6: retire the four shadows
W6 = [('ZeroKnowledge/GraphIsomorphism/Proofs.lean', 'GI', 'ZeroKnowledge/GraphIsomorphism.lean', 25, 700),
      ('ZeroKnowledge/ThreeColoring/ProtocolProofs.lean', 'ColProofs', 'ZeroKnowledge/ThreeColoring/Protocol.lean', 13, 320),
      ('ZeroKnowledge/GraphIsomorphismZK/Simulator.lean', 'GIZK', 'ZeroKnowledge/GraphIsomorphismZK.lean', 5, 180),
      ('ZeroKnowledge/ThreeColoring/SimulatorNumeric.lean', 'ColSimMachine', 'ZeroKnowledge/ThreeColoring/Simulator.lean', 6, 180)]
for i, (p, ns, main, ndefs, est) in enumerate(W6, 1):
    add(id=f'S2-W6-{i}', source='DW-10 W6 (Seyoon: retire the four shadow copies)', owner_file=full(p) + ' ; ' + full(main),
        tip_line='-', declaration=f'{ns}.* shadow definitions (~{ndefs}) and the shadow statements over them', kind='retire shadow',
        statement_change=f'yes: verbatim move of the canonical definitions below the proof file (REMOVED/ADDED pairs, CS1-Q3 precedent); {ns}.* lemma statements restated over the canonical names (definitional); {ns} shadow defs REMOVED',
        freeze_ref='W6 (Seyoon) + Q-W6 (proposed)', est_lines=est, target='canonical definitions of ' + full(main),
        notes='design to be fixed in the brief (Q-W6); main-file frozen statements unchanged')

# ---------------------------------------------------------------- 7. Q8: SEAL-B-ONLY rows
inv = list(csv.DictReader(open(f'{S}/inv/inventory.tsv'), delimiter='\t'))
stmt = set()
for l in open(f'{S}/dw10ev/outputs/stmtcheck.txt'):
    if "'SEAL-B-ONLY'" in l:
        stmt.update(re.findall(r"'([A-Z0-9-]+:\d+)'", l.rsplit('[', 1)[1]))
bonly = [r for r in inv if r['class'] == 'SEAL-B-ONLY']
for i, r in enumerate(bonly, 1):
    L = find_decl(TIP, r['base_path'], r['declaration'])
    short = r['declaration'].split('.')[-1]
    sl = r['item_id'] in stmt
    add(id=f'S2-BO-{i:03d}', source=f"DW-10 {r['item_id']} (SEAL-B-ONLY; {r['status']}{'; ' + r['known_record'] if r['known_record'] != '-' else ''})",
        owner_file=r['base_path'], tip_line=str(L), declaration=r['declaration'],
        kind='B-only fix statement-level [freeze exception]' if sl else 'B-only fix proof-level',
        statement_change='yes: header restated through PolyExpr.eval readers (meaning-preserving)' if sl else 'no',
        freeze_ref='Q8 (Seyoon) — listed individually' if sl else '-', depends_on='S2-PE (PolyExpr.eval reader set, if any is missing)',
        est_lines=8 if sl else 4, target='PolyExpr.eval readers', notes=f"coe-B {r['coe_B']} / strict-B {r['strict_B']} errors; fix text: none in the inventory (Q8 changed the ruling after the inventory)")

# ---------------------------------------------------------------- 8. PS10 Tier A / Tier B
TA = [('A1', 'TCSlib/Complexity/Randomized/Build/IterateFind.lean', [566])] + \
     [('A1', 'TCSlib/Complexity/Randomized/SeedMajority.lean', [26, 74, 173, 235]), ('A1', 'TCSlib/Complexity/Randomized/SeedMajority/Enumeration.lean', [42]),
      ('A1', 'TCSlib/Complexity/Randomized/SeedMajority/State.lean', [70, 99, 142, 155, 183, 220]), ('A1', 'TCSlib/Complexity/Randomized/SeedMajority/Words.lean', [45, 88, 116, 131, 163]),
      ('A2', 'TCSlib/Complexity/Randomized/SeedMajority.lean', [83]), ('A2', 'TCSlib/Cryptography/Randomness/Derandomization/RootSchedule.lean', [16]),
      ('A3', 'TCSlib/Cryptography/Authentication/MAC/FromPRF/Reduction.lean', [16]), ('A4', 'TCSlib/Cryptography/Authentication/Signatures/Lamport/Advice.lean', [112]),
      ('A5', 'TCSlib/Cryptography/Composability/SequentialZK.lean', [916]), ('A5', 'TCSlib/Cryptography/Composability/SequentialZK/Normalization.lean', [18]),
      ('A5', 'TCSlib/Cryptography/Composability/SequentialZK/NormalizationMachine.lean', [15]), ('A6', 'TCSlib/Cryptography/Encryption/PrivateKey.lean', [70]),
      ('A6', 'TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/Games.lean', [16]), ('A7', 'TCSlib/Cryptography/Encryption/PublicKey/OracleSecurity/ChallengeSim.lean', [18]),
      ('A7', 'TCSlib/Cryptography/Encryption/PublicKey/OracleSecurity/PaddedCPA.lean', [16]), ('A8', 'TCSlib/Cryptography/Hashing/CollisionResistant.lean', [45]),
      ('A9', 'TCSlib/Cryptography/SecureComputation/Garbling.lean', [40, 160]), ('A9', 'TCSlib/Cryptography/SecureComputation/SpecialEncryptionSecurity.lean', [23, 234]),
      ('A10', 'TCSlib/Cryptography/SecureComputation/ObliviousTransfer/ViewA.lean', [18, 50]), ('A11', 'TCSlib/Cryptography/SecureComputation/ObliviousTransfer/Efficiency.lean', [530]),
      ('A11', 'TCSlib/Cryptography/SecureComputation/Yao.lean', [853]), ('A11', 'TCSlib/Cryptography/SecureComputation/Yao/HybridProof/Lengths.lean', [18]),
      ('A12', 'TCSlib/Cryptography/SecureComputation/Yao/HybridProof/AliceProgram.lean', [90]), ('A13', 'TCSlib/Cryptography/SecureComputation/Yao/HybridProof/StatisticalSwitch.lean', [18])]
k = 0
for tag, path, Ls in TA:
    for L in Ls:
        tl = mapline(PS10BASE, path, L)
        k += 1
        add(id=f'S2-PA-{k:02d}', source=f'PS10 Tier A {tag}', owner_file=path, tip_line=str(tl), declaration='docstring',
            kind='citation fix', est_lines=2, target='REPORT §2 ' + tag, notes='docstring-only')
TB = [('CoinRelabel', 'TCSlib/Cryptography/SecureComputation/Yao/HybridProof/CoinRelabel.lean', [132]),
      ('SimulationBound', 'TCSlib/Cryptography/SecureComputation/Yao/HybridProof/SimulationBound.lean', [84]),
      ('StatisticalSwitch', 'TCSlib/Cryptography/SecureComputation/Yao/HybridProof/StatisticalSwitch.lean', [41, 67]),
      ('RepeatedSoundness', 'TCSlib/Cryptography/Composability/SequentialZK/RepeatedSoundness.lean', [139, 196]),
      ('SimulatorMachine', 'TCSlib/Cryptography/Composability/SequentialZK/SimulatorMachine.lean', [192, 312]),
      ('PhaseView', 'TCSlib/Cryptography/Composability/SequentialZK/PhaseView.lean', [49, 67, 159]),
      ('NormalizedStep', 'TCSlib/Cryptography/Composability/SequentialZK/NormalizedStep.lean', [47]),
      ('SuffixMachine', 'TCSlib/Cryptography/Composability/SequentialZK/SuffixMachine.lean', [161]),
      ('Learning', 'TCSlib/Cryptography/Randomness/Learning.lean', [117]),
      ('Distinguisher', 'TCSlib/Cryptography/Randomness/Learning/Distinguisher.lean', [14, 82]),
      ('Law', 'TCSlib/Cryptography/Randomness/Learning/Law.lean', [16, 144]),
      ('Random', 'TCSlib/Cryptography/Randomness/Learning/Random.lean', [15, 135]),
      ('Sample', 'TCSlib/Cryptography/Randomness/Learning/Sample.lean', [15])]
k = 0
for tag, path, Ls in TB:
    for L in Ls:
        tl = mapline(PS10BASE, path, L)
        k += 1
        add(id=f'S2-PB-{k:02d}', source=f'PS10 Tier B ({tag})', owner_file=path, tip_line=str(tl), declaration='docstring',
            kind='citation fix (advisory)', est_lines=1, target='mark the label as a repository step', notes='apply where it changes what a reader is told (Q-PS10B)')
REL = [('A11-related', 'TCSlib/Cryptography/SecureComputation/ObliviousTransfer/Efficiency.lean', [15]),
       ('A7-related', 'TCSlib/Cryptography/Encryption/PublicKey/OracleSecurity.lean', [63]),
       ('S_B exercise', 'TCSlib/Cryptography/SecureComputation/ObliviousTransfer/Simulators.lean', [14, 153]),
       ('enhanced hard-core', 'TCSlib/Cryptography/SecureComputation/YaoReal.lean', [86]),
       ('(1/2)^n bound', 'TCSlib/Cryptography/Hashing/FromDiscreteLog.lean', [709])]
k = 0
for tag, path, Ls in REL:
    for L in Ls:
        tl = mapline(PS10BASE, path, L)
        k += 1
        add(id=f'S2-PR-{k:02d}', source=f'PS10 related note ({tag}; outside the 871 pairs)', owner_file=path, tip_line=str(tl),
            declaration='docstring', kind='citation fix (advisory)', est_lines=1, target='REPORT §3 related notes', notes='Q-PS10B')

json.dump(items, open(f'{OUT}/items.json', 'w'), indent=0)
print(len(items))
