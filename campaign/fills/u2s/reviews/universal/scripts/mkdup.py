"""Build the semantic-duplication probe: the base module with the overlay import, then (inside
`namespace Turing`) the new private *definitions* verbatim, then each sampled new private's
statement posed as an `example` to `exact?`/`apply?`, plus controls posing the published lemmas'
statements. Usage: mkdup.py <base UniversalK.lean> <head UniversalK.lean> <out>"""
import re, sys
base, head, out = sys.argv[1:4]
Bs = open(base, encoding='utf-8').read().split('\n')
H = open(head, encoding='utf-8').read().split('\n')
assert Bs[10] == 'import TCSlib.Complexity.TuringMachine.Build.SeamLayout'
Bs.insert(11, 'import TCSlib.Complexity.TuringMachine.Build.Rewind')
assert Bs[-2] == 'end Turing' and Bs[-1] == ''
D = re.compile(r'^(?:@\[[^\]]*\]\s*)*((?:(?:private|protected|noncomputable)\s+)*)(theorem|lemma|def|abbrev)\s+(\S+)')
starts = [(i, D.match(l)) for i, l in enumerate(H) if D.match(l)]
def block(name):
    for j, (i, m) in enumerate(starts):
        if m.group(3) == name:
            e = i
            while e < len(H) and H[e].strip() != '':
                e += 1
            return H[i:e]
    raise SystemExit('missing ' + name)
def stmt(name):
    txt = block(name)
    s = '\n'.join(txt)
    k = s.index(':= by')
    head_ = s[:k].rstrip()
    head_ = re.sub(r'^private theorem ' + re.escape(name), f'example /- {name} -/', head_)
    return head_
defs = ['uk_loopTM', 'uk_scanTM', 'uk_scanCfg', 'uk_headerTM', 'uk_suffixStartupTM', 'uk_suffixCfg']
sample = ['uk_init_mapState', 'uk_encode_halt', 'uk_loop_pre_live', 'uk_loop_forward', 'uk_loop_live',
          'uk_loop_converse', 'uk_ruler_fields', 'uk_scan_ruler', 'uk_loop_init', 'uk_encode_init_fields']
parts = ['', '/-! ## Review: semantic-duplication probes (appended; not part of the module) -/', '']
for d in defs:
    parts += block(d) + ['']
for n in sample:
    parts += [f'-- PROBE {n} (exact?)', 'set_option maxHeartbeats 4000000 in', stmt(n) + ' := by', '  exact?', '']
parts += ['-- PROBE uk_loop_live (apply?)', 'set_option maxHeartbeats 4000000 in', stmt('uk_loop_live') + ' := by', '  apply?', '']
parts += ['-- PROBE uk_init_mapState (apply?)', 'set_option maxHeartbeats 4000000 in', stmt('uk_init_mapState') + ' := by', '  apply?', '']
# controls: inline arguments of the delivered file posed as statements
parts += ['-- CONTROL first halt with absorption (uk_loop_forward, lines 1881-1890)',
          'set_option maxHeartbeats 4000000 in',
          'example {k n : ℕ} {x : List Bool} (M : MultiTapeTM k Bool (Fin (n + 1))) (t : ℕ)',
          '    (hhalt : (M.runFrom (M.initCfg x) t).state = none) :',
          '    ∃ t₀ ≤ t, (∀ u < t₀, ¬(M.runFrom (M.initCfg x) u).Halted) ∧',
          '      M.runFrom (M.initCfg x) t₀ = M.runFrom (M.initCfg x) t := by',
          '  exact?', '',
          '-- CONTROL visited sets grow (exists_selfUniversalK, lines 2128-2132)',
          'set_option maxHeartbeats 4000000 in',
          'example {k n : ℕ} {x : List Bool} (M : MultiTapeTM k Bool (Fin (n + 1))) (t₀ t : ℕ)',
          '    (ht₀ : t₀ ≤ t) (j : Fin k) :',
          '    M.visitedByTapeHead (M.initCfg x) t₀ j ⊆ M.visitedByTapeHead (M.initCfg x) t j := by',
          '  exact?', '',
          '-- CONTROL halted space frozen (exists_selfUniversalK hfreeze, lines 2145-2161)',
          'set_option maxHeartbeats 4000000 in',
          'example (U : FinTM Bool) (z output : List Bool) (t₁ t₂ s : ℕ)',
          '    (h : U.ComputesInTime z output t₁) (hs : U.tm.spaceUsed (U.tm.initCfg z) t₁ ≤ s) :',
          '    U.tm.spaceUsed (U.tm.initCfg z) t₂ ≤ s := by',
          '  exact?', '']
text = '\n'.join(Bs[:-2]) + '\n' + '\n'.join(parts) + '\nend Turing\n'
open(out, 'w', encoding='utf-8').write(text)
print('wrote', out, len(text.split('\n')), 'lines')
