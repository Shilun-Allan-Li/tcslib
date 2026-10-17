"""MIG-1 statement gate, round 2: build the Loop overlay that demonstrates Finding 1's repair.

Usage: python3 -I build_overlay.py <worktree> <mig0b Finite.lean> <unit.lean> <outdir>

Read-only on its inputs. Writes, in <outdir>:
  LoopOverlay.lean        the overlay: part 1 + part 2 + the axiom printout
  part1.lean              part 1 alone: the tip's Build/Loop.lean with the round-2 edits
  part2.lean              part 2 alone: the unit's Loop part, shims dropped, sorries proved
  unit-loop-part.lean     the unit's Loop part as gated (for the part-2 diff)
  standin-source.lean     the MIG-0b declaration the stand-in copies (for the stand-in diff)
  standin.lean            the stand-in as inserted into part 1

Every edit is an asserted string replacement (`rep`): the old text must occur exactly the stated
number of times. Moved Catalog code and the stand-in are extracted from their source files and
transformed by asserted token replacements only; no hand-typed copies of source code.
"""
import os
import re
import sys

WT, FINITE, UNIT, OUT = sys.argv[1:5]
LOOP = os.path.join(WT, 'TCSlib/Complexity/TuringMachine/Build/Loop.lean')
CATALOG = os.path.join(WT, 'TCSlib/Complexity/TuringMachine/Build/Catalog.lean')


def read(p):
    with open(p, encoding='utf-8') as f:
        return f.read()


def rep(t, old, new, n=1):
    c = t.count(old)
    assert c == n, (c, n, old[:200])
    return t.replace(old, new)


def block(lines, first, last, head, tail):
    """Lines first..last (1-based, inclusive), asserting the first and last line's text."""
    b = lines[first - 1:last]
    assert b[0].startswith(head), (first, b[0])
    assert b[-1].rstrip() == tail.rstrip(), (last, b[-1])
    return '\n'.join(b)


tip = read(LOOP)
tip_lines = tip.split('\n')
cat_lines = read(CATALOG).split('\n')
fin_lines = read(FINITE).split('\n')

# ---------------------------------------------------------------------------------------------
# (b) The MIG-0b stand-in: the declaration at Finite.lean:396-408 (docstring 386-395), with the
# declaration keyword line changed only (name and `private`), and a stand-in docstring.
src_decl = block(fin_lines, 396, 408, 'theorem MultiTapeTM.workTapePos_runFrom_mem_Icc',
                 '    constructor <;> omega')
src_full = block(fin_lines, 386, 408, '/-- **The time-derived head envelope** (MIG-0b)',
                 '    constructor <;> omega')
standin_decl = rep(src_decl, 'theorem MultiTapeTM.workTapePos_runFrom_mem_Icc ',
                   'private theorem mig0bStandIn_workTapePos_runFrom_mem_Icc ')
STANDIN_DOC = '''/-- **Stand-in, not landed** (MIG-1 round-2 overlay only). A verbatim copy, statement and
proof, of MIG-0b's `Turing.MultiTapeTM.workTapePos_runFrom_mem_Icc` (MIG-0b's landing set,
`TuringMachine/Finite.lean:386-408`), which lands before MIG-1 S (user decision 3, 2026-10-14)
but is not at the campaign tip this overlay is elaborated against; only the name, `private` and
the namespace (`Turing.FinTM` here, `Turing` there) differ. At landing this declaration is
dropped and every citation `mig0bStandIn_workTapePos_runFrom_mem_Icc` becomes
`MultiTapeTM.workTapePos_runFrom_mem_Icc`, with the same explicit arguments. After `u` steps
from `cfg`, every work head lies within `u` cells of its start.

**Proof sketch.** Induction on `u`: each step moves a head by at most one cell
(`Turing.MultiTapeTM.workTapePos_step_le`). -/'''
standin = STANDIN_DOC + '\n' + standin_decl + '\n'


def cite(tm_cfg_u_j, indent):
    """The landing form `Finset.mem_Icc.mp (workTapePos_runFrom_mem_Icc tm cfg u j)`."""
    return 'Finset.mem_Icc.mp (mig0bStandIn_workTapePos_runFrom_mem_Icc ' + tm_cfg_u_j + ')'


# ---------------------------------------------------------------------------------------------
# (c) The moved loop-budget family, from Catalog.
def moved(text, names):
    for n in names:
        k = len(re.findall(r'\bf2_' + n + r'\b', text))
        assert k > 0, n
        text = re.sub(r'\bf2_' + n + r'\b', n, text)
    assert 'f2_' not in text and 'a2_' not in text, text[:300]
    return text


loopCall_heads = block(cat_lines, 8062, 8086, '/-- At a canonical call, only the retained',
                       '      · simpa only [Fin.addCases_right] using hf j')
loopCall_heads = rep(loopCall_heads,
                     'All body, flag, counter and capture heads are at zero. -/',
                     'All body, flag, counter and capture heads are at zero.\n'
                     '**Proof sketch.** Split the tape index: the capture tape, the body bank and\n'
                     'the counter tape of a canonical call are at the origin by construction, and\n'
                     'the fuel bank carries the given fuel configuration\'s heads. -/')
loopCall_heads = moved(loopCall_heads, ['loopCall_heads', 'loopCall', 'loopBodyPadded',
                                        'loopBodyCfg'])

tail3 = block(cat_lines, 8331, 8408, '/-- Uniform seam positions and segment lengths',
              '    exact f2_segment_heads M.tm cfg N B H hseam hend hterminal hsegment (u - startup) i')
tail3 = rep(tail3, 'occurs in the interval: every next segment restarts at a bounded seam. -/',
            'occurs in the interval: every next segment restarts at a bounded seam.\n'
            '**Proof sketch.** Induction on the number of seams `N`. Within the first segment\n'
            'a head moves at most one cell per step from a seam of radius `H`, so it stays\n'
            'within `H + B`; an early halt is absorbing; otherwise continue from the next\n'
            'seam. With no seams left, the halted terminal is stationary. -/')
tail3 = rep(tail3, 'The inclusive interval contains every head position at every prefix. -/',
            'The inclusive interval contains every head position at every prefix.\n'
            '**Proof sketch.** Each tape\'s visited set lies in `[-B, B]`, of cardinality\n'
            '`2B + 1` (`Int.card_Icc`); sum over the `k` tapes. -/')
tail3 = rep(tail3, 'in the common segment budget, independently of the number of rounds. -/',
            'in the common segment budget, independently of the number of rounds.\n'
            '**Proof sketch.** Up to `startup ≤ B` steps a head is within `B` of the origin;\n'
            'afterwards `segment_heads` applies from `cfg 0`; conclude by `space_radius`. -/')
tail3 = rep(tail3, '      have hh := f2_head_steps tm (cfg 0) v i',
            '      have hh := ' + cite('tm (cfg 0) v i', 6))
tail3 = rep(tail3, '  · have hp := f2_head_steps M.tm (M.tm.initCfg x) u i',
            '  · have hp := Finset.mem_Icc.mp\n'
            '      (mig0bStandIn_workTapePos_runFrom_mem_Icc M.tm (M.tm.initCfg x) u i)')
tail3 = moved(tail3, ['segment_heads', 'space_radius', 'seamed_space'])

# (d) Catalog's extended contract, moved over Loop's `loopHost_contracts` (statement and proof;
# Loop's docstring is kept and extended).
ext = block(cat_lines, 8113, 8290, 'private lemma f2_loopHost_contracts',
            '    exact hterminalheads j')
ext = rep(ext, 'f2_loopHost_prepare body F anchor findMode R T hF x',
          'loopHost_prepare body F anchor false findMode R T hF x')
ext = rep(ext, 'f2_loopHost_start body F anchor findMode (s0 x)',
          'loopHost_start body F anchor false findMode (s0 x)')
ext = rep(ext, '    · have hd := f2_head_steps (f2_loopHost body F anchor findMode).tm\n'
               '        (candidate (R x.length)) (time (R x.length)) j',
          '    · have hd := Finset.mem_Icc.mp (mig0bStandIn_workTapePos_runFrom_mem_Icc\n'
          '        (loopHost body F anchor findMode).tm (candidate (R x.length)) (time (R x.length)) j)')
ext = rep(ext, 'f2_loopHost body F anchor findMode', 'loopHost body F anchor findMode', 18)
# the witness `c = loopHost_bound = 10` made explicit (round-1 manifest transform `∃ c` removed,
# `c ↦ 10`): four statement occurrences, and the opening `refine`
ext = rep(ext, '    ∃ c : ℕ, ∀ x : List Bool,\n', '    ∀ x : List Bool,\n')
ext = rep(ext, 'c * (T x.length + 1)', '10 * (T x.length + 1)', 4)
ext = rep(ext, '  refine ⟨f2_loopHost_bound, ?_⟩\n', '')
ext = moved(ext, ['loopHost_contracts', 'loopCall_heads', 'loopCall', 'loopDebit_iterate_length',
                  'loopDebit_iterate_value', 'loopDebit_success', 'loopDebit', 'loopHost_bound',
                  'loopHost_round', 'loop_fuel_width', 'loop_orbit_inv'])
# two over-wide lines of the moved text, wrapped (they are new in Loop)
ext = rep(ext, '    · simpa only [candidate, words, orbit, Function.iterate_succ_apply\', '
               'hsuccess i hi] using hsegment',
          '    · simpa only [candidate, words, orbit, Function.iterate_succ_apply\',\n'
          '        hsuccess i hi] using hsegment')
ext = rep(ext, '  have hterminal : terminal.state = none ∧ terminal.output = '
               '(if findMode then [] else [false]) := by',
          '  have hterminal :\n'
          '      terminal.state = none ∧ terminal.output = (if findMode then [] else [false]) := by')

# ---------------------------------------------------------------------------------------------
# Part 1: the tip's Loop.lean with the edits.
t = tip
# imports: the unit Loop part's one extra import (already in Loop's closure)
t = rep(t, 'import TCSlib.Complexity.TuringMachine.Composition\n',
        'import TCSlib.Complexity.TuringMachine.Composition\n'
        'import TCSlib.Complexity.TuringMachine.Simulation\n')

# (a) the strengthened `loopHost_prepare`: docstring, statement, proof
t = rep(t, '''/-- Fuel execution, setup, and input rewind reach prepared body startup
within `5*T+7` steps, retaining the actual fuel endpoint.
**Proof sketch.** Replace the supplied padded fuel run by its first halt,
relocate it twice, and capture it in the actual host. Setup costs `3L+4`,
where `L ≤ T`; the input rewind costs at most the first run's displacement
plus two, hence at most `T+3`. No bound in the input length is used. -/''',
        standin + '''
/-- Fuel execution, setup, and input rewind reach prepared body startup
within `5*T+7` steps, retaining the actual fuel endpoint, whose work heads lie
within `T |x|` of the origin (the fuel-head clause, added by MIG-1: the extended
`loopHost_contracts` needs it for the seam head bounds of the space budget).
**Proof sketch.** Replace the supplied padded fuel run by its first halt,
relocate it twice, and capture it in the actual host. Setup costs `3L+4`,
where `L ≤ T`; the input rewind costs at most the first run's displacement
plus two, hence at most `T+3`. No bound in the input length is used. The fuel
endpoint is the run at the first halting time `u ≤ T |x|` from the initial
configuration, whose heads are at the origin, and each step moves a head by at
most one cell (`MultiTapeTM.workTapePos_runFrom_mem_Icc`). -/''')
t = rep(t, '''      (loopHostM body F anchor forward findMode).tm.runFrom
        ((loopHostM body F anchor forward findMode).tm.initCfg x) t = loopReady body F c := by''',
        '''      (loopHostM body F anchor forward findMode).tm.runFrom
        ((loopHostM body F anchor forward findMode).tm.initCfg x) t = loopReady body F c ∧
      ∀ i, -(T x.length : ℤ) ≤ c.workTapePos i ∧ c.workTapePos i ≤ T x.length := by''')
t = rep(t, '  refine ⟨c, u + (3 * c.output.length + 4) + v, hc, ho, ?_, ?_⟩\n',
        '  refine ⟨c, u + (3 * c.output.length + 4) + v, hc, ho, ?_, ?_, ?_⟩\n')
t = rep(t, '''      MultiTapeTM.runFrom_add (a := u) (b := 3 * c.output.length + 4), hcap, hsetup, hrew]
    rfl

/-- The stopped body's padded source configuration''',
        '''      MultiTapeTM.runFrom_add (a := u) (b := 3 * c.output.length + 4), hcap, hsetup, hrew]
    rfl
  · intro i
    have h := Finset.mem_Icc.mp
      (mig0bStandIn_workTapePos_runFrom_mem_Icc F.tm (F.tm.initCfg x) u i)
    have hh : -(u : ℤ) ≤ c.workTapePos i ∧ c.workTapePos i ≤ u := by
      simpa [c, MultiTapeTM.initCfg, Cfg.init, Cfg.ofWords] using h
    omega

/-- The stopped body's padded source configuration''')

# (c) `loopCall_heads` before `loopHost_bound`
t = rep(t, '/-- The audit\'s single maximum: startup coefficient nine, body coefficient\n',
        loopCall_heads + '\n\n'
        '/-- The audit\'s single maximum: startup coefficient nine, body coefficient\n')

# (d) the contract: Loop's docstring extended; the statement and proof replaced
t = rep(t, '''ledger. The missing proof is precisely the controller-level lifting and
assembly of these phase contracts, including startup and replay bounds. -/
/- Batch L2 closure:''', '''ledger. The missing proof is precisely the controller-level lifting and
assembly of these phase contracts, including startup and replay bounds.

**MIG-1 extension** (Catalog's extended copy, moved here, replacing the original
statement and proof): the coefficient is explicit, `10 = loopHost_bound`, and two
clauses are added. Every candidate seam `cfg i`, `i ≤ R |x|`, has its work heads
within `T |x|` of the origin (`loopCall_heads` with the fuel-head clause of
`loopHost_prepare`), and the terminal `cfg (R |x| + 1)` within
`T |x| + 10·(T |x| + 1)`: either the halted copy of the next seam, after an
accepting last candidate, or the last segment's endpoint, at most
`10·(T |x| + 1)` steps from a seam. The space budget uses both. -/
/- Batch L2 closure:''')
old_contract = block(tip_lines, 2066, 2211, 'private lemma loopHost_contracts',
                     '        simp only [terminal, ha, Bool.false_eq_true, ↓reduceIte]')
t = rep(t, old_contract, ext)
# the moved space lemmas after the contract
t = rep(t, '\n/-- **The configuration-level loop combinator** (added per round-2 finding 1',
        '\n' + tail3 + '\n\n/-- **The configuration-level loop combinator** (added per round-2 finding 1')

# callers of the replaced contract and of the strengthened preparation lemma
t = rep(t, '''  obtain ⟨c, hc⟩ := loopHost_contracts body F anchor Inv stepF acceptF
    (fun _ _ => [true]) false s0 R T hF hInv0 hInvStep hstart hround
  exact ⟨loopHost body F anchor false, c, by simpa using hc⟩''',
        '''  have hc := loopHost_contracts body F anchor Inv stepF acceptF
    (fun _ _ => [true]) false s0 R T hF hInv0 hInvStep hstart hround
  refine ⟨loopHost body F anchor false, 10, fun x => ?_⟩
  obtain ⟨cfg, startup, hs, hinit, hout, hend, hterm, hseg, -, -⟩ := hc x
  exact ⟨cfg, startup, hs, hinit, hout, hend, by simpa using hterm, by simpa using hseg⟩''')
t = rep(t, '''  obtain ⟨c, hc⟩ := loopHost_contracts body F anchor Inv stepF acceptF out true s0 R T
    hF hInv0 hInvStep hstart hround
  let E := loopHost body F anchor true
  refine ⟨E, c, fun x => ?_⟩
  obtain ⟨cfg, startup, hs, hinit, _, hend, hout, hsegments⟩ := hc x''',
        '''  have hc := loopHost_contracts body F anchor Inv stepF acceptF out true s0 R T
    hF hInv0 hInvStep hstart hround
  let c : ℕ := 10
  let E := loopHost body F anchor true
  refine ⟨E, c, fun x => ?_⟩
  obtain ⟨cfg, startup, hs, hinit, _, hend, hout, hsegments, -, -⟩ := hc x''')
t = rep(t, '''  obtain ⟨fuel, ftime, hfh, hfo, hft, hprepare⟩ :=
    loopHost_prepare body F anchor true true R T hF x''',
        '''  obtain ⟨fuel, ftime, hfh, hfo, hft, hprepare, -⟩ :=
    loopHost_prepare body F anchor true true R T hF x''')
assert 'f2_' not in t and 'a2_' not in t
part1 = t

# ---------------------------------------------------------------------------------------------
# Part 2: the unit's Loop part (unit lines 799-1488), shims dropped, sorries proved.
ulines = read(UNIT).split('\n')
upart = block(ulines, 799, 1488, '/-! ════ Part 6. `Build/Loop.lean`', 'end Turing.FinTM')
p = upart
# the three shim blocks: verbatim copies of declarations that the overlay has as originals
shims = re.findall(r'-- @shim begin[^\n]*\n.*?-- @shim end\n', p, re.S)
assert len(shims) == 3, len(shims)
for s in shims:
    p = rep(p, s, '-- (gate shim dropped: the overlay holds the original declarations)\n')

# docstrings: no Catalog `f2_` name survives F-D, so none is cited
p = rep(p, '''`Build/Loop.lean:649`, today the private abbreviation `loopHost`, body unchanged; Catalog holds
an older copy, `f2_loopHost`, from before the forwarding flag). The decision and find host of''',
        '''`Build/Loop.lean:649`, today the private abbreviation `loopHost`, body unchanged; Catalog's
older copy from before the forwarding flag is deleted at F-D). The decision and find host of''')
p = rep(p, '''**Proof sketch.** The space half of Catalog's private `f2_exists_loopFind_space`
(`Build/Catalog.lean:8411`), which uses no find-mode fact: the extended contract
`f2_loopHost_contracts` (it replaces `loopHost_contracts`, moved and re-targeted) also bounds
every seam's heads by `T |x|` and the terminal's by `T |x| + 10·(T |x| + 1)`; each segment
lasts at most `10·(T |x| + 1)` steps, so by `f2_seamed_space` (moved, with `f2_segment_heads`
and `f2_space_radius`) every head stays within `T |x| + 10·(T |x| + 1)` of the origin at every''',
        '''**Proof sketch.** The space half of Catalog's private find-mode space lemma (deleted at
F-D), which uses no find-mode fact: the extended contract `loopHost_contracts` (moved from
Catalog over the original) also bounds every seam's heads by `T |x|` (from the fuel-head clause
of `loopHost_prepare`) and the terminal's by `T |x| + 10·(T |x| + 1)`; each segment lasts at
most `10·(T |x| + 1)` steps, so by `seamed_space` (moved, with `segment_heads` and
`space_radius`) every head stays within `T |x| + 10·(T |x| + 1)` of the origin at every''')


def prove(text, name, proof):
    i = text.index('theorem ' + name + ' ')
    j = text.index(':= by\n  sorry\n', i)
    assert text.count('theorem ' + name + ' ') == 1
    old = text[i:j] + ':= by\n  sorry\n'
    assert text.count(old) == 1 and old.count('/--') == 0, name
    return rep(text, old, text[i:j] + ':= by\n' + proof)


p = prove(p, 'loopHostTM_contracts', '''  intro x
  obtain ⟨cfg, startup, hs, hinit, hout, hend, hterm, hseg, -, -⟩ :=
    loopHost_contracts body F anchor Inv stepF acceptF out findMode s0 R T hF hInv0 hInvStep
      hstart hround x
  exact ⟨cfg, startup, hs, hinit, hout, hend, hterm, hseg⟩
''')
p = prove(p, 'loopHostTM_decides', '''  intro x
  let E := loopHostTM body F anchor false
  obtain ⟨cfg, startup, hs, hinit, _, hend, hout, hsegments⟩ :=
    loopHostTM_contracts body F anchor Inv stepF acceptF (fun _ _ => [true]) false s0 R T hF
      hInv0 hInvStep hstart hround x
  obtain ⟨t, ht, hhalt, houtput⟩ := loop_halted_run E.tm cfg
    (fun i => acceptF x ((stepF x)^[i] (s0 x))) (10 * (T x.length + 1))
    (R x.length + 1) ⟨hend, by simpa using hout⟩
    (fun j hj => by simpa using hsegments j (by omega))
  have hrun := E.tm.runFrom_add (E.tm.initCfg x) startup t
  rw [hinit] at hrun
  have hcompute : E.ComputesInTime x
      [(List.range (R x.length + 1)).any
        (fun i => acceptF x ((stepF x)^[i] (s0 x)))] (startup + t) := by
    refine ⟨_, ?_, ?_, rfl⟩
    · rw [hrun]; exact hhalt
    · rw [hrun]; exact houtput
  apply hcompute.mono
  calc startup + t ≤ 10 * (T x.length + 1) +
        (R x.length + 1) * (10 * (T x.length + 1)) := Nat.add_le_add hs ht
    _ = 10 * (T x.length + 1) * (R x.length + 2) := by
      rw [Nat.mul_comm (R x.length + 1)]
      simp only [Nat.mul_add, Nat.mul_one, Nat.mul_two]
      omega
''')
p = prove(p, 'loopHostTM_finds', '''  intro x
  let E := loopHostTM body F anchor true
  obtain ⟨cfg, startup, hs, hinit, _, hend, hout, hsegments⟩ :=
    loopHostTM_contracts body F anchor Inv stepF acceptF out true s0 R T hF hInv0 hInvStep
      hstart hround x
  obtain ⟨t, ht, hhalt, houtput⟩ := loop_find_run E.tm cfg
    (fun i => acceptF x ((stepF x)^[i] (s0 x)))
    (fun i => out x ((stepF x)^[i] (s0 x))) (10 * (T x.length + 1)) (R x.length + 1)
    ⟨hend, by simpa using hout⟩
    (fun j hj => by simpa using hsegments j (by omega))
  have hrun := E.tm.runFrom_add (E.tm.initCfg x) startup t
  rw [hinit] at hrun
  have hcompute : E.ComputesInTime x
      (match (List.range (R x.length + 1)).find?
          (fun i => acceptF x ((stepF x)^[i] (s0 x))) with
        | some i => out x ((stepF x)^[i] (s0 x))
        | none => []) (startup + t) := by
    refine ⟨_, ?_, ?_, rfl⟩
    · rw [hrun]; exact hhalt
    · rw [hrun]; exact houtput
  apply hcompute.mono
  calc startup + t ≤ 10 * (T x.length + 1) +
        (R x.length + 1) * (10 * (T x.length + 1)) := Nat.add_le_add hs ht
    _ = 10 * (T x.length + 1) * (R x.length + 2) := by
      rw [Nat.mul_comm (R x.length + 1)]
      simp only [Nat.mul_add, Nat.mul_one, Nat.mul_two]
      omega
''')
p = prove(p, 'loopHostTM_spaceUsed_le_budget', '''  let E := loopHostTM body F anchor findMode
  obtain ⟨cfg, startup, hs, hinit, _, hend, _, hsegments, hheads, hterminal⟩ :=
    loopHost_contracts body F anchor Inv stepF acceptF out findMode s0 R T hF hInv0
      hInvStep hstart hround x
  have h := seamed_space E x cfg (R x.length + 1) (10 * (T x.length + 1))
    (T x.length) startup hs hinit (fun j hj => hheads j (by omega)) hend hterminal
    (by
      intro j hj
      obtain ⟨u, hu, he⟩ := hsegments j (by omega)
      refine ⟨u, hu, ?_⟩
      split at he
      · exact Or.inl he.1
      · exact Or.inr he) t
  have hb : 2 * (T x.length + 10 * (T x.length + 1)) + 1 ≤ 23 * (T x.length + 1) := by omega
  calc
    _ ≤ E.k * (23 * (T x.length + 1)) := h.trans (Nat.mul_le_mul_left _ hb)
    _ = 23 * E.k * (T x.length + 1) := by
      rw [Nat.mul_assoc, Nat.mul_left_comm]
''')
# `emitLoopTM_computes`: the proof of today's `exists_emitLoopTM`, from the tip, with the named
# witness for the existential and the extra conjunct of the strengthened preparation discarded
i = tip.index('theorem exists_emitLoopTM ')
j = tip.index(':= by\n', i) + len(':= by\n')
k = tip.index('\n/-- **E5a, the install-mode clean call**', j)
emit_proof = tip[j:k].rstrip('\n') + '\n'
emit_proof = rep(emit_proof, '  let E := emLoopHost body F anchor true\n  refine ⟨E, 10, fun x => ?_⟩\n',
                 '  intro x\n  let E := emitLoopTM body F anchor\n')
emit_proof = rep(emit_proof, '  obtain ⟨fuel, ftime, hfh, hfo, hft, hprepare⟩ :=\n',
                 '  obtain ⟨fuel, ftime, hfh, hfo, hft, hprepare, -⟩ :=\n')
p = prove(p, 'emitLoopTM_computes', emit_proof)
p = prove(p, 'callTM_run', '  exact emCall_first M emit x arg cap T hM\n')
assert 'sorry' not in p
assert 'f2_' not in p and 'a2_' not in p
part2 = p

AX = ['mig0bStandIn_workTapePos_runFrom_mem_Icc', 'loopHost_prepare', 'loopCall_heads',
      'loopHost_contracts', 'segment_heads', 'space_radius', 'seamed_space',
      'exists_loopCfgTM', 'exists_loopTM', 'exists_loopFindTM', 'exists_emitLoopTM',
      'loopHostTM_contracts', 'loopHostTM_decides', 'loopHostTM_finds',
      'loopHostTM_spaceUsed_le_budget', 'emitLoopTM_computes', 'callTM_run',
      'MIG1Gate.row_exists_loopCfgTM', 'MIG1Gate.row_exists_loopTM',
      'MIG1Gate.row_exists_loopFindTM', 'MIG1Gate.row_exists_emitLoopTM',
      'MIG1Gate.row_exists_installCallTM', 'MIG1Gate.row_exists_emitCallTM']
axioms = ('/-! Axiom printout (overlay only, not landed): the repaired preparation lemma, the\n'
          'moved budget family, the replaced contract, the four loop rows, the Loop-part specs\n'
          'and the six gate rows. -/\n\nnamespace Turing.FinTM\n\n'
          + ''.join('#print axioms ' + n + '\n' for n in AX) + '\nend Turing.FinTM\n')

header2 = ('\n/-! ════ MIG-1 round-2 overlay, part 2 (not landed as such): the unit\'s Loop part,\n'
           'its gate shims dropped (the overlay holds the originals) and its `sorry`s replaced by\n'
           'proofs over the declarations above. -/\n\n')
overlay = part1.rstrip('\n') + '\n' + header2 + part2.rstrip('\n') + '\n\n' + axioms
os.makedirs(OUT, exist_ok=True)
for name, txt in [('LoopOverlay.lean', overlay), ('part1.lean', part1), ('part2.lean', part2),
                  ('unit-loop-part.lean', upart + '\n'), ('standin-source.lean', src_full + '\n'),
                  ('standin.lean', standin)]:
    with open(os.path.join(OUT, name), 'w', encoding='utf-8') as f:
        f.write(txt)
wide = [(n, len(l)) for n, l in enumerate(overlay.split('\n'), 1) if len(l) > 100]
print('overlay lines:', overlay.count('\n'), '; part1 lines:', part1.count('\n'),
      '; part2 lines:', part2.count('\n'), '; lines over 100 columns:', len(wide))
