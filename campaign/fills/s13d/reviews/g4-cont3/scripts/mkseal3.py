# usage: mkseal3.py <module> <out> <seal-list>
# Wraps the whole home (from the first line after `Turing.zoneRowHi`'s definition, i.e. the
# docstring of `zr_singletonContract`, to `/-! ### The rows -/`) in a section that makes every listed
# other-file definition `local irreducible`. Controls inside the section must FAIL; the same
# controls after it must PASS.
import sys
src, out, lst = sys.argv[1:4]
names = [l.strip() for l in open(lst, encoding='utf-8') if l.strip() and not l.startswith('#')]
L = open(src, encoding='utf-8').read().split('\n')
rows = L.index('/-! ### The rows -/')
start = next(i for i, l in enumerate(L) if l.startswith("/-- Normalize a composite's singleton exit"))
assert L[start - 1] == '' and L[start - 2].startswith('  if j = 0 then (zoneStart'), L[start - 2]
controls = '''
/-- Seal control 1 (must FAIL inside the sealed section): a catalog contract field by defeq. -/
example {k : ℕ} (x w : List (ZoneSym k)) (d : Cfg 2 (ZoneSym k) SeekPhase x) :
    (skipTM_contract (0 : Fin 2) x).time w d = w.length + 1 := rfl

/-- Seal control 2 (must FAIL inside the sealed section): a zone-layer definition by defeq. -/
example : zoneStart 0 = 2 := rfl

/-- Seal control 3 (must FAIL inside the sealed section): the singleton adapter's endpoint read
by unfolding `Contract.ofSegment`. -/
example {n : ℕ} {Γ S I : Type} {x : List Γ} {M : MultiTapeTM n Γ S} {entry : S}
    {X : Set (Option S)} (R : Contract M entry X I x) (done : S) (hX : X = {some done}) :
    (zr_singletonContract R done hX).post = R.post := rfl

/-- Seal control 4 (must FAIL inside the sealed section): a seam's time by unfolding
`Contract.seq`. -/
example {k : ℕ} (x : List (ZoneSym k)) (D : zr_RightData k) (d) :
    (zr_rightPassContract x).time D d =
      (zr_rightRulerContract x).time D (d.mapState fun _ => Sum.inl (Sum.inl SeekPhase.run)) + 1 +
        (zr_writeHalvesContract x).time (zr_rulerWord D)
          (((zr_rightRulerContract x).post D (d.mapState fun _ => Sum.inl (Sum.inl SeekPhase.run))).mapState
            fun _ => Sum.inl SweepPhase.sweep) :=
  rfl
'''.split('\n')
inside = controls
outside = [c.replace('must FAIL inside the sealed section', 'must PASS outside the sealed section') for c in controls]
L = L[:rows] + inside + ['end G4C3Seal', ''] + outside + L[rows:]
L = L[:start] + ['section G4C3Seal', 'attribute [local irreducible] ' + ' '.join(names), ''] + L[start:]
open(out, 'w', encoding='utf-8').write('\n'.join(L))
print('home lines', start + 1, '..', rows, '; sealed', len(names))
