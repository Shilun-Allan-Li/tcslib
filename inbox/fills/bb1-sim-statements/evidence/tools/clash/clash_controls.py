"""(bb1-sim-statements, lead: copied unchanged from the bb1-machine delivery, evidence/clash/.)
clash_controls.py <repo> <base-rev> <outdir>

Controls of clash_scan.py (fill bb1-machine), and the pre-scan of the planned glue names. Run as
`python3 -I clash_controls.py /home/user/fill/wt-sub 7c0a55e0 <outdir>`. Loads clash_scan.py
from its own directory (by path; `-I` puts no script directory on sys.path), builds the base index
at <base-rev> from git objects, and runs the scanner's core (`added_decls` + `classify`) on
synthetic head files:
  K1 a synthetic NEW file under namespaces mixing fake and existing names, each with an expected
     status (CLASH for an existing public name; for an existing private name; for a dotted name
     `IBEScheme.sidSpec_eq` inside the outer namespace; for a `_root_.`-qualified existing name;
     inside `section`/`noncomputable section`/`mutual` blocks; after a partial `end`; OK for
     fresh names; anonymous instances and names in comments/strings ignored).
  K2 a synthetic ADDED LINE in the base Defs.lean (a duplicate `oracleImpl_one` inserted after
     line 387, inside `namespace IBEScheme`): CLASH (same file, one more declaration than base).
  K3 a synthetic CHANGED header line of an existing declaration (`oracleImpl_two` in Defs.lean,
     binder renamed): MODIFIED (not a new name).
  PRE the planned glue of `BonehBoyenMachine/Oracles.lean` (namespace
     TCSlib.Cryptography.AdvancedEncryption.IdentityBased, then BB1Machine): the six private
     `cast_eq_padFin`, `ofFn_padFin_ofFn`, `ofFn_decAnswer_some`, `sidSpec_rng_one'`,
     `sidSpec_rng_two'`, `expect_bb1SimImpl` and the public
     `abs_expect_bb1Sim_sub_distinguisherL_le`; written to <outdir>/planned-prescan.tsv.
Prints one line per control and `ALL_CONTROLS_OK True|False`, then the pre-scan's RESULT.

written by tools-agent (sub-agent), fill bb1-machine
"""
import importlib.util
import os
import sys

NS = 'TCSlib.Cryptography.AdvancedEncryption.IdentityBased'
DEFS = 'TCSlib/Cryptography/AdvancedEncryption/IdentityBased/Defs.lean'
FAKE = 'TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenMachine/Fake.lean'
ORACLES = 'TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenMachine/Oracles.lean'

K1_TEXT = '''/-! module doc: theorem oracleImpl_zero ... namespace Foo ... end -/
namespace TCSlib.Cryptography.AdvancedEncryption.IdentityBased

/-- docstring: `theorem bb1SimCt_eq` and `end IBEScheme` are not commands here. -/
theorem fakeClash_fresh_one : True := trivial
-- theorem drawStep : commented out
def fakeStr : String := "theorem bb1SimCt_eq inside a string"

namespace IBEScheme
theorem oracleImpl_zero : True := trivial
end IBEScheme

section Inner
private lemma IBEScheme.sidSpec_eq : True := trivial
end Inner

theorem _root_.TCSlib.Cryptography.AdvancedEncryption.IdentityBased.bb1SimCt_eq : True :=
  trivial

instance : Inhabited Nat := ⟨0⟩
instance (priority := 100) fakeInst_fresh : Inhabited Bool := ⟨true⟩

namespace BB1Machine
noncomputable section
@[simp] private theorem expect_sample_eq_uprob : True := trivial
protected def fakeClash_fresh_two : Nat := 0
end
mutual
def drawStep : Nat := 0
end
end BB1Machine

namespace IBEScheme.Sub
theorem fakeClash_fresh_three : True := trivial
end Sub
theorem oracleImpl_one : True := trivial
end IBEScheme

end TCSlib.Cryptography.AdvancedEncryption.IdentityBased
'''
K1_EXPECT = {
    NS + '.fakeClash_fresh_one': 'OK',
    NS + '.fakeStr': 'OK',
    NS + '.IBEScheme.oracleImpl_zero': 'CLASH',
    NS + '.IBEScheme.sidSpec_eq': 'CLASH',
    NS + '.bb1SimCt_eq': 'CLASH',
    NS + '.fakeInst_fresh': 'OK',
    NS + '.BB1Machine.expect_sample_eq_uprob': 'CLASH',
    NS + '.BB1Machine.fakeClash_fresh_two': 'OK',
    NS + '.BB1Machine.drawStep': 'CLASH',
    NS + '.IBEScheme.Sub.fakeClash_fresh_three': 'OK',
    NS + '.IBEScheme.oracleImpl_one': 'CLASH',
}

PLANNED_TEXT = '''namespace TCSlib.Cryptography.AdvancedEncryption.IdentityBased

namespace BB1Machine

private theorem cast_eq_padFin : True := trivial
private theorem ofFn_padFin_ofFn : True := trivial
private theorem ofFn_decAnswer_some : True := trivial
private theorem sidSpec_rng_one' : True := trivial
private theorem sidSpec_rng_two' : True := trivial
private theorem expect_bb1SimImpl : True := trivial
theorem abs_expect_bb1Sim_sub_distinguisherL_le : True := trivial

end BB1Machine

end TCSlib.Cryptography.AdvancedEncryption.IdentityBased
'''


def load_core():
    sys.dont_write_bytecode = True  # no __pycache__ in the evidence directory
    here = os.path.dirname(os.path.abspath(__file__))
    spec = importlib.util.spec_from_file_location('clash_scan', os.path.join(here,
                                                                            'clash_scan.py'))
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m


def main(argv):
    if len(argv) != 4:
        print(__doc__)
        return 2
    repo, rev, out = argv[1:4]
    os.makedirs(out, exist_ok=True)
    cs = load_core()
    rev = cs.git(repo, 'rev-parse', rev + '^{commit}').decode().strip()
    idx = cs.base_index(repo, rev)
    print(f'base {rev}: {idx["nfiles"]} files, {idx["ndecls"]} declarations')
    ok = True
    # K1
    rows = cs.classify(cs.added_decls(K1_TEXT, None, FAKE, 'A'), idx)
    got = {r['full']: r['status'] for r in rows}
    k1 = got == K1_EXPECT
    ok &= k1
    print(f'K1 synthetic new file: {"OK" if k1 else "UNEXPECTED"} | {len(rows)} declarations')
    for r in rows:
        mark = '' if K1_EXPECT.get(r['full']) == r['status'] else \
            f'   <-- expected {K1_EXPECT.get(r["full"])}'
        print(f'    {r["status"]:8} {r["full"]} [{" ".join(r["flags"]) or "-"}] '
              f'{cs.fmt_locs(r["clash"], 3)}{mark}')
    for k in sorted(set(K1_EXPECT) - set(got)):
        print(f'    MISSING  {k} (expected {K1_EXPECT[k]})')
    # K2 / K3 on the base Defs.lean
    base_defs = cs.cat_files(repo, rev, [DEFS])[DEFS]
    L = base_defs.split('\n')
    assert L[386] == '    S.oracleImpl κ init key chal 2 x s = chal x s := rfl'
    L2 = L[:387] + ['', 'theorem oracleImpl_one : True := trivial'] + L[387:]
    rows = cs.classify(cs.added_decls('\n'.join(L2), {388, 389}, DEFS), idx)
    k2 = [(r['full'], r['status']) for r in rows] == [(NS + '.IBEScheme.oracleImpl_one', 'CLASH')]
    ok &= k2
    print(f'K2 synthetic added line in Defs.lean: {"OK" if k2 else "UNEXPECTED"} | '
          + '; '.join(f'{r["status"]} {r["full"]} {cs.fmt_locs(r["clash"], 3)}' for r in rows))
    j = next(i for i, x in enumerate(L) if x.startswith('theorem oracleImpl_two '))
    L3 = list(L)
    L3[j] = L3[j].replace('{σ : Type}', '{τ : Type}')
    assert L3[j] != L[j]
    rows = cs.classify(cs.added_decls('\n'.join(L3), {j + 1}, DEFS), idx)
    k3 = [(r['full'], r['status']) for r in rows] == [(NS + '.IBEScheme.oracleImpl_two',
                                                        'MODIFIED')]
    ok &= k3
    print(f'K3 synthetic changed header line in Defs.lean: {"OK" if k3 else "UNEXPECTED"} | '
          + '; '.join(f'{r["status"]} {r["full"]}' for r in rows))
    print('ALL_CONTROLS_OK', ok)
    # PRE: planned names
    rows = cs.classify(cs.added_decls(PLANNED_TEXT, None, ORACLES, 'A'), idx)
    res, k, dup = cs.write_report(rows, os.path.join(out, 'planned-prescan.tsv'), [
        f'PRE-SCAN of the planned glue names (synthetic file {ORACLES}) against {rev}',
        'declarations stubbed as `True := trivial`: only the names and namespaces matter'])
    for r in rows:
        print(f'PRE {r["status"]:5} {r["full"]} [{" ".join(r["flags"]) or "-"}] clash: '
              f'{cs.fmt_locs(r["clash"]) or "-"} | same short name: '
              f'{cs.fmt_locs(r["info"], 6) or "-"}')
    print('PRE-SCAN', res)
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main(sys.argv))
