"""Write the G2 fill's prescribed overlay of `Build/Catalog.lean` (read-only on its inputs).

Usage: python3 -I mkoverlay.py <base Catalog.lean> <tools dir> <out overlay>

Every edit is a content-anchored replacement asserted to match exactly once:

  1. The plain copy/transfer families and traces (`catalogCopyF`, `catalogCopyR`,
     `catalogTransferR`, `catalog_copy_forward`, `catalog_copy_trace`,
     `catalog_transfer_trace`) are replaced by `tools/mapped-block.lean.txt`: the mapped families
     and the one mapped trace lemma, `catalog_transferMap_trace`, with the shared clause lemma
     `catalog_trace_clauses` and the copy-as-transfer lemmas `copyMapTM_step_eq`/`_runFrom_eq`.
  2. The mapped framed block (`copyMapTM_plain`, `transferMapTM_plain`, `copyMapTM_run_ofCfg`,
     `transferMapTM_run_ofCfg`), landed at the end of the file in its own `namespace Turing`, moves
     verbatim to just before `Turing.transferTM_run_ofCfg`'s docstring, so that the plain framed
     rows can derive from it; the emptied namespace block goes.
  3. The two mapped framed theorems are proved from the mapped traces.
  4. `Turing.transferTM_run_ofCfg` and `Turing.copyTM_run_ofCfg` are re-proved from the mapped
     framed rows at the identity map (statements byte-identical).
  5. `Turing.transferTM_spaceUsedByTape` and `Turing.copyTM_spaceUsedByTape` are re-proved through
     the mapped traces at the identity map (statements byte-identical).
  6. Three proof sketches name the row each framed contract now instantiates.
  7. The G2 section's header states the proved shape (one trace lemma for both mapped rows).

The reverse check (`--reverse-check`) is not needed: the freeze is checked by the probe.
"""
import os
import sys

base, tools, out = sys.argv[1:4]
t = open(base, encoding="utf-8").read()


def rep(a, b, n=1):
    global t
    c = t.count(a)
    assert c == n, (a[:80], c)
    t = t.replace(a, b)


# 1. the plain families and traces -> the mapped block
s0 = t.index("/-- Copy and transfer share the framed forward phase: only the destination\n")
s1 = t.index("\n\n/-- The first unequal or terminating cells occur after a common nonblank", s0)
old = t[s0:s1]
for n in ("private def catalogCopyF", "private def catalogCopyR", "private def catalogTransferR",
          "private lemma catalog_copy_forward", "private lemma catalog_copy_trace",
          "private lemma catalog_transfer_trace"):
    assert old.count(n) == 1, n
assert old.count("private ") == 6
block = open(os.path.join(tools, "mapped-block.lean.txt"), encoding="utf-8").read().rstrip("\n")
t = t[:s0] + block + t[s1:]

# 2. move the mapped framed block up
m0 = t.index("\n\nnamespace Turing\n\n/-- The plain copy is the mapped copy at the identity map:")
assert t.endswith("\nend Turing\n")
m2 = t[m0:]
inner = m2[len("\n\nnamespace Turing\n\n"):-len("\n\nend Turing\n")] + "\n\n"
assert inner.count("theorem ") == 4
c0 = inner.index("/-- **§13d G2, the mapped copy, framed**")
t0 = inner.index("/-- **§13d G2, the mapped transfer, framed**")
assert c0 < t0
inner = inner[:c0] + inner[t0:].rstrip("\n") + "\n\n" + inner[c0:t0]
t = t[:m0] + "\n"
ANCHOR = "/-- **Transfer, framed** (design §12.6). From any\n"
rep(ANCHOR, inner + ANCHOR)

# 3. the mapped framed theorems, from the mapped traces
TM_BODY_OLD = """          d.workTapePos j) := by
  sorry

/-- **§13d G2, the mapped copy, framed**"""
TM_BODY_NEW = """          d.workTapePos j) := by
  have htr := catalog_transferMap_trace src dst hne extract merge rest w d hstate hw
  refine ⟨?_, catalog_trace_clauses _ d (fun j => j = src ∨ j = dst) _ _ _ w.length htr
    (fun _ => ⟨rfl, fun _ => rfl⟩) (fun _ => ⟨rfl, fun _ => rfl⟩) ⟨rfl, rfl⟩⟩
  rw [htr]
  simp only [catalogTrace, show ¬2 * w.length + 2 ≤ w.length by omega,
    show ¬2 * w.length + 2 ≤ 2 * w.length + 1 by omega, if_false]
  congr 1
  funext j q
  by_cases hs : j = src
  · subst hs; simp [catalogSweepResidueR, catalogSweepR, catalogSweepF, hne]
  · by_cases hd : j = dst
    · subst hd; simp [catalogSweepResidueR, catalogSweepR, catalogSweepF, hs]
    · simp [catalogSweepResidueR, catalogSweepR, catalogSweepF, hs, hd]

/-- **§13d G2, the mapped copy, framed**"""
rep(TM_BODY_OLD, TM_BODY_NEW)
CM_BODY_OLD = """          d.workTapePos j) := by
  sorry

/-- **Transfer, framed** (design §12.6). From any"""
CM_BODY_NEW = """          d.workTapePos j) := by
  obtain ⟨h1, h2, h3⟩ := transferMapTM_run_ofCfg src dst hne extract merge some w d hstate hw
  simp only [← copyMapTM_runFrom_eq] at h1 h2 h3
  refine ⟨h1.trans ?_, h2, h3⟩
  congr 1
  funext j q
  by_cases hs : j = src
  · subst hs
    simp only [hne, false_and, if_false]
    split_ifs with hq
    · rw [show ∀ o : Option Symbol, o.bind some = o from fun o => by cases o <;> rfl,
        ← hw (q - d.workTapePos j) (by omega) (by omega)]
      congr 1
      omega
    · rfl
  · simp [hs]

/-- **Transfer, framed** (design §12.6). From any"""
rep(CM_BODY_OLD, CM_BODY_NEW)


# 4. the plain framed rows from the mapped ones
TR_OLD = """  constructor
  · rw [catalog_transfer_trace src dst hne w d hstate hw]
    simp [catalogTrace, catalogCopyF, catalogTransferR, catalogCopyR, show ¬2 * w.length + 2 ≤ w.length by omega]
  · constructor
    · intro t ht
      rw [catalog_transfer_trace src dst hne w d hstate hw]
      simp only [catalogTrace]
      split_ifs <;> simp_all [catalogCopyF, catalogTransferR, catalogCopyR] <;> omega
    · intro j t ht
      rw [catalog_transfer_trace src dst hne w d hstate hw]
      simp only [catalogTrace]
      split_ifs <;> simp_all [catalogCopyF, catalogTransferR, catalogCopyR, Finset.mem_Icc] <;> omega
"""
TR_NEW = """  obtain ⟨h1, h2, h3⟩ :=
    transferMapTM_run_ofCfg src dst hne id (fun _ s => s) (fun _ => none) w d hstate hw
  refine ⟨h1.trans ?_, h2, h3⟩
  apply Cfg.ext <;> simp
"""
rep(TR_OLD, TR_NEW)
CP_OLD = """  constructor
  · rw [catalog_copy_trace src dst hne w d hstate hw]
    simp [catalogTrace, catalogCopyF, catalogCopyR, show ¬2 * w.length + 2 ≤ w.length by omega]
  · constructor
    · intro t ht
      rw [catalog_copy_trace src dst hne w d hstate hw]
      simp only [catalogTrace]
      split_ifs <;> simp_all [catalogCopyF, catalogCopyR] <;> omega
    · intro j t ht
      rw [catalog_copy_trace src dst hne w d hstate hw]
      simp only [catalogTrace]
      split_ifs <;> simp_all [catalogCopyF, catalogCopyR, Finset.mem_Icc] <;> omega
"""
CP_NEW = """  obtain ⟨h1, h2, h3⟩ := copyMapTM_run_ofCfg src dst hne id (fun _ s => s) w d hstate hw
  refine ⟨h1.trans ?_, h2, h3⟩
  apply Cfg.ext <;> simp
"""
rep(CP_OLD, CP_NEW)

# 5. the two space lemmas through the mapped traces
rep("""    rw [catalog_transfer_trace src dst hne (w src) (Cfg.ofWords .sweep w) rfl
      (by intro p _ _; simp [Cfg.ofWords])]
    simp only [catalogTrace]
    split_ifs <;> simp only [catalogCopyF, catalogTransferR, catalogCopyR, catalogCfg, Cfg.ofWords] <;>
      (try split_ifs) <;> omega""",
    """    rw [← transferMapTM_plain, catalog_transferMap_trace src dst hne id (fun _ s => s)
      (fun _ => none) (w src) (Cfg.ofWords .sweep w) rfl (by intro p _ _; simp [Cfg.ofWords])]
    simp only [catalogTrace]
    split_ifs <;>
      simp only [catalogSweepF, catalogSweepResidueR, catalogSweepR, Cfg.ofWords] <;>
      (try split_ifs) <;> omega""")
rep("""  rw [catalog_transfer_trace src dst hne (w src) (Cfg.ofWords .sweep w) rfl
      (by intro p _ _; simp [Cfg.ofWords])]
  simp only [catalogTrace]
  split_ifs <;> simp [catalogCopyF, catalogTransferR, catalogCopyR, catalogCfg, Cfg.ofWords, hs, hd]""",
    """  rw [← transferMapTM_plain, catalog_transferMap_trace src dst hne id (fun _ s => s)
    (fun _ => none) (w src) (Cfg.ofWords .sweep w) rfl (by intro p _ _; simp [Cfg.ofWords])]
  simp only [catalogTrace]
  split_ifs <;>
    simp [catalogSweepF, catalogSweepResidueR, catalogSweepR, Cfg.ofWords, hs, hd]""")
rep("""    rw [catalog_copy_trace src dst hne (w src) (Cfg.ofWords .sweep w) rfl
      (by intro p _ _; simp [Cfg.ofWords])]
    simp only [catalogTrace]
    split_ifs <;> simp only [catalogCopyF, catalogCopyR, catalogCfg, Cfg.ofWords] <;>
      (try split_ifs) <;> omega""",
    """    rw [← copyMapTM_plain, copyMapTM_runFrom_eq, catalog_transferMap_trace src dst hne id
      (fun _ s => s) some (w src) (Cfg.ofWords .sweep w) rfl (by intro p _ _; simp [Cfg.ofWords])]
    simp only [catalogTrace]
    split_ifs <;>
      simp only [catalogSweepF, catalogSweepResidueR, catalogSweepR, Cfg.ofWords] <;>
      (try split_ifs) <;> omega""")
rep("""  rw [catalog_copy_trace src dst hne (w src) (Cfg.ofWords .sweep w) rfl
      (by intro p _ _; simp [Cfg.ofWords])]
  simp only [catalogTrace]
  split_ifs <;> simp [catalogCopyF, catalogCopyR, catalogCfg, Cfg.ofWords, hs, hd]""",
    """  rw [← copyMapTM_plain, copyMapTM_runFrom_eq, catalog_transferMap_trace src dst hne id
    (fun _ s => s) some (w src) (Cfg.ofWords .sweep w) rfl (by intro p _ _; simp [Cfg.ofWords])]
  simp only [catalogTrace]
  split_ifs <;>
    simp [catalogSweepF, catalogSweepResidueR, catalogSweepR, Cfg.ofWords, hs, hd]""")

# 6. the plain framed rows' proof sketches name the mapped rows they now instantiate, and the
#    mapped copy's names its derivation from the transfer
rep("""step, as for the plain copy. The routine never branches on the destination, which is why its
old contents are arbitrary. -/""", """step, as for the plain copy. The routine never branches on the destination, which is why its
old contents are arbitrary. Formally the row is `Turing.transferMapTM_run_ofCfg` with
the identity residue `some`: that transfer's runs are the copy's, since its return pass writes
back what it reads. -/""")
rep("""The left delimiter supplies
the final entry step. -/
theorem transferTM_run_ofCfg""", """The left delimiter supplies
the final entry step. Formally the row is `Turing.transferMapTM_run_ofCfg` at the identity
map with the blank residue (§13d G2: one trace family serves both). -/
theorem transferTM_run_ofCfg""")
rep("""guided by the intact source word, whose left delimiter at `-1` is the first
blank met moving left. -/
theorem copyTM_run_ofCfg""", """guided by the intact source word, whose left delimiter at `-1` is the first
blank met moving left. Formally the row is `Turing.copyMapTM_run_ofCfg` at the identity map
(§13d G2: one trace family serves both). -/
theorem copyTM_run_ofCfg""")

# 7. the G2 section header: the mapped framed rows are proved, through one trace lemma
rep("""The fills of the mapped framed rows share the two-pass sweep trace `Turing.catalog_trace_run`
that every sweep row cites (one trace per routine family, as §12.6 established).""",
    """The mapped framed rows share the two-pass sweep trace `Turing.catalog_trace_run` that every
sweep row cites (one trace per routine family, as §12.6 established), through one trace lemma:
the copy is the transfer with the identity residue `some`, whose return pass writes back what it
reads (`Turing.copyMapTM_run_ofCfg`).""")

for gone in ("catalogCopyF ", "catalogCopyR ", "catalogTransferR ", "catalog_copy_forward",
             "catalog_copy_trace", "catalog_transfer_trace"):
    assert gone not in t, gone
open(out, "w", encoding="utf-8").write(t)
print(f"overlay written: {len(t.splitlines())} lines; 1 block replaced, 1 block moved, "
      f"2 + 2 + 2 bodies re-proved, 3 sketches extended, 1 header updated")
