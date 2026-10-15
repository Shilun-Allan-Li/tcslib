"""Write the landed forms of Build/Catalog.lean and Build/Contract/Catalog.lean (read-only on the
base tree and the part files).

Usage: python3 -I mklanded_catalog.py <base tree> <parts dir> <landed root>

Every edit is a content-anchored replacement or insertion asserted to match exactly once.

Build/Catalog.lean:
  1. Part M1 (the mapped tables) is inserted before `Turing.transferTM`'s docstring;
  2. the bodies of `Turing.transferTM` and `Turing.copyTM` become the mapped rows at the
     identity map (a definitional restatement), and each docstring gains one sentence;
  3. the repairs listed in REPAIRS (proofs that unfolded the old tables) are applied;
  4. Part M2 is appended.
Build/Contract/Catalog.lean:
  5. Part C1 (the shared constructor) is inserted before `Turing.clearTM_contract`'s docstring;
  6. `Turing.clearTM_contract`'s body becomes `Turing.sweepContract` applied to clear's clauses,
     its docstring's proof sketch says so, and the proofs of `clearTM_contract_frames` and
     `clearTM_contract_traj` are re-pointed at the shared lemmas;
  7. Part C2 is appended.
"""
import os
import sys

base, parts, out = sys.argv[1:4]
CAT = "TCSlib/Complexity/TuringMachine/Build/Catalog.lean"
CCAT = "TCSlib/Complexity/TuringMachine/Build/Contract/Catalog.lean"


def one(s, a):
    n = s.count(a)
    assert n == 1, f"anchor occurs {n} times: {a[:80]!r}"


def rep(s, a, b):
    one(s, a)
    return s.replace(a, b)


def inner(path, var=False):
    t = open(path, encoding="utf-8").read()
    head = "namespace Turing\n\nvariable {k : ℕ} {Γ : Type}\n\n" if var else "namespace Turing\n\n"
    assert t.startswith(head), path
    t = t[len(head):].rstrip()
    assert t.endswith("end Turing"), path
    return t[: -len("end Turing")].rstrip() + "\n\n"


def outer(path):
    return open(path, encoding="utf-8").read().rstrip("\n") + "\n"


# ---------------------------------------------------------------- Build/Catalog.lean
cat = open(os.path.join(base, CAT), encoding="utf-8").read()
TR_DOC = ("/-- **R3, transfer** (design §12; [Bon26]). Move the word stored on tape\n"
          "`src` to tape `dst`: a forward pass copies cell by cell (both heads in\n"
          "lockstep), the turn at the source's right blank starts the return pass,\n"
          "which erases the source on the way back, and the overshoot to the left\n"
          "blank steps right into the live `done` anchor with both heads at the\n"
          "origin. -/\n")
cat = rep(cat, TR_DOC, inner(os.path.join(parts, "M1.body")) + TR_DOC[:-4] +
          " Its table is the mapped transfer's\n"
          "(`Turing.transferMapTM`, §13d G2) at the identity map with the blank residue. -/\n")
TR_SIG = ("def transferTM {Symbol : Type*} (k : ℕ) (src dst : Fin k) : MultiTapeTM k Symbol "
          "SweepPhase where\n")
CP_DOC_END = "return pass. -/\n"
i = cat.index(TR_SIG)
j = cat.index("\n\n/-- **R3, copy**", i)
old_tr = cat[i:j]
assert old_tr.count("q₀ := .sweep") == 1 and "def copyTM" not in old_tr
cat = rep(cat, old_tr, "def transferTM {Symbol : Type*} (k : ℕ) (src dst : Fin k) : "
          "MultiTapeTM k Symbol SweepPhase :=\n  transferMapTM k src dst id (fun _ s => s) "
          "(fun _ => none)")
CP_DOC = ("the same two-pass sweep as `Turing.transferTM` without the erasure on the\n"
          "return pass. -/\n")
cat = rep(cat, CP_DOC, "the same two-pass sweep as `Turing.transferTM` without the erasure on the\n"
          "return pass. Its table is the mapped copy's (`Turing.copyMapTM`, §13d G2) at the identity\n"
          "map. -/\n")
CP_SIG = ("def copyTM {Symbol : Type*} (k : ℕ) (src dst : Fin k) : MultiTapeTM k Symbol "
          "SweepPhase where\n")
i = cat.index(CP_SIG)
j = cat.index("\n\n/-- **R3, clear**", i)
old_cp = cat[i:j]
assert old_cp.count("q₀ := .sweep") == 1 and "def clearTM" not in old_cp
cat = rep(cat, old_cp, "def copyTM {Symbol : Type*} (k : ℕ) (src dst : Fin k) : "
          "MultiTapeTM k Symbol SweepPhase :=\n  copyMapTM k src dst id (fun _ s => s)")
# repairs: proofs that unfold the plain tables now also unfold the mapped ones
REPAIRS = [
    # (old, new, expected count): the three private trace lemmas whose proofs unfolded the
    # old tables (catalog_copy_forward, catalog_copy_trace, catalog_transfer_trace)
    ("    simp only [copyTM, hs]\n", "    simp only [copyTM, copyMapTM, hs]\n", 3),
    ("  simp only [copyTM, hs]\n", "  simp only [copyTM, copyMapTM, hs]\n", 1),
    ("  · apply Cfg.ext <;> simp [MultiTapeTM.step, copyTM, Action.apply]\n",
     "  · apply Cfg.ext <;> simp [MultiTapeTM.step, copyTM, copyMapTM, Action.apply]\n", 1),
    ("    simp only [transferTM, hs]\n", "    simp only [transferTM, transferMapTM, hs]\n", 3),
    ("  · apply Cfg.ext <;> simp [MultiTapeTM.step, transferTM, Action.apply]\n",
     "  · apply Cfg.ext <;> simp [MultiTapeTM.step, transferTM, transferMapTM, Action.apply]\n", 1),
]
applied = []
for a, b, n in REPAIRS:
    c = cat.count(a)
    assert c == n, (a, c, n)
    cat = cat.replace(a, b)
    applied.append((a.strip(), n))
cat = cat.rstrip("\n") + "\n\n" + outer(os.path.join(parts, "M2.body"))
os.makedirs(os.path.dirname(os.path.join(out, CAT)), exist_ok=True)
open(os.path.join(out, CAT), "w", encoding="utf-8").write(cat)

# ---------------------------------------------------------------- Build/Contract/Catalog.lean
cc = open(os.path.join(base, CCAT), encoding="utf-8").read()
CL_DOC = "/-- **R3 clear as a contract** (the fit test, from `Turing.clearTM_run_ofCfg`): the index is the\n"
cc = rep(cc, CL_DOC, inner(os.path.join(parts, "C1.body"), var=True) + CL_DOC)
cc = rep(cc, "**Proof sketch.** Each field is the corresponding clause of `Turing.clearTM_run_ofCfg`; a fixed\n"
         "head lies in its one-point interval. -/\n",
         "**Proof sketch.** `Turing.sweepContract` with the clauses of `Turing.clearTM_run_ofCfg`. -/\n")
i = cc.index("def clearTM_contract (i : Fin k) (x : List Γ) :")
j = cc.index("\n\n/-- R3 clear frames the cleared word's cells", i)
old_cl = cc[i:j]
assert old_cl.count("where") == 1 and "env w d hd hp u hu j" in old_cl
cc = rep(cc, old_cl, """def clearTM_contract (i : Fin k) (x : List Γ) :
    Contract (clearTM k i) SweepPhase.sweep {some SweepPhase.done} (List Γ) x :=
  sweepContract _ _ _ i (fun j => j = i) x (sweepPost .done i fun _ _ _ _ => none) (fun _ _ => rfl)
    (clearTM_run_ofCfg i)""")
i = cc.index("theorem clearTM_contract_frames (i : Fin k) (x : List Γ) :")
j = cc.index("\n\n/-- **A joint trajectory of R3 clear**", i)
old_fr = cc[i:j]
k0 = old_fr.index(":= by\n")
cc = rep(cc, old_fr, old_fr[:k0] + ":=\n  fun _ _ _ _ _ _ hq => sweep_ite_keep _ _ hq")
cc = rep(cc, "**Proof sketch.** The endpoint blanks a cell only when the cell lies in the footprint; any other\n"
         "cell takes the `else` branch of its definition, which is the start's cell. -/\n",
         "**Proof sketch.** `Turing.sweep_ite_keep` at tape `i`. -/\n")
i = cc.index("theorem clearTM_contract_traj (i : Fin k) (x : List Γ) :")
j = cc.index("\n\nend Turing", i)
old_tj = cc[i:j]
k0 = old_tj.index(":= by\n")
cc = rep(cc, old_tj, old_tj[:k0] + ":=\n  sweepContract_traj _ _ _ _ _ _ _ _ _")
cc = cc.rstrip("\n") + "\n\n" + outer(os.path.join(parts, "C2.body"))
os.makedirs(os.path.dirname(os.path.join(out, CCAT)), exist_ok=True)
open(os.path.join(out, CCAT), "w", encoding="utf-8").write(cc)
print(f"landed Catalog.lean: {len(cat.splitlines())} lines; repairs: {applied}")
print(f"landed Contract/Catalog.lean: {len(cc.splitlines())} lines")
