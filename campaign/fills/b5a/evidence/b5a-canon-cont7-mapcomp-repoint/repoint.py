"""repoint.py <CodeSimulator.lean>: the private canonGramMapComp re-pointed to Cfg.mapState_mapState (Build/InputRewind)."""
import sys
p = sys.argv[1]; s = open(p, encoding='utf-8').read()
def rep(a, b, n=1):
    global s
    c = s.count(a); assert c == n, (a[:70], c, n); s = s.replace(a, b)
lemma = """/-- Renaming a configuration's control twice is renaming it once along the composite. -/
private lemma canonGramMapComp {M : ℕ} {x : List Bool} {S A B : Type}
    (c : Cfg M Bool S x) (f : S → A) (g : A → B) :
    (c.mapState f).mapState g = c.mapState (fun s => g (f s)) := by
  refine Cfg.ext ?_ ?_ ?_ ?_ ?_
  · rw [Cfg.mapState_state, Cfg.mapState_state, Cfg.mapState_state, Option.map_map]
    rfl
  · rw [Cfg.mapState_inputPos, Cfg.mapState_inputPos, Cfg.mapState_inputPos]
  · funext j z
    rw [Cfg.mapState_workTapes, Cfg.mapState_workTapes, Cfg.mapState_workTapes]
  · funext j
    rw [Cfg.mapState_workTapePos, Cfg.mapState_workTapePos, Cfg.mapState_workTapePos]
  · rw [Cfg.mapState_output, Cfg.mapState_output, Cfg.mapState_output]

"""
rep(lemma, "")
rep("      rw [hcA, canonGramMapComp, canonGramMapComp]\n", "      rw [hcA, Cfg.mapState_mapState, Cfg.mapState_mapState]; rfl\n")
rep("        rw [hcT, canonGramMapComp, canonGramMapComp]\n", "        rw [hcT, Cfg.mapState_mapState, Cfg.mapState_mapState]; rfl\n")
rep("import TCSlib.Complexity.TuringMachine.Build.InputCall\n", "import TCSlib.Complexity.TuringMachine.Build.InputCall\nimport TCSlib.Complexity.TuringMachine.Build.InputRewind\n")
assert 'canonGramMapComp' not in s
open(p, 'w', encoding='utf-8').write(s); print('ok')
