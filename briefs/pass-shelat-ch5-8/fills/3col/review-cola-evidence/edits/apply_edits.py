# apply_edits.py <worktree> [E...]: apply the review's landing edits to the col-a head tree in place.
# Each replacement must match exactly once.
import sys, os
wt = sys.argv[1]; want = set(sys.argv[2:]) or {'E1','E2','E3','E4','E5','E6','E7'}
D = os.path.join(wt, 'TCSlib/Cryptography/ZeroKnowledge')
def sub(path, old, new):
    t = open(path).read()
    n = t.count(old)
    assert n == 1, (path, n, old[:80])
    open(path, 'w').write(t.replace(old, new))

if 'E1' in want:
    f = os.path.join(D, 'ThreeColoring.lean')
    sub(f, "import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.Protocol\n",
        "import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.Protocol\n"
        "import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.ColRepWitness\n"
        "import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.ColRepSound\n")
    sub(f, "  (Lem-127.g, Claim-127.h), and the interactive-proof half of [PS10, Proposition 127.6]\n  (Prop-127.6).\n",
        "  (Lem-127.g, Claim-127.h), and the interactive-proof half of [PS10, Proposition 127.6]\n  (Prop-127.6).\n"
        "* `ColRepWitness` — the decider of `R_3COL` (Def-124.f): the test of `R3COL_witnessRelation`'s\n"
        "  sketch, its correctness, and its polynomial time through a scan of bounded searches.\n"
        "* `ColRepSound` — generic lemmas of the `n|E|`-fold protocol (Prot-127.5, Prop-127.6): the\n"
        "  views of four-move iterations against a challenge verifier, the blocks of a uniform tape,\n"
        "  and `K` edge samplers close to uniform.\n")

W = os.path.join(D, 'ThreeColoring/ColRepWitness.lean')
if 'E2' in want:
    sub(W, """/-- Exclusive or of two one-bit tests is polynomial-time (private copy of
`Complexity.polyTimeComputable_xor` of `Complexity/ClassP/BinaryArith/Basic.lean`, which is
not upstream of this file: `polyTimeComputable_ite` on the first test). -/
private theorem colRep_xor_poly {p q : List Bool → Bool}
    (hp : PolyTimeComputable (fun x => [p x])) (hq : PolyTimeComputable (fun x => [q x])) :
    PolyTimeComputable (fun x => [p x ^^ q x]) :=
  ptc_congr (polyTimeComputable_ite hp (polyTimeComputable_not hq) hq) fun x => by
    cases p x <;> cases q x <;> rfl

""", "")
    sub(W, """  refine ptc_congr (polyTimeComputable_or (colRep_xor_poly hb0 hd0)
    (colRep_xor_poly hb1 hd1)) fun w => ?_""",
        """  refine ptc_congr (polyTimeComputable_or (StateLoop.xor_poly hb0 hd0)
    (StateLoop.xor_poly hb1 hd1)) fun w => ?_""")
    sub(W, "(`getBit_poly`, `colorVal_poly`, `divNum_poly`, `modNum_poly`, `eqTest_poly`). -/",
        "(`getBit_poly`, `colorVal_poly`, `divNum_poly`, `modNum_poly`, `eqTest_poly`,\n`StateLoop.xor_poly`). -/")
if 'E3' in want:
    sub(W, """/-- Two Booleans with exclusive or `false` are equal. -/
private theorem eq_of_xor_eq_false {a b : Bool} (h : (a ^^ b) = false) : a = b := by
  revert h
  cases a <;> cases b <;> decide

""", "")
    sub(W, "      exact eq_of_xor_eq_false hb.1\n", "      exact bne_eq_false_iff_eq.1 hb.1\n")
    sub(W, "      exact eq_of_xor_eq_false hb.2\n", "      exact bne_eq_false_iff_eq.1 hb.2\n")

S = os.path.join(D, 'ThreeColoring/ColRepSound.lean')
if 'E4' in want:
    sub(S, """to the first `K b` bits (`GIZK.pushesUniform_castLE`) followed by the bijection
`(Fin (K b) → Bool) ≃ (Fin K → Fin b → Bool)` (`finProdFinEquiv`, `Equiv.curry`). -/
theorem pushesUniform_blockRead (b K C : ℕ) (h : K * b ≤ C) :
    HardcoreBit.PushesUniform (blockRead b K C h) := by
  let e : (Fin (K * b) → Bool) ≃ (Fin K → Fin b → Bool) :=
    (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl Bool)).trans (Equiv.curry _ _ _)
  have he : ∀ s : Fin (K * b) → Bool, ∀ t j, e s t j = s (finProdFinEquiv (t, j)) := by
    intro s t j
    rfl
  have hc := (GIZK.pushesUniform_castLE (B := Bool) h).comp (HardcoreBit.pushesUniform_equiv e)
  convert hc using 1
  funext r t j
  rw [he, blockRead_eq]""",
        """to the first `K b` bits (`GIZK.pushesUniform_castLE`) followed by the blockwise bijection
`EnsembleLemmas.blocks K b : (Fin (K b) → Bool) ≃ (Fin K → Fin b → Bool)`
(`EnsembleLemmas.blocks_apply`). -/
theorem pushesUniform_blockRead (b K C : ℕ) (h : K * b ≤ C) :
    HardcoreBit.PushesUniform (blockRead b K C h) := by
  have hc := (GIZK.pushesUniform_castLE (B := Bool) h).comp
    (HardcoreBit.pushesUniform_equiv (EnsembleLemmas.blocks K b))
  convert hc using 1
  funext r t j
  rw [EnsembleLemmas.blocks_apply, blockRead_eq]""")

P = os.path.join(D, 'ThreeColoring/Protocol.lean')
if 'E5' in want:
    sub(P, """**Proof sketch.** `mem_iff` is `mem_L3COL_iff`; `bounded` with `p := 2 · var`
(`length_encColoring`, `length_encGraph`, `n ≤ n²`); `decidable` with
`T ⟨x, y⟩ := decide (x = encGraph (decGraph x).2 ∧ y = encColoring (decColoring n y) ∧
ProperColoring (decGraph x).2 (decColoring n y))`, correct by `decGraph_encGraph` and
`decColoring_encColoring`, and polynomial-time by `polyTimeComputable_pairEq` on the
re-encodings (`polyTimeComputable_blockMap`, `polyTimeComputable_iterateEmit`) and a scan of
the `n²` entries for the colouring test (`polyTimeComputable_iterate` with an accumulated
conjunction). -/""",
        """**Proof sketch.** `mem_iff` is `mem_L3COL_iff`; `bounded` with `p := 2 · var`
(`length_encColoring`, `length_encGraph`, `n ≤ n²`); `decidable` is `ColRep.R3COL_decidable`
(`ThreeColoring/ColRepWitness.lean`) with
`T ⟨x, y⟩ := decide (x = encGraph (decGraph x).2 ∧ y = encColoring (decColoring n y) ∧
ProperColoring (decGraph x).2 (decColoring n y))` (`ColRep.r3colTest`), correct by `R3COL_iff`,
`decGraph_encGraph` and `decColoring_encColoring`. It is polynomial-time because it agrees with a
scan form, with `n = √|x|` (`ColRep.decGraph_fst`): `|x| = n²`
(`ColMachines.encGraph_decGraph_eq_take`); `|y| = 2n` and no vertex `i < n` whose bits `2i`,
`2i + 1` differ from those of its colour value (`getD_encColoring_two_mul`,
`getD_encColoring_two_mul_add_one`, `ColMachines.decColoring_val`); no set entry `j < n²` whose
endpoints `j / n`, `j % n` have equal colour values (`ProperColoring_iff`,
`ColMachines.decGraph_apply`). Each "no" is a bounded search `EncodingMachines.firstIdx` that
finds nothing (`firstIdx_eq_iff`, `polyTimeComputable_firstIdx`), over tests built from
`getBit_poly`, `ColMachines.colorVal_poly` and unary arithmetic. -/""")
if 'E6' in want:
    sub(P, """(the verifier's history is `[com_0, opn_0, …]` and the parity bookkeeping of `colProverRep`
/ `colVerifierRep` reproduces one iteration on each coin block, `exec_succ`; the empty
messages beyond `n|E|` iterations are ignored). Soundness with""",
        """(the verifier's history is `[com_0, opn_0, …]` and the parity bookkeeping of `colProverRep`
/ `colVerifierRep` reproduces one iteration on each coin block, `exec_succ`, through the generic
`ColRep.exec_four_mul`; the empty messages beyond `n|E|` iterations are ignored). Soundness with""")
    sub(P, """`ε N := Real.exp (-(Nat.sqrt N)) + N² (1/2)^N + 2⁻¹^N` (strict clause): for `x = encGraph G`
not colourable with `n ≥ 2`, fix the prover's coins, condition on all `n|E|` edge samplers
being uniform (`statClose_sampleEdgeIdx` per block, `StatClose.prod` iterated,
`StatClose.abs_uprob_sub_le_prod`, union cost `n|E| (1/2)^{|x|} ≤ |x|² (1/2)^{|x|}`), and apply
`uprob_col_cheat_le` with `k = n|E|`, `comF i` the prover's commitment of iteration `i` (a
function of the earlier challenges through `exec`) and `opnF i` its opening: the acceptance""",
        """`ε N := Real.exp (-(Nat.sqrt N)) + N² (1/2)^N + 2⁻¹^N` (strict clause): if `x` is ill formed,
or `n < 2`, the verdict is `[false]` on every tape; for `x = encGraph G` not colourable with
`n ≥ 2`, fix the prover's coins, condition on all `n|E|` edge samplers being uniform
(`statClose_sampleEdgeIdx` per block, `OneWay.statClose_pi` over the coin blocks:
`ColRep.statClose_edgeBlocks`; `StatClose.abs_uprob_sub_le_prod`, union cost
`n|E| (1/2)^{|x|} ≤ |x|² (1/2)^{|x|}`), and apply `uprob_col_cheat_le` with `k = n|E|`, `comF i`
the prover's commitment of iteration `i` (a function of the earlier challenges through `exec`,
`ColRep.exec_four_mul` and `ColRep.chView`) and `opnF i` its opening: the acceptance""")
if 'E7' in want:
    sub(P, """layout) is `ThreeColoring/Machines.lean`, `ThreeColoring/Parties.lean` and
`ThreeColoring/ProtocolProofs.lean`.""",
        """layout) is `ThreeColoring/Machines.lean`, `ThreeColoring/Parties.lean` and
`ThreeColoring/ProtocolProofs.lean`; the decider of `R_3COL` is `ThreeColoring/ColRepWitness.lean`,
and the generic lemmas of the `n|E|`-fold protocol are `ThreeColoring/ColRepSound.lean`.""")
print('applied', sorted(want))
