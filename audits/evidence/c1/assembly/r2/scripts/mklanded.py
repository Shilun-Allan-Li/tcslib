"""Landing forms and cut checks of the C1-A unit, round 2 (read-only on the sources; stdlib only).

Usage: python3 -I mklanded.py <tip source tree> <unit.lean> <outdir>

The unit holds Part E (for `Build/Embed.lean`, with an evidence proof between the
`EVIDENCE PROOF` markers and its landing proof on the `-- @landing-proof` line) and Part N (for
`Build/NDHost.lean`). This script writes, under <outdir>:

  parts/EmbedCap.landing.lean.txt   Part E's declaration as it lands: its docstring and statement
                                    copied verbatim from the unit, then `:= by` and the landing
                                    proof (asserted: the statement is the unit's, character for
                                    character).
  landed/TCSlib/Complexity/TuringMachine/Build/Embed.lean
                                    the tip's file with Part E's declaration inserted after
                                    `embedEmitCfg_selected_pos`, and two comment edits.
  landed/TCSlib/Complexity/TuringMachine/Build/NDHost.lean
                                    the tip's file, `import ...Build.Catalog`, Part N appended,
                                    and the module docstring edits of round 1 (plus one bullet).
  landed/TCSlib/Complexity/SpaceComplexity/Inclusions.lean
                                    the tip's file with `b2b_capture_shape`'s capture fields
                                    proved by the export (asserted edits; nothing else changes).
  cut/Embed.check.lean              = the landed Embed (an insertion; its closure is unchanged).
  cut/NDHost.check.lean             the tip's NDHost byte for byte, the Catalog import, the
                                    *shim* (Part E as in the unit: the export with its evidence
                                    proof, standing in for the landed Embed, which the snapshot
                                    lacks), and Part N.
  cut/NDHost.landed+shim.check.lean the landed NDHost with the shim before Part N.
  cut/Inclusions.check.lean         the landed Inclusions with the shim after its options.
Every edit is asserted to match exactly once.
"""
import os
import re
import sys

base, unit, out = sys.argv[1], sys.argv[2], sys.argv[3]
U = open(unit, encoding="utf-8").read()
HEADER = "/-! ════"
starts = [m.start() for m in re.finditer(r"^/-! ════", U, re.M)]
assert len(starts) == 2, starts
partE, partN = U[starts[0]:starts[1]], U[starts[1]:]
assert "-- @landing TCSlib.Complexity.TuringMachine.Build.Embed\n" in partE
assert "-- @landing TCSlib.Complexity.TuringMachine.Build.NDHost\n" in partN


def body_after_imports(part):
    lines = part.split("\n")
    last = max(i for i, l in enumerate(lines) if l.startswith("-- @imports ") or
               l.startswith("-- @landing-proof"))
    return "\n".join(lines[last + 1:]).strip("\n") + "\n"


shim = body_after_imports(partE)          # namespace Turing … end Turing, evidence proof
bodyN = body_after_imports(partN)
proof_line = [l for l in partE.split("\n") if l.startswith("-- @landing-proof")]
assert len(proof_line) == 1
landing_proof = proof_line[0][len("-- @landing-proof"):].strip()
# Part E's declaration: from its docstring to `:= by`
i0 = shim.index("/-- **The silent transport's capture tape.**")
i1 = shim.index(":= by\n", i0) + len(":= by\n")
decl_head = shim[i0:i1]
ev0 = shim.index("  -- EVIDENCE PROOF BEGIN", i1)
ev1 = shim.index("  -- EVIDENCE PROOF END\n", ev0) + len("  -- EVIDENCE PROOF END\n")
assert shim[i1:ev0] == "", "the evidence proof must follow `:= by` directly"
landingE = decl_head + "  " + landing_proof + "\n"
stmt = decl_head[decl_head.index("theorem embedSilentCfg_cap"):]
assert landingE.count(stmt) == 1 and shim.count(stmt) == 1

edits = lambda text, pairs: _apply(text, pairs)


def _apply(text, pairs):
    for o, n in pairs:
        assert text.count(o) == 1, o[:90]
        text = text.replace(o, n)
    return text


# ---- Embed
emb = open(os.path.join(base, "TCSlib/Complexity/TuringMachine/Build/Embed.lean"),
           encoding="utf-8").read()
anchor = ("    (embedEmitCfg ι tapes heads pre c).workTapePos (ι i) = c.workTapePos i := by\n"
          "  simp [embedEmitCfg, embedSlot_selected]\n")
landedE = _apply(emb, [
    (anchor, anchor + "\n" + landingE),
    ("""`embedSlot_selected` is private. These four projections export the
selected-tape fields of the two configuration transports.""",
     """`embedSlot_selected` is private. These four projections export the
selected-tape fields of the two configuration transports; `Turing.embedSilentCfg_cap`, after
them, exports the silent transport's capture field (the C1-A assembly gate, finding M1)."""),
    ("""* `Turing.embedSilentTM_runFrom`, `Turing.embedEmitTM_runFrom` — lockstep:""",
     """* `Turing.embedSilentCfg_cap` — the silent transport's capture tape and head, off the
  selection (the C1-A assembly gate's export, 2026-10-14).
* `Turing.embedSilentTM_runFrom`, `Turing.embedEmitTM_runFrom` — lockstep:"""),
])

# ---- NDHost
nd = open(os.path.join(base, "TCSlib/Complexity/TuringMachine/Build/NDHost.lean"),
          encoding="utf-8").read()
imp = "import TCSlib.Complexity.TuringMachine.Nondeterministic\n"
assert nd.count(imp) == 1 and nd.endswith("end Turing\n")
cutN = nd.replace(imp, imp + "import TCSlib.Complexity.TuringMachine.Build.Catalog\n") + \
    "\n" + shim + "\n" + bodyN
withimp = nd.replace(imp, imp + "import TCSlib.Complexity.TuringMachine.Build.Catalog\n")
landedN = _apply(withimp + "\n" + bodyN, [
    ("# The nondeterministic phase host and the choice writer\n",
     "# The nondeterministic phase host, the choice writer, and the guess-then-run assembly\n"),
    ("""  the diagonalizer; the controller flavor, the linear normal form's display guess.
""", """  the diagonalizer; the controller flavor, the linear normal form's display guess.
* **The guess-then-run assembly** `Turing.guessRunTM` composes the phase host over a
  deterministic setup, the bounded writer, a rewind by the catalog's `Turing.skipTM` and
  `Turing.skipBackTM`, a deterministic run ending in a live verdict, and a verdict leaf (ruling 2
  of the C1 host-contracts gate). Its contract identifies the writer's word, transfers the
  deterministic phases, and gives all-branch halting and exact-budget acceptance; with the
  interpreter core run silently (`Turing.embedSilentTM`), the core's precondition and live
  verdicts (`Turing.guessRunTM_silent_spec`).
"""),
    ("""* `Turing.NDWriterState`, `Turing.ndWriterTM` — the choice writer. [AB09, §2.1.2]
""", """* `Turing.NDWriterState`, `Turing.ndWriterTM` — the choice writer. [AB09, §2.1.2]
* `Turing.GuessRunPhase`, `Turing.guessRunPhases`, `Turing.guessRunRed`, `Turing.guessRunTM` —
  the guess-then-run host. [AB09, §2.1.2, proof of Theorem 2.6]
* `Turing.guessRunCfg`, `Turing.streamStartCfg` — the run's entry configuration after a guess,
  and the interpreter core's start configuration.
"""),
    ("""* `Turing.ndWriterTM_run_block` — the bounded flavor's contract (sorried).
""", """* `Turing.ndWriterTM_run_block` — the bounded flavor's contract (sorried).
* `Turing.guessRunTM_runWith_handoff`, `Turing.guessRunTM_runWith_handoff_state`,
  `Turing.guessRunTM_runWith_live`, `Turing.guessRunTM_runWith`,
  `Turing.guessRunTM_haltsWithin`, `Turing.guessRunTM_accepts_iff` — the guess-then-run assembly
  (proved modulo `Turing.ndWriterTM_run_block`); `Turing.guessRunTM_runWith_setup_halt` — a
  halting setup (proved).
* `Turing.guessRunCfg_clean` (proved), `Turing.guessRunTM_silent_spec` (proved modulo the
  writer) — the interpreter core's interface: precondition, emission capture, live verdicts.
"""),
    ("""  Cambridge University Press, 2009. (§2.1.2: an NDTM chooses one of its two transition
  functions at every step.)
""", """  Cambridge University Press, 2009. (§2.1.2: an NDTM chooses one of its two transition
  functions at every step; the proof of Theorem 2.6: guess a string, then verify it
  deterministically; Exercise 2.6.)
"""),
])
assert landedN.endswith("\n" + bodyN)
landedNshim = landedN[:-len(bodyN)] + shim + "\n" + bodyN

# ---- Inclusions
inc = open(os.path.join(base, "TCSlib/Complexity/SpaceComplexity/Inclusions.lean"),
           encoding="utf-8").read()
landedI = _apply(inc, [
    ("""projections; elsewhere use the frame theorem. At the capture tape unfold the
captured-output entry and its head at the word's length. -/
private theorem b2b_capture_shape""",
     """projections; elsewhere use the frame theorem. At the capture tape the captured-output
entry and its head at the word's length are `Turing.embedSilentCfg_cap`. -/
private theorem b2b_capture_shape"""),
    ("""  let d : Cfg m Bool S x := { Cfg.init s x with inputPos := p, output := y }
  have hslot : (List.finRange m).find? (fun j => decide (ι j = cap)) = none := by
    apply List.find?_eq_none.mpr
    intro j _
    simp only [decide_eq_true_eq]
    exact fun hj => hcap ⟨j, hj⟩
  apply Cfg.ext <;> try rfl
""", """  let d : Cfg m Bool S x := { Cfg.init s x with inputPos := p, output := y }
  apply Cfg.ext <;> try rfl
"""),
    ("""    · subst j
      change (match (List.finRange m).find? (fun a => decide (ι a = cap)) with
        | some a => d.workTapes a
        | none => if cap = cap then FinTM.bufferTape ([] ++ d.output) else tapes cap) = _
      simp [hslot, d]
""", """    · subst j
      rw [(embedSilentCfg_cap ι cap hcap tapes (fun _ => 0) [] [] d).1, Function.update_self]
      rfl
"""),
    ("""    · subst j
      change (match (List.finRange m).find? (fun a => decide (ι a = cap)) with
        | some a => d.workTapePos a
        | none => if cap = cap then (([] ++ d.output).length : ℤ) else 0) = _
      simp [hslot, d]
""", """    · subst j
      rw [(embedSilentCfg_cap ι cap hcap tapes (fun _ => 0) [] [] d).2, Function.update_self]
      rfl
"""),
])
opt = "set_option autoImplicit false\n"
assert landedI.count(opt) == 1
cutI = landedI.replace(opt, opt + "\n" + shim)

files = {
    "parts/EmbedCap.landing.lean.txt": landingE,
    "landed/TCSlib/Complexity/TuringMachine/Build/Embed.lean": landedE,
    "landed/TCSlib/Complexity/TuringMachine/Build/NDHost.lean": landedN,
    "landed/TCSlib/Complexity/SpaceComplexity/Inclusions.lean": landedI,
    "cut/Embed.check.lean": landedE,
    "cut/NDHost.check.lean": cutN,
    "cut/NDHost.landed+shim.check.lean": landedNshim,
    "cut/Inclusions.check.lean": cutI,
}
for rel, text in files.items():
    p = os.path.join(out, rel)
    os.makedirs(os.path.dirname(p), exist_ok=True)
    if os.path.exists(p):
        os.remove(p)
    open(p, "w", encoding="utf-8").write(text)
n = lambda t: t.count("\n")
print(f"tip Embed {n(emb)} -> landed {n(landedE)}; tip NDHost {n(nd)} -> landed {n(landedN)} "
      f"(Part N {n(bodyN)}); tip Inclusions {n(inc)} -> landed {n(landedI)}; shim {n(shim)}")
print("Part E statement copied verbatim into the landing text: True")
