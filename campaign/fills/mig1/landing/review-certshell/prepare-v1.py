"""Prepare one existing proof repair in inert scratch copies; actual source is not edited here."""
from pathlib import Path
import json
import re
OUT=Path(__file__).resolve().parent
ROOT=OUT.parents[4]
text=(OUT/'CertShell-start.lean.txt').read_text()
lo=text.index('private theorem cert_prepare_exists')
hi=text.index('\n\n/-- **The certificate shell**',lo)
proof=text[lo:hi]
proof=proof.replace('have hcapval : cap.val = m + (F₀.k + (S₀.k + (1 + P.k))) := rfl',
'''have hcapval : cap.val = m + (F₀.k + (S₀.k + (1 + P.k))) := by
    simp only [cap, vhostCap_eq, Fin.coe_natAdd, Fin.val_zero, Nat.add_zero]''')
proof=re.sub(r'\bvhostBuffer\b(?=,|\])','vhostBuffer_eq',proof)
proof=re.sub(r'\bvhostBank\b(?=,|\])','vhostBank_eq',proof)
proof=proof.replace('''(Sum.inr SweepPhase.done) rfl rfl
    · intro i''','''(Sum.inr SweepPhase.done)
      (by rw [vhostCfg_state, Cfg.ofWords_state, Option.map_some])
      (vhostCfg_inputPos ..)
    · intro i
      funext p
      rw [vhostCfg_workTapes]''')
proof=proof.replace('''        change FinTM.bufferTape x = FinTM.bufferTape (w₆ vx)
        rw [hfinal]''','''        simp only [Fin.addCases_left]
        rw [← vhostBuffer_eq]
        change FinTM.bufferTape x p = FinTM.bufferTape (w₆ vx) p
        rw [hfinal]''')
proof=proof.replace('''        simp only [vhostCfg, Fin.addCases_right, Cfg.ofWords]
        change FinTM.bufferTape (Function.update (fun _ => []) j u z) =
          FinTM.bufferTape (w₆ (ι (vhostBank z)))
        apply congrArg FinTM.bufferTape''','''        simp only [Fin.addCases_right, Cfg.ofWords_workTapes]
        rw [← vhostBank_eq]
        apply congrArg (fun word => FinTM.bufferTape word p)''')
proof=proof.replace('''        simp [vhostCfg, Cfg.ofWords]
      · intro z
        simp [vhostCfg, Cfg.ofWords]
    · rfl''','''        simp only [vhostCfg_workTapePos, Fin.addCases_left, Cfg.ofWords_inputPos,
          Fin.val_one, Nat.cast_one, sub_self]
      · intro z
        simp only [vhostCfg_workTapePos, Fin.addCases_right, Cfg.ofWords_workTapePos]
    · rw [vhostCfg_output, Cfg.ofWords_output, List.nil_append]''')
assert proof!=text[lo:hi]
plain=text[:lo]+proof+text[hi:]
assert not (OUT/'CertShell-proposed-v1.lean.txt').exists()
(OUT/'CertShell-proposed-v1.lean.txt').write_text(plain)
common=json.loads((ROOT/'campaign/fills/mig1/landing/review-primitives/controls-manifest.json').read_text())['definitions']
extra=['Turing.Cfg.ofWords','Turing.Cfg.mapState','Turing.vhostCfg','Turing.vhostBuffer','Turing.vhostBank','Turing.vhostCap',
       'Turing.vhostEmitTM','Turing.embedSilentCfg','Turing.embedEmitTM','Turing.seamCompTM','Turing.copyTM','Turing.transferTM','Turing.stateWord']
defs=list(dict.fromkeys(common+extra))
guard='section CertPrepareStrict\nattribute [local irreducible] '+' '.join(defs)+'\nattribute [-simp] Turing.Action.apply Turing.Cfg.init Turing.MultiTapeTM.initCfg\n'
doc=plain.rfind('/-- The loader interface,',0,plain.index('private theorem cert_prepare_exists'))
end=plain.index('\n\n/-- **The certificate shell**',doc)
sealed=plain[:doc]+guard+plain[doc:end]+'\nend CertPrepareStrict\n'+plain[end:]
(OUT/'CertShell-strict-v1.lean.txt').write_text(sealed)
(OUT/'seal-inventory.json').write_text(json.dumps(dict(definitions=defs,ordinary_definitions=len(defs),guard_before_docstring_and_header=True,
    unchanged_legacy_helpers_outside_guard=True,default_simp_removed=['Turing.Action.apply','Turing.Cfg.init','Turing.MultiTapeTM.initCfg'],
    notation_exceptions=['Turing.Cfg.Halted is an unsealable reducible abbreviation; no unsafe reducibility is enabled.'],
    no_actual_source_edits_yet=True),indent=2)+'\n')
print('Prepared proposed/strict v1; sealed',len(defs),'definitions before target docstring/header.')
