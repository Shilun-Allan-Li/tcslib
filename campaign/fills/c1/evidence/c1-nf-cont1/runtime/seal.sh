#!/usr/bin/env bash
# seal.sh <outdir> <reached-defs.txt> : sealed module copy + sealed/unsealed controls
set -u
source ~/.elan/env
cd /home/user/tcslib
OD="$1"; REACHED="$2"; mkdir -p "$OD"
MOD=TCSlib/Complexity/ClassNP/NDNormalForm.lean
# seal set: the review's 223 plus the reached TCSlib definitions that are not structure
# projections or casesOn recursors
grep -vE '\.(casesOn)$' "$REACHED" | grep -vE '^Turing\.(Action\.(inputTape|output|state|workTapes)|Cfg\.(inputPos|output|state|workTapePos|workTapes)|FinNDTM\.(State|decEqState|fintypeState|k|tm)|MultiTapeTM\.(q₀|tr)|NDTM\.(q₀|tr))$' \
  | cat - scratch/seal223.txt | sort -u > "$OD/seal-set.txt"
N=$(wc -l < "$OD/seal-set.txt")
{ echo "attribute [-simp] Turing.Action.apply Turing.Cfg.init Turing.MultiTapeTM.initCfg Turing.NDTM.initCfg"
  echo "attribute [local irreducible]"; sed 's/^/  /' "$OD/seal-set.txt"; } > "$OD/seal-block.lean"
# the sealed module copy: the block right before the first new private (after line 704)
{ head -n 704 "$MOD"; echo; echo "-- SEAL ($N definitions)"; cat "$OD/seal-block.lean"; tail -n +705 "$MOD"; } > scratch/NFSeal.lean
cp scratch/NFSeal.lean "$OD/NFSeal.lean"
bash scripts/lean_check_tree.sh scratch/NFSeal > "$OD/seal-module.log" 2>&1; echo "exit: $?" >> "$OD/seal-module.log"
# controls
HDR=$(sed -n '/^import/,/^section Controls/p' campaign/fills/c1/inputs/c1-fill-nf-cont1/NFContSealControl_sealed.lean.txt | grep -v '^section Controls')
for mode in unsealed sealed; do
  { echo "/- Seal controls for the owned module's seal ($N definitions): one delta goal per sealed"
    echo "definition, logging CONTROL_PASS or CONTROL_FAIL. Expected: unsealed, every control passes;"
    echo "sealed, every control fails. A probe record, not library code. -/"
    echo "import TCSlib.Complexity.ClassNP.NTIME"
    echo "import TCSlib.Complexity.TuringMachine.NDCodes"
    echo "$HDR"
    cat <<'LEAN'

open Lean Elab Command Meta in
elab "#ctl_use " id:ident " : " t:term : command => do
  let ok ← liftTermElabM do
    try
      Term.withoutErrToSorry do
        let goal ← Term.elabType t
        let proof ← Term.elabTermEnsuringType (← `(by decide)) goal
        Term.synthesizeSyntheticMVarsNoPostponing
        return !(← instantiateMVars proof).hasSorry
    catch _ => return false
  logInfo m!"{if ok then "CONTROL_PASS" else "CONTROL_FAIL"} use {id.getId}"
LEAN
    echo; echo "section Controls"
    if [ "$mode" = sealed ]; then cat "$OD/seal-block.lean"; else echo "attribute [-simp] Turing.Action.apply Turing.Cfg.init Turing.MultiTapeTM.initCfg Turing.NDTM.initCfg"; fi
    while read -r d; do
      case "$d" in
        Turing.FinTM.sweepFold|Turing.NDTM.runWith|Turing.codeReadUnary|Turing.codeReadVec|Turing.codeSkipRepeat|Turing.incFixed|Turing.mealyRun|Turing.pairDecode|Turing.unaryTokenSplit|Turing.workReadsK)
          echo "#ctl_eqn $d" ;;
        Turing.instFintypeSeekPhase) echo "#ctl_use $d : (Finset.univ : Finset Turing.SeekPhase).card = 4" ;;
        Turing.instFintypeSweepPhase) echo "#ctl_use $d : (Finset.univ : Finset Turing.SweepPhase).card = 3" ;;
        Turing.instFintypeScanPhase) echo "#ctl_rfl $d" ;;
        Turing.instFintypeGuessRunPhase) echo "#ctl_use $d : (Finset.univ : Finset Turing.GuessRunPhase).card = 6" ;;
        *) echo "#ctl_rfl $d" ;;
      esac
    done < "$OD/seal-set.txt"
    echo "end Controls"; } > "scratch/NFSealCtl_$mode.lean"
  cp "scratch/NFSealCtl_$mode.lean" "$OD/NFSealCtl_$mode.lean"
  bash scripts/lean_check_tree.sh "scratch/NFSealCtl_$mode" > "$OD/controls-$mode.log" 2>&1; echo "exit: $?" >> "$OD/controls-$mode.log"
  echo "$mode: PASS=$(grep -c 'CONTROL_PASS' "$OD/controls-$mode.log") FAIL=$(grep -c 'CONTROL_FAIL' "$OD/controls-$mode.log")"
done
echo "module: $(grep -c 'error' "$OD/seal-module.log") error lines; $(tail -1 "$OD/seal-module.log")"
