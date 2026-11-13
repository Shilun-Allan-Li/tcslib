#!/usr/bin/env bash
# Grep receipts for groups R, B and L, at the issue base (git grep on the base commit).
BASE=d3f2290a2c66f614e8807903b89ac595086578b3
cd /workspace/folds
run() { echo "### $1"; echo "\$ git grep -nE '$2' $BASE -- TCSlib audits"; git grep -nE "$2" $BASE -- TCSlib audits | sed "s/^$BASE://" ; echo; }
run R1-fin-readers 'def fin[A-Z][A-Za-z]* |fields_finInput|polyTimeComputable_finFields|pairFstD \(pairSndD \(pairSndD w\)\)'
run R2-round-readers 'def (rd[A-Z][A-Za-z]*|rState|rIdx|rQuery|rLog|rS|rI|rX|rL|rU|rZ|rW) |fields_input'
run R2-bodies 'pairFstD \(pairFstD \(pairSndD \(pairSndD w\)\)\)|pairSndD \(pairFstD \(pairSndD \(pairSndD w\)\)\)|pairSndD \(pairSndD \(pairSndD w\)\)'
run R3-answer 'pairSndD \(pairSndD \(pairFstD \((rL|rdLog|rLog) w\)\)\)|def (rdAns|rAns|rFwd|rY) '
run B1-chunks 'def (chunkAt|coinBlock|chunk|block)[A-Za-z]* |\(w\.drop \(i \* k\)\)\.take k|\(r\.drop \(i \* B\)\)\.take B'
run B2-windows 'ofFn_block|take_drop_ofFn_blocks|ofFn_nthCt|coinBlock_flatten|chunkAt_flatten|ofFn_chunk|ofFn_halves|drop \(i \* [a-zA-Z.()]*\)\)\.take'
run B3-aliases 'EnsembleLemmas\.blocks|def blocks|blocks_eq|private def blocks'
run L1-lists 'flatMap_range_drop|ofFn_natAdd_eq_drop|decide_map_ofFn|length_flatten_map_const|length_flatten_map_range|ofFn_eq_map_range'
run L2-padFin 'padFin_append_split|getD_append_right'
run L3-seeds 'seedEquiv|coinsEquivPoly rfl n\)\.prodCongr'
run L4-padL 'ofFn_padFin_eq_padL'
