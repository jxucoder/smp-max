#!/usr/bin/env bash
# Build the formal development and check the existing trust boundary.
set -euo pipefail
SMP_REPO=$(cd "$(dirname "$0")/.." && pwd)
cd "$SMP_REPO/lean"
lake build SmpMax export_cnf export_sched_cnf export_cubes6
if grep -rnE '\bsorry\b' SmpMax; then
  echo 'Unexpected sorry in the Lean library' >&2
  exit 1
fi
SMP_CHECK_DIR=$(mktemp -d)
trap 'rm -rf "$SMP_CHECK_DIR"' EXIT
cat > "$SMP_CHECK_DIR/axioms.lean" <<'LEAN'
import SmpMax
#print axioms f5_eq_16_of_unsat
#print axioms bridge
#print axioms chain_complete
#print axioms traj_mem_iff
#print axioms wtraj_nodup
#print axioms total_moves_le_30
#print axioms count_le_of_orderPreserving
#print axioms sc_le_readoffS_chainSched
#print axioms manOpt_wrelabel6
#print axioms validity_unconditional
#print axioms PM_sem
#print axioms PW_sem
#print axioms Legal_length_le_15
#print axioms minFirst_mem_cyclicShapes
#print axioms permsN6_perm_permutations
#print axioms Legal_map_minFirst
#print axioms SchedCNF6.dec_pwVar3
#print axioms firstApp_relabel
#print axioms Legal_relabel
#print axioms sc_le_readoffS_relabelSched
#print axioms exists_canonical_schedule
#print axioms fits_final
#print axioms cube_faithful6
#print axioms dihedral6_count
#print axioms f6_upper_of_unsat
#print axioms f6_eq_48_of_unsat
LEAN
lake env lean "$SMP_CHECK_DIR/axioms.lean" | tee "$SMP_CHECK_DIR/axioms.txt"
python3 - "$SMP_CHECK_DIR/axioms.txt" <<'PY'
import re,sys
text=open(sys.argv[1]).read()
matches=re.findall(r"depends on axioms: \[([^]]*)\]",text)
expected={'propext','Classical.choice','Quot.sound'}
if len(matches)!=26 or any(set(s.split(', '))!=expected for s in matches):
    sys.exit('Unexpected axiom dependency or missing theorem output')
PY
lake env lean checks/FiveWitness.lean | tee "$SMP_CHECK_DIR/witness.txt"
grep -q 'depends on axioms: \[propext\]' "$SMP_CHECK_DIR/witness.txt"
lake env lean SmpMax/Checks/FiveCountCrossCheck.lean | tee "$SMP_CHECK_DIR/cross-check.txt"
grep -q 'mismatches: 0' "$SMP_CHECK_DIR/cross-check.txt"
lake env lean SmpMax/Checks/FourLratPilot.lean
echo 'Lean build, axiom checks, standalone witness, differential count, and LRAT pilot passed.'
