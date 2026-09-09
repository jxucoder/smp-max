import SmpMax.Six.ReadOff
import Mathlib.Data.List.Permutation

/-!
# Order six: the lower bound `f(6) ≥ 48`

Implements `docs/history/research-plan-2026-09-08.md` §A (file `Lower6.lean`) and
`docs/design/f6-faithfulness.md` §7 L7.4 (the dihedral lower bound needed by
`f6_eq_48_of_unsat`) / §10 risk 5 (kernel-computation cost: the
`stableCount6'` reformulation via `List.permutations'`).

`dihedral6` is the dihedral Latin instance of OEIS A351413 with ranking
matrix (entry = 1-based rank man `i` gives woman `j`)

```
123456
214365
365214
456123
541632
632541
```

Conventions (as in `latin_instance` of `tools/stable_matchings.py`): `mrank[i][j] = entry - 1`
and woman `j` gives man `i` the rank `7 - entry`, i.e.
`wrank[j][i] = 6 - entry`.  Both tables are written out explicitly below;
the repository's brute-force counter (`tools/stable_matchings.py`) gives 48 stable matchings
for this matrix.

`stableCount6` enumerates via `List.permutations`, which Lean's kernel
cannot reduce (well-founded recursion), so the witness count is
established via the structurally-recursive `List.permutations'` and
transported across `List.permutations_perm_permutations'`, exactly as in
`Lower.lean` for order 5.

No statement deviates from the plan.
-/

/-- The dihedral Latin instance of OEIS A351413 (48 stable matchings), as
0-based rank tables.  Row `i` of `mrank` is man `i`'s rank of each woman;
row `j` of `wrank` is woman `j`'s rank of each man. -/
def dihedral6 : Inst6 :=
  ⟨[[0, 1, 2, 3, 4, 5],
    [1, 0, 3, 2, 5, 4],
    [2, 5, 4, 1, 0, 3],
    [3, 4, 5, 0, 1, 2],
    [4, 3, 0, 5, 2, 1],
    [5, 2, 1, 4, 3, 0]],
   [[5, 4, 3, 2, 1, 0],
    [4, 5, 0, 1, 2, 3],
    [3, 2, 1, 0, 5, 4],
    [2, 3, 4, 5, 0, 1],
    [1, 0, 5, 4, 3, 2],
    [0, 1, 2, 3, 4, 5]]⟩

theorem dihedral6_WF : WF6 dihedral6 = true := by decide

/-- Kernel-computable variant of `stableCount6` (structural recursion via
`List.permutations'`). -/
def stableCount6' (I : Inst6) : Nat :=
  (idRow6.permutations'.filter (isStable6 I)).length

theorem stableCount6_eq_stableCount6' (I : Inst6) :
    stableCount6 I = stableCount6' I := by
  unfold stableCount6 sms6 stableCount6'
  exact ((List.permutations_perm_permutations' _).filter _).length_eq

/-- The dihedral instance has exactly 48 stable matchings (kernel
computation: 720 permutations × 36 pair checks). -/
theorem dihedral6_count : stableCount6 dihedral6 = 48 := by
  rw [stableCount6_eq_stableCount6']
  decide

/-- **`f(6) ≥ 48`**: a well-formed order-6 instance with 48 stable
matchings. -/
theorem f6_lower : ∃ I : Inst6, WF6 I = true ∧ stableCount6 I = 48 :=
  ⟨dihedral6, dihedral6_WF, dihedral6_count⟩
