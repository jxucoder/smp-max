import SmpF5.WRelabel6
import SmpF5.Cubes6

/-!
# Schedule-level relabeling (plan §3.1–§3.2, §3.4)

`relabelSched σ S` renames every man in every step by `app σ`; men and
women are relabeled by the same `σ`, matching `relabel6 σ` and `mapMu6`.
The definition comes first; the equivariance, legality and count-bridge
lemmas (L3.1–L3.7, L3.12–L3.16) follow below it.
-/

def relabelSched (σ : List Nat) (S : List (List Nat)) : List (List Nat) :=
  S.map (fun st => st.map (app σ))

theorem length_relabelSched (σ : List Nat) (S : List (List Nat)) :
    (relabelSched σ S).length = S.length := by
  simp [relabelSched]
