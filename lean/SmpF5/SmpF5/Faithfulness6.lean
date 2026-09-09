import SmpF5.FamState6
import SmpF5.FamGates6
import SmpF5.FamTrans6
import SmpF5.FamSelect6
import SmpF5.Units6
import SmpF5.FirstApp6
import SmpF5.SplitList6

/-!
# Faithfulness of the order-6 cube formulas (plan §6 assembly, §7 L7.1, §1/§3.4)

Assembles the layer-1 results into the three facts `Bridge6.lean` needs:

* `schedCNF_sat`: the base formula `schedCNFn 6 k` is satisfied by the
  witness assignment `tau6 k S idxs` — the twelve family lemmas of
  `FamState6`, `FamTrans6`, `FamGates6` and `FamSelect6`, one per summand of
  `schedCNFn` (plan §6).
* `cube_faithful6` (L7.1): a legal schedule `S` of at most 15 steps with
  `49 ≤ stableCount6 (readoffS S)` makes every well-formed cube fitting `S`
  satisfiable at target 49 (witness `tau6 49 S (idxsOf (readoffS S))`, the
  units by `Units6`).
* `exists_canonical_schedule` (the witness chain of plan §1/§3.4 and
  `docs/history/PLAN-2026-09-08.md` A): from `49 ≤ stableCount6 I` to a legal, first-appearance
  canonical schedule `S'` with `49 ≤ stableCount6 (readoffS S')`. The chain
  is `validity_unconditional`'s (`WRelabel6.lean`) up to `S := chainSched J`,
  then `σ := sigmaOf S`, `S' := relabelSched σ S` (`Legal_relabel`,
  `firstApp_relabel`), and the count chain
  `49 ≤ sc I = sc J = sc (relabel6 σ J) ≤ sc (readoffS S')`
  (`stableCount6_wrelabel6`, `stableCount6_relabel6`,
  `sc_le_readoffS_relabelSched`). `readoffS` is never assumed
  relabel-equivariant: the bridge is re-instantiated at `relabel6 σ J`.
* `f6_upper_of_unsat_of_coverage`: the upper bound `stableCount6 I ≤ 48`
  from the certificates, conditional on the coverage statement that
  `Coverage6.fits_final` will discharge in `Bridge6.lean` (this file does
  not import `Coverage6`).

Deviations from the task statement: none in the lemma statements. One
extra import, `SmpF5.SplitList6`, because `Cubes6.finalCubes` (used only in
`f6_upper_of_unsat_of_coverage`) is defined there; the module is built and
already imported by `SmpF5.lean`.
-/

open SchedCNF6

/-! ## The base formula -/

/-- Plan §6: `schedCNFn 6 k` is satisfied by `tau6 k S idxs`. The hypotheses
are exactly the union of what the twelve family lemmas need. -/
theorem schedCNF_sat {k : Nat} {S : List (List Nat)} {idxs : List Nat}
    (hL : Legal S) (hlen : S.length ≤ 15) (hk : k ≤ idxs.length)
    (hmem : ∀ i ∈ idxs, i < 720) (hpair : idxs.Pairwise (· < ·))
    (hstab : ∀ i ∈ idxs, i < 720 ∧ isStable6 (readoffS S) ((permsN 6).getD i []) = true) :
    (schedCNFn 6 k).all (evalClause (tau6 k S idxs)) = true := by
  show (initClauses (layout 6) ++ matchingClauses (layout 6) ++ stepClauses (layout 6) ++
      transitionClauses (layout 6) (cyclicShapes 6) ++ beforeClauses (layout 6) ++
      neitherClauses (layout 6) ++ pmClauses (layout 6) ++ beforeWClauses (layout 6) ++
      pwClauses (layout 6) ++ selectorClauses (layout 6) k ++ ladderClauses (layout 6) k ++
      blockClauses (layout 6) k (permsN 6)).all (evalClause (tau6 k S idxs)) = true
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨init_sat k S idxs, matching_sat hL.1⟩, step_sat hL.1 hlen⟩,
    transition_sat hL hlen⟩, before_sat⟩, neither_sat⟩, pm_sat⟩, beforeW_sat⟩, pw_sat⟩,
    selector_sat hk hmem⟩, ladder_sat hk hpair⟩, block_sat6 hL hlen hk hstab⟩

/-! ## L7.1: a fitting cube is satisfiable -/

/-- Plan §7 L7.1: a legal schedule of at most 15 steps whose read-off
instance has at least 49 stable matchings satisfies the formula of every
well-formed cube that fits it, at target 49. Witness:
`tau6 49 S (idxsOf (readoffS S))`. -/
theorem cube_faithful6 {S : List (List Nat)} (hL : Legal S) (hlen : S.length ≤ 15)
    {c : Cubes6.Cube} (hc : Cubes6.CubeWF c) (hf : Cubes6.Fits c S)
    (h49 : 49 ≤ stableCount6 (readoffS S)) :
    Satisfiable (Cubes6.cubeFormula 49 c) := by
  refine ⟨tau6 49 S (idxsOf (readoffS S)), ?_⟩
  have hk : 49 ≤ (idxsOf (readoffS S)).length := by
    rw [idxsOf_length]; exact h49
  exact cubeFormula_sat_of
    (schedCNF_sat hL hlen hk (idxsOf_lt _) (idxsOf_pairwise _)
      (fun i hi => ⟨idxsOf_lt _ i hi, idxsOf_stable _ i hi⟩))
    (prefixUnits_sat hL.1 hlen hc hf) (stopUnits_sat hlen hc hf)

/-! ## The witness chain (plan §1, §3.4; `docs/history/PLAN-2026-09-08.md` A) -/

/-- A positive stable count means the stable-matching list is nonempty. -/
theorem sms6_ne_nil_of_pos {I : Inst6} {n : Nat} (h : n + 1 ≤ stableCount6 I) :
    sms6 I ≠ [] := by
  intro hnil
  have h0 : stableCount6 I = 0 := by
    unfold stableCount6; rw [hnil]; rfl
  omega

/-- The chain from a man-optimal-identity instance `J`: `S := chainSched J`,
`σ := sigmaOf S`, `S' := relabelSched σ S` is legal, first-appearance
canonical, and its read-off has at least `stableCount6 J` stable matchings
(`stableCount6_relabel6` + `sc_le_readoffS_relabelSched`). -/
theorem exists_canonical_schedule_of_manOpt {J : Inst6} (hWFJ : WF6 J = true)
    (hneJ : sms6 J ≠ []) (hmo : manOpt J = idRow6) :
    ∃ S : List (List Nat), Legal S ∧ (∀ t, Cubes6.canonAtB S t = true) ∧
      stableCount6 J ≤ stableCount6 (readoffS S) := by
  have hLS : Legal (chainSched J) := Legal_chainSched hWFJ hneJ hmo
  have hp : (sigmaOf (chainSched J)).Perm idRow6 := sigmaOf_perm hLS.1
  refine ⟨relabelSched (sigmaOf (chainSched J)) (chainSched J), Legal_relabel hp hLS,
    firstApp_relabel hLS.1, ?_⟩
  rw [← stableCount6_relabel6 hp J]
  exact sc_le_readoffS_relabelSched hWFJ hneJ hmo hp

/-- Plan §1/§3.4, `docs/history/PLAN-2026-09-08.md` A: every well-formed instance with at least 49
stable matchings yields a legal, first-appearance canonical schedule whose
read-off instance also has at least 49. Mirrors `validity_unconditional`
(`WRelabel6.lean`): `J := wrelabel6 (invMatch (manOpt I)) I` has
`WF6 J`, `manOpt J = idRow6`, `stableCount6 J = stableCount6 I`; then
`exists_canonical_schedule_of_manOpt`. -/
theorem exists_canonical_schedule {I : Inst6} (hWF : WF6 I = true)
    (h49 : 49 ≤ stableCount6 I) :
    ∃ S : List (List Nat), Legal S ∧ (∀ t, Cubes6.canonAtB S t = true) ∧
      49 ≤ stableCount6 (readoffS S) := by
  have hne : sms6 I ≠ [] := sms6_ne_nil_of_pos h49
  have hμ0 : manOpt I ∈ sms6 I := (manOpt_spec hWF hne).1
  have hp0 : (invMatch (manOpt I)).Perm idRow6 := invMatch_perm (mem_sms6_perm hμ0)
  have hWFJ : WF6 (wrelabel6 (invMatch (manOpt I)) I) = true := WF6_wrelabel6 hp0 hWF
  have hmo : manOpt (wrelabel6 (invMatch (manOpt I)) I) = idRow6 := manOpt_wrelabel6 hWF hne
  have hcnt : stableCount6 (wrelabel6 (invMatch (manOpt I)) I) = stableCount6 I :=
    stableCount6_wrelabel6 hp0 I
  have hneJ : sms6 (wrelabel6 (invMatch (manOpt I)) I) ≠ [] :=
    sms6_ne_nil_of_pos (n := 48) (by omega)
  obtain ⟨S, hLS, hcan, hle⟩ := exists_canonical_schedule_of_manOpt hWFJ hneJ hmo
  exact ⟨S, hLS, hcan, by omega⟩

/-! ## The upper bound, conditional on coverage -/

/-- The certificates give `f(6) ≤ 48`, given that every legal canonical
schedule is covered by a well-formed cube of `finalCubes`
(`Coverage6.fits_final`, discharged in `Bridge6.lean`). -/
theorem f6_upper_of_unsat_of_coverage
    (Hcov : ∀ S, Legal S → (∀ t, Cubes6.canonAtB S t = true) →
      ∃ c ∈ Cubes6.finalCubes, Cubes6.Fits c S ∧ Cubes6.CubeWF c)
    (H : ∀ c ∈ Cubes6.finalCubes, ¬ Satisfiable (Cubes6.cubeFormula 49 c)) :
    ∀ I : Inst6, WF6 I = true → stableCount6 I ≤ 48 := by
  intro I hWF
  by_contra hlt
  have h49 : 49 ≤ stableCount6 I := by omega
  obtain ⟨S, hLS, hcan, h49'⟩ := exists_canonical_schedule hWF h49
  obtain ⟨c, hc, hf, hcWF⟩ := Hcov S hLS hcan
  exact H c hc (cube_faithful6 hLS (Legal_length_le_15 hLS) hcWF hf h49')
