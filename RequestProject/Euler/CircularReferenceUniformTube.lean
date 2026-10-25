module

public import RequestProject.Euler.CircularReferenceCompactness
public import RequestProject.Euler.CircularContourPeriodMap
public import RequestProject.Euler.BanachCompactLipschitzNeighborhood

/-! One genuine self-field Lipschitz constant and reference tube are
chosen before every time horizon and every transfer ratio. This fixes
the quantifier order in the delayed ancestor response estimate. -/

@[expose] public section

set_option maxHeartbeats 3000000
set_option maxRecDepth 4000

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) uniformRefTubeLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) uniformRefTubeLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

theorem exists_circular_reference_uniform_lipschitz_tube {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) :
    ∃ U : Set (Fin 2 → LittleContourSpace γ), IsOpen U ∧
      U ⊆ circularBanachDomain hγ hγ1 ∧
      U ⊆ ⋃ t : ℝ, ball (littleCircularMaterialContours hγ hγ1 t) (cellA / 4) ∧
      ∃ K : ℝ≥0, ∃ r > 0, ∃ L > 0,
        LipschitzOnWith K (circularBanachField hγ hγ1) U ∧
        (∀ t : ℝ, closedBall (littleCircularMaterialContours hγ hγ1 t) r ⊆ U) ∧
        (∀ Z ∈ U, ‖Z‖ ≤ L) := by
  let f := circularBanachField hγ hγ1
  let D := circularBanachDomain hγ hγ1
  let c := littleCircularMaterialContours hγ hγ1
  let V : Set (Fin 2 → LittleContourSpace γ) := ⋃ t : ℝ, ball (c t) (cellA / 4)
  have hD : IsOpen D := isOpen_phaseAdmissibleLittleContourFamilies _ _
  have hV : IsOpen V := isOpen_iUnion (fun _ => isOpen_ball)
  have hf : ContDiffOn ℝ 1 f D :=
    (contDiffOn_finiteContourPhaseFieldTotal hγ hγ1 _ _ _ _ _ (⊤ : ℕ∞)).of_le (by simp)
  have hcK : IsCompact (range c) := isCompact_range_littleCircularMaterialContours hγ hγ1
  have hcD (t : ℝ) : c t ∈ D := phaseAdmissible_littleCircularMaterialContours hγ hγ1 t
  have hcV (t : ℝ) : c t ∈ V := mem_iUnion.mpr
    ⟨t, mem_ball_self (div_pos cellA_pos (by norm_num : (0 : ℝ) < 4))⟩
  obtain ⟨U, hU, hcU, hUDV, K, hLip⟩ :=
    exists_lipschitz_open_neighborhood_of_compact (hD.inter hV)
      (hf.mono inter_subset_left) hcK (by rintro _ ⟨t, rfl⟩; exact ⟨hcD t, hcV t⟩)
  obtain ⟨r, hr, hrtube⟩ := hcK.exists_cthickening_subset_open hU hcU
  obtain ⟨L₀, hL₀, hcL⟩ := hcK.isBounded.subset_closedBall_lt 0 (0 : Fin 2 → LittleContourSpace γ)
  let L := L₀ + cellA / 4 + 1
  have hL : 0 < L := by dsimp only [L]; linarith [cellA_pos]
  refine ⟨U, hU, fun Z hZ => (hUDV hZ).1, fun Z hZ => (hUDV hZ).2,
    K, r, hr, L, hL, hLip,
    fun t => (closedBall_subset_cthickening (mem_range_self t) r).trans hrtube, ?_⟩
  intro Z hZ
  obtain ⟨t, ht⟩ := mem_iUnion.mp (hUDV hZ).2
  have hdist : ‖Z - c t‖ < cellA / 4 := by simpa only [mem_ball, dist_eq_norm] using ht
  have hct : ‖c t‖ ≤ L₀ := mem_closedBall_zero_iff.mp (hcL (mem_range_self t))
  have hn := norm_le_norm_sub_add Z (c t)
  dsimp only [L]
  linarith

end Euler2D

end
