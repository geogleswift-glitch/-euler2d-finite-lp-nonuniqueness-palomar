module

public import RequestProject.Euler.BanachExistingForcedTrajectoryComparison
public import RequestProject.Euler.CircularReferenceCompactness
public import RequestProject.Euler.CircularContourPeriodMap
public import RequestProject.Euler.BanachCompactLipschitzNeighborhood
public import RequestProject.Euler.UniformForcedPeriodSmallness

/-! An already existing actual cell trajectory is compared with the
same isolated flow using only its forcing values on a fixed reference
tube. The tube lies near genuine circular contours and never includes
candidate contours through the inner source. -/

@[expose] public section

set_option maxHeartbeats 6000000
set_option maxRecDepth 4000

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) existingIntervalLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) existingIntervalLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

theorem exists_circular_existing_forced_interval_constants {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {T : ℝ} (hT : 0 < T) :
    ∃ U : Set (Fin 2 → LittleContourSpace γ), IsOpen U ∧
      U ⊆ circularBanachDomain hγ hγ1 ∧
      U ⊆ ⋃ t : ℝ, ball (littleCircularMaterialContours hγ hγ1 t) (cellA / 4) ∧
      ∃ K : ℝ≥0, ∃ r > 0, ∃ δ > 0,
        (∀ t ∈ Icc (0 : ℝ) T, closedBall (littleCircularMaterialContours hγ hγ1 t) r ⊆ U) ∧
        ∀ {ρ ε : ℝ} {X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ},
          IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
            (ball (littleCircularReference hγ hγ1) ρ) T X → 0 ≤ ε →
          ∀ {b : Fin 2 → LittleContourSpace γ},
            b ∈ ball (littleCircularReference hγ hγ1) (min ρ δ) →
          ∀ {y p : ℝ → Fin 2 → LittleContourSpace γ},
            y 0 = b → ContinuousOn y (Icc (0 : ℝ) T) →
            (∀ t ∈ Icc (0 : ℝ) T, HasDerivAt y (circularBanachField hγ hγ1 (y t) + p t) t) →
            (∀ t ∈ Icc (0 : ℝ) T, y t ∈ U) →
            (∀ t ∈ Icc (0 : ℝ) T, ‖p t‖ ≤ ε) →
            ∀ t ∈ Icc (0 : ℝ) T, dist (y t) (X b t) ≤ ε * t * Real.exp ((K : ℝ) * t) := by
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
  have htube (t : ℝ) (_ : t ∈ Icc (0 : ℝ) T) : closedBall (c t) r ⊆ U :=
    (closedBall_subset_cthickening (mem_range_self t) r).trans hrtube
  obtain ⟨δ, hδ, _, _, hsmall, _⟩ := exists_uniform_forced_flow_smallness hr hT K
  refine ⟨U, hU, fun z hz => (hUDV hz).1, fun z hz => (hUDV hz).2,
    K, r, hr, δ, hδ, htube, ?_⟩
  intro ρ ε X hX hε b hb y p hy0 hyc hyd hym hp
  have hX' : IsBanachFlowOn f D (ball (c 0) ρ) T X := by
    simpa only [c, littleCircularMaterialContours_zero] using hX
  have hb' : b ∈ ball (c 0) (min ρ δ) := by
    simpa only [c, littleCircularMaterialContours_zero] using hb
  exact dist_existing_forcedTrajectory_same_flow_le hD hf (fun z hz => (hUDV hz).1)
    (contDiff_littleCircularMaterialContours hγ hγ1).continuous.continuousOn
    (fun t _ => littleCircularMaterialContours_hasDerivAt hγ hγ1 t)
    hT hr hδ hε htube hLip hsmall hX' hb' hy0 hyc hyd hym hp

end Euler2D

end
