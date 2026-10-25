module

public import RequestProject.Euler.BanachForcedReturnComparison
public import RequestProject.Euler.CircularReferenceCompactness
public import RequestProject.Euler.CircularContourPeriodMap
public import RequestProject.Euler.BanachCompactLipschitzNeighborhood

/-! The original circular phase field admits a true forced full-period
map. The output is compared to any same original circular flow, including
the flow used by the public unstable graph and ancient solution. -/

@[expose] public section

set_option maxHeartbeats 3500000
set_option maxRecDepth 4000

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) forcedPeriodLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) forcedPeriodLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)
local instance (priority := 2000) forcedPeriodC1_group (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) := Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)

theorem exists_circular_forced_period_comparison_constants {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) :
    ∃ L > 0, ∃ K : ℝ≥0, ∃ r > 0, ∀ J : ℝ≥0, ∀ {δ ε : ℝ},
      0 < δ → 0 ≤ ε →
      δ * Real.exp (2 * (K : ℝ) * period) < r →
      (δ + ε * period) * Real.exp (2 * ((K : ℝ) + J) * period) < r →
      ∀ q : ℝ → (Fin 2 → LittleContourSpace γ) → Fin 2 → LittleContourSpace γ,
      (∀ t ∈ Icc (0 : ℝ) period, LipschitzOnWith J (q t) (ball 0 L)) →
      (∀ Z ∈ ball (0 : Fin 2 → LittleContourSpace γ) L,
        ContinuousOn (fun t => q t Z) (Icc (0 : ℝ) period)) →
      (∀ t ∈ Icc (0 : ℝ) period, ∀ Z ∈ ball (0 : Fin 2 → LittleContourSpace γ) L,
        ‖q t Z‖ ≤ ε) →
      ∃ Y : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ,
        IsNonautonomousBanachFlowOn (fun t Z => circularBanachField hγ hγ1 Z + q t Z)
          (circularBanachDomain hγ hγ1)
          (ball (littleCircularReference hγ hγ1) δ) period Y ∧
        (∀ Z ∈ ball (littleCircularReference hγ hγ1) δ, ∀ t ∈ Icc (0 : ℝ) period,
          Y Z t ∈ ball 0 L) ∧
        (∀ Z ∈ ball (littleCircularReference hγ hγ1) δ, ∀ t ∈ Icc (0 : ℝ) period, ∀ i θ,
          HasDerivAt (fun s => LittleContourSpace.lift γ (Y Z s i) θ)
            (contourBoundaryField circularContourStrengths
              (fun j => LittleContourSpace.lift γ (Y Z t j)) i θ +
              LittleContourSpace.lift γ (q t (Y Z t) i) θ) t) ∧
        ∀ {ρ : ℝ} {X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ},
          IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
            (ball (littleCircularReference hγ hγ1) ρ) period X →
          ∀ Z ∈ ball (littleCircularReference hγ hγ1) (min ρ δ), ∀ t ∈ Icc (0 : ℝ) period,
            dist (Y Z t) (X Z t) ≤ ε * t * Real.exp ((K : ℝ) * t) := by
  let f := circularBanachField hγ hγ1
  let D := circularBanachDomain hγ hγ1
  let c := littleCircularMaterialContours hγ hγ1
  have hD : IsOpen D := isOpen_phaseAdmissibleLittleContourFamilies _ _
  have hf : ContDiffOn ℝ 1 f D :=
    (contDiffOn_finiteContourPhaseFieldTotal hγ hγ1 _ _ _ _ _ (⊤ : ℕ∞)).of_le (by simp)
  have hcK : IsCompact (range c) := isCompact_range_littleCircularMaterialContours hγ hγ1
  have hcD (t : ℝ) : c t ∈ D := phaseAdmissible_littleCircularMaterialContours hγ hγ1 t
  obtain ⟨B, hB⟩ := hcK.isBounded.exists_norm_le
  let L : ℝ := |B| + 1
  have hL : 0 < L := by dsimp only [L]; positivity
  have hcL (t : ℝ) : c t ∈ ball 0 L := by
    apply mem_ball_zero_iff.mpr
    exact (hB _ (mem_range_self t)).trans_lt (by dsimp only [L]; linarith [le_abs_self B])
  obtain ⟨W, hW, hcW, hWD, K, hLip⟩ :=
    exists_lipschitz_open_neighborhood_of_compact (hD.inter isOpen_ball)
      (hf.mono inter_subset_left) hcK (by rintro _ ⟨t, rfl⟩; exact ⟨hcD t, hcL t⟩)
  obtain ⟨r, hr, hrtube⟩ := hcK.exists_cthickening_subset_open hW hcW
  have htube (t : ℝ) (_ht : t ∈ Icc (0 : ℝ) period) : closedBall (c t) r ⊆ W :=
    (closedBall_subset_cthickening (mem_range_self t) r).trans hrtube
  have hWU : W ⊆ D := fun z hz => (hWD hz).1
  have hWL : W ⊆ ball 0 L := fun z hz => (hWD hz).2
  have hp : 0 < period := by unfold period; positivity
  refine ⟨L, hL, K, r, hr, ?_⟩
  intro J δ ε hδ hε hsmall₀ hsmall q hqLip hqc hqbound
  obtain ⟨Y, hY, hYmem, hcompare⟩ := exists_forced_banachFlow_with_same_return_comparison
    hD hf hWU (contDiff_littleCircularMaterialContours hγ hγ1).continuous.continuousOn
    (fun t _ => littleCircularMaterialContours_hasDerivAt hγ hγ1 t)
    hp hr hδ hε htube hLip hsmall₀ hsmall q
    (fun t ht => (hqLip t ht).mono hWL) (fun Z hZ => hqc Z (hWL hZ))
    (fun t ht Z hZ => hqbound t ht Z (hWL hZ))
  have hY' : IsNonautonomousBanachFlowOn (fun t Z => f Z + q t Z) D
      (ball (littleCircularReference hγ hγ1) δ) period Y := by
    simpa only [c, littleCircularMaterialContours_zero] using hY
  refine ⟨Y, hY', ?_, ?_, ?_⟩
  · intro Z hZ t ht
    have hZ' : Z ∈ ball (c 0) δ := by simpa only [c, littleCircularMaterialContours_zero] using hZ
    exact hWL (htube t ht (ball_subset_closedBall (hYmem Z hZ' t ht)))
  · intro Z hZ t ht i θ
    have hd := ((LittleContourSpace.eval γ (θ : ContourCircle)).comp
      (ContinuousLinearMap.proj i)).hasFDerivAt.comp_hasDerivAt t (hY'.hasDerivAt Z hZ t ht)
    change HasDerivAt (fun s => LittleContourSpace.lift γ (Y Z s i) θ)
      (LittleContourSpace.lift γ (circularBanachField hγ hγ1 (Y Z t) i) θ +
        LittleContourSpace.lift γ (q t (Y Z t) i) θ) t at hd
    rw [circularBanachField, lift_finiteContourPhaseFieldTotal hγ hγ1 _ _ _ _ _
      (Y Z t) (hY'.mem Z hZ t ht)] at hd
    exact hd
  · intro ρ X hX Z hZ t ht
    have hX' : IsBanachFlowOn f D (ball (c 0) ρ) period X := by
      simpa only [c, littleCircularMaterialContours_zero] using hX
    apply hcompare hX' Z _ t ht
    simpa only [c, littleCircularMaterialContours_zero] using hZ

end Euler2D

end
