module

public import RequestProject.Euler.CircularPeriodRotationCovariance
public import RequestProject.Euler.CircularReferenceCompactness

/-! Independent origins of the two material parameters give genuine
nearby periodic reference contours. This identifies the neutral low
directions of the actual return derivative without changing the flow. -/

@[expose] public section

set_option maxHeartbeats 1000000

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) referencePhaseLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) referencePhaseLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

theorem phaseAdmissibleLittleContourFamily_parameterShift {γ : ℝ≥0} {ι : Type} [Fintype ι]
    (Z₀ : ι → ContourC1Space γ) (r : ι → ℝ) (b : ι → ℝ)
    {Z : ι → LittleContourSpace γ} (hZ : IsPhaseAdmissibleLittleContourFamily Z₀ r Z) :
    IsPhaseAdmissibleLittleContourFamily Z₀ r (contourParameterShiftFamilyCLM γ b Z) := by
  obtain ⟨c, hc⟩ := hZ
  refine ⟨b + c, ?_⟩
  have hi : -(b + c) + b = -c := by
    funext i
    simp only [Pi.add_apply, Pi.neg_apply]
    ring
  rw [contourParameterShiftFamilyCLM_add, hi]
  exact hc

theorem finiteContourPhaseFieldTotal_parameterShift {γ : ℝ≥0} {ι : Type} [Fintype ι]
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1)
    (Z₀ : ι → ContourC1Space γ) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (r i)) (g : ι → ℝ)
    (b : ι → ℝ) (Z : ι → LittleContourSpace γ) (hZ : IsPhaseAdmissibleLittleContourFamily Z₀ r Z) :
    finiteContourPhaseFieldTotal hγ hγ1 Z₀ r hr href g (contourParameterShiftFamilyCLM γ b Z) =
      contourParameterShiftFamilyCLM γ b (finiteContourPhaseFieldTotal hγ hγ1 Z₀ r hr href g Z) := by
  obtain ⟨c, hc⟩ := hZ
  have hi : contourParameterShiftFamilyCLM γ (-(b + c)) (contourParameterShiftFamilyCLM γ b Z) =
      contourParameterShiftFamilyCLM γ (-c) Z := by
    rw [contourParameterShiftFamilyCLM_add]
    have hab : -(b + c) + b = -c := by
      funext i
      simp only [Pi.add_apply, Pi.neg_apply]
      ring
    rw [hab]
  have hshift : IsAdmissibleLittleContourFamily Z₀ r
      (contourParameterShiftFamilyCLM γ (-(b + c)) (contourParameterShiftFamilyCLM γ b Z)) := by
    rw [hi]
    exact hc
  rw [finiteContourPhaseFieldTotal_eq_chart hγ hγ1 Z₀ r hr href g (b + c) _ hshift,
    finiteContourPhaseFieldTotal_eq_chart hγ hγ1 Z₀ r hr href g c Z hc]
  unfold finiteContourPhaseFieldChart
  rw [hi]
  exact (contourParameterShiftFamilyCLM_add b c _).symm

theorem circularBanachDomain_parameterShift {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
    (b : Fin 2 → ℝ) {Z : Fin 2 → LittleContourSpace γ} (hZ : Z ∈ circularBanachDomain hγ hγ1) :
    contourParameterShiftFamilyCLM γ b Z ∈ circularBanachDomain hγ hγ1 :=
  phaseAdmissibleLittleContourFamily_parameterShift _ _ b hZ

theorem circularBanachField_parameterShift {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
    (b : Fin 2 → ℝ) {Z : Fin 2 → LittleContourSpace γ} (hZ : Z ∈ circularBanachDomain hγ hγ1) :
    circularBanachField hγ hγ1 (contourParameterShiftFamilyCLM γ b Z) =
      contourParameterShiftFamilyCLM γ b (circularBanachField hγ hγ1 Z) :=
  finiteContourPhaseFieldTotal_parameterShift hγ hγ1 _ _ _ _ _ b Z hZ

theorem circularPeriod_fixes_parameterShift_reference {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {ρ : ℝ}
    {X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hX : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) ρ) period X)
    (b : Fin 2 → ℝ)
    (hW : contourParameterShiftFamilyCLM γ b (littleCircularReference hγ hγ1) ∈
      ball (littleCircularReference hγ hγ1) ρ) :
    X (contourParameterShiftFamilyCLM γ b (littleCircularReference hγ hγ1)) period =
      contourParameterShiftFamilyCLM γ b (littleCircularReference hγ hγ1) := by
  let S := contourParameterShiftFamilyCLM γ b
  let W := S (littleCircularReference hγ hγ1)
  let α : ℝ → Fin 2 → LittleContourSpace γ := fun t => S (littleCircularMaterialContours hγ hγ1 t)
  have hm (t : ℝ) : littleCircularMaterialContours hγ hγ1 t ∈ circularBanachDomain hγ hγ1 :=
    phaseAdmissible_littleCircularMaterialContours hγ hγ1 t
  have hd (t : ℝ) : HasDerivAt α (circularBanachField hγ hγ1 (α t)) t := by
    have h := S.hasFDerivAt.comp_hasDerivAt t (littleCircularMaterialContours_hasDerivAt hγ hγ1 t)
    change HasDerivAt α (S (circularBanachField hγ hγ1 (littleCircularMaterialContours hγ hγ1 t))) t at h
    rw [← circularBanachField_parameterShift hγ hγ1 b (hm t)] at h
    exact h
  have hcont : Continuous α := S.continuous.comp (contDiff_littleCircularMaterialContours hγ hγ1).continuous
  have he : EqOn α (X W) (Icc 0 period) := by
    apply eqOn_of_banachODE_open (isOpen_phaseAdmissibleLittleContourFamilies _ _)
      (contDiffOn_finiteContourPhaseFieldTotal hγ hγ1 _ _ _ _ _ 1)
      hcont.continuousOn (hX.continuous W hW)
      (fun t _ => circularBanachDomain_parameterShift hγ hγ1 b (hm t)) (hX.mem W hW)
      (fun t _ => hd t)
      (fun t ht => hX.hasDerivAt W hW t ⟨ht.1, ht.2.le⟩)
    change S (littleCircularMaterialContours hγ hγ1 0) = X W 0
    rw [littleCircularMaterialContours_zero, hX.initial W hW]
  calc
    _ = α period := (he ⟨by unfold period; positivity, le_rfl⟩).symm
    _ = _ := by
      dsimp only [α]
      rw [littleCircularMaterialContours_period, littleCircularMaterialContours_zero]

end Euler2D

end
