module

public import RequestProject.Euler.ContourFourthMomentParameterShift
public import RequestProject.Euler.CircularPatchMomentUnstableLinear

/-! The actual strength-weighted fourth moment in global boundary
coordinates, including its derivative along every fourth Fourier mode. -/

@[expose] public section

set_option maxHeartbeats 4000000
set_option maxRecDepth 4000

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory
open scoped NNReal ContDiff BigOperators

namespace Euler2D

local instance (priority := 2000) boundaryFourthC1_group (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) := Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)
local instance (priority := 2000) boundaryFourthC1_space (γ : ℝ≥0) :
    NormedSpace ℝ (ContourC1Space γ) := Submodule.normedSpace (contourC1GraphSubmodule γ)
local instance (priority := 2000) boundaryFourthLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) boundaryFourthLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)
local instance (priority := 2000) boundaryFourthFamily_tower (γ : ℝ≥0) :
    IsScalarTower ℝ ℝ (Fin 2 → LittleContourSpace γ) where
  smul_assoc a b Z := by
    funext i
    change (a * b) • Z i = a • (b • Z i)
    exact (smul_smul a b (Z i)).symm

def circularBoundaryFourthMoment {γ : ℝ≥0} (Z : Fin 2 → LittleContourSpace γ) : ℂ :=
  ∑ i : Fin 2, (circularContourStrengths i : ℂ) * contourFourthMoment γ (Z i).val

theorem contDiff_circularBoundaryFourthMoment (γ : ℝ≥0) :
    ContDiff ℝ ∞ (@circularBoundaryFourthMoment γ) := by
  have hd (i : Fin 2) : ContDiff ℝ ∞ (fun Z : Fin 2 → LittleContourSpace γ =>
      contourFourthMoment γ (Z i).val) :=
    (contDiff_contourFourthMoment γ).comp
      ((LittleContourSpace.inclusion γ).contDiff.comp
        (ContinuousLinearMap.proj i : (Fin 2 → LittleContourSpace γ) →L[ℝ] LittleContourSpace γ).contDiff)
  have hw (i : Fin 2) : ContDiff ℝ ∞ (fun Z : Fin 2 → LittleContourSpace γ =>
      (circularContourStrengths i : ℂ) * contourFourthMoment γ (Z i).val) := contDiff_const.mul (hd i)
  convert (hw 0).add (hw 1) using 1
  funext Z
  simp only [circularBoundaryFourthMoment, Fin.sum_univ_two, Pi.add_apply]

theorem circularBoundaryFourthMoment_parameterShift {γ : ℝ≥0}
    (b : Fin 2 → ℝ) (Z : Fin 2 → LittleContourSpace γ) :
    circularBoundaryFourthMoment (contourParameterShiftFamilyCLM γ b Z) = circularBoundaryFourthMoment Z := by
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact contourFourthMoment_parameterShiftC1 (b i) (Z i).val

theorem fderiv_circularBoundaryFourthMoment_parameterShift {γ : ℝ≥0}
    (b : Fin 2 → ℝ) (Z V : Fin 2 → LittleContourSpace γ) :
    fderiv ℝ (@circularBoundaryFourthMoment γ) (contourParameterShiftFamilyCLM γ b Z)
        (contourParameterShiftFamilyCLM γ b V) = fderiv ℝ (@circularBoundaryFourthMoment γ) Z V := by
  have hd (W : Fin 2 → LittleContourSpace γ) :=
    ((contDiff_circularBoundaryFourthMoment γ).differentiable (by norm_num)).differentiableAt.hasFDerivAt (x := W)
  have hleft := (hd (contourParameterShiftFamilyCLM γ b Z)).comp Z
    (contourParameterShiftFamilyCLM γ b).hasFDerivAt
  have he : (fun W : Fin 2 → LittleContourSpace γ =>
      circularBoundaryFourthMoment (contourParameterShiftFamilyCLM γ b W)) = circularBoundaryFourthMoment :=
    funext (circularBoundaryFourthMoment_parameterShift b)
  change HasFDerivAt (fun W : Fin 2 → LittleContourSpace γ =>
      circularBoundaryFourthMoment (contourParameterShiftFamilyCLM γ b W))
    ((fderiv ℝ (@circularBoundaryFourthMoment γ) (contourParameterShiftFamilyCLM γ b Z)).comp
      (contourParameterShiftFamilyCLM γ b)) Z at hleft
  rw [he] at hleft
  exact congrArg (fun A : (Fin 2 → LittleContourSpace γ) →L[ℝ] ℂ => A V) (hleft.unique (hd Z))

theorem circularBoundaryFourthMoment_reference {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) :
    circularBoundaryFourthMoment (littleCircularReference hγ hγ1) = 0 := by
  unfold circularBoundaryFourthMoment
  have hz (i : Fin 2) : contourFourthMoment γ (littleCircularReference hγ hγ1 i).val = 0 :=
    contourFourthMoment_reference_zero hγ hγ1.le (circularContourRadii i)
  simp only [hz, mul_zero, Finset.sum_const_zero]

theorem circularBoundaryFourthMoment_eq_domain_moments {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (b : Fin 2 → ℝ) (Z : Fin 2 → LittleContourSpace γ)
    (hsmall : ∀ i, ‖(contourParameterShiftFamilyCLM γ b Z i).val -
      (littleReferenceCircle hγ hγ1.le (circularContourRadii i)).val‖ ≤ circularContourRadii i / 4) :
    circularBoundaryFourthMoment Z = ∑ i : Fin 2, (circularContourStrengths i : ℂ) *
      momentJ (contourC1EnclosedDomain (contourParameterShiftFamilyCLM γ b Z i).val
        (littleReferenceCircle hγ hγ1.le (circularContourRadii i)).val
        (growingMoment_radius_pos i) (lift_littleReferenceCircle hγ hγ1.le (circularContourRadii i))
        (hsmall i)) 4 := by
  rw [← circularBoundaryFourthMoment_parameterShift b Z]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact (momentJ_contourC1EnclosedDomain_four _ _ (growingMoment_radius_pos i)
    (lift_littleReferenceCircle hγ hγ1.le (circularContourRadii i)) (hsmall i)).symm

theorem fderiv_circularBoundaryFourthMoment_fourthMode {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (η τ : Fin 2 → ℂ) :
    fderiv ℝ (@circularBoundaryFourthMoment γ) (littleCircularReference hγ hγ1)
      (circularNormalModeLittle hγ hγ1.le 2 η τ) =
      ∑ i : Fin 2, (circularContourStrengths i : ℂ) *
        (Real.pi * (circularContourRadii i : ℂ) ^ 6 * η i) := by
  let H := circularNormalModeLittle hγ hγ1.le 2 η τ
  let Z : ℝ → Fin 2 → LittleContourSpace γ := fun s => littleCircularReference hγ hγ1 + s • H
  have hZ : HasDerivAt Z H 0 := by
    simpa only [one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const H).const_add
      (littleCircularReference hγ hγ1)
  have hd (i : Fin 2) : HasDerivAt (fun s => contourFourthMoment γ (Z s i).val)
      (Real.pi * (circularContourRadii i : ℂ) ^ 6 * η i) 0 := by
    apply hasDerivAt_contourFourthMoment_fourthMode hγ hγ1.le η τ i
    · exact ((LittleContourSpace.inclusion γ).comp (ContinuousLinearMap.proj i)).hasFDerivAt.comp_hasDerivAt 0 hZ
    · simp only [Z, zero_smul, add_zero]
      rfl
  have hsum := ((hd 0).const_mul (circularContourStrengths 0 : ℂ)).add
    ((hd 1).const_mul (circularContourStrengths 1 : ℂ))
  have hz : Z 0 = littleCircularReference hγ hγ1 := by simp only [Z, zero_smul, add_zero]
  have houter : HasFDerivAt (@circularBoundaryFourthMoment γ)
      (fderiv ℝ (@circularBoundaryFourthMoment γ) (littleCircularReference hγ hγ1)) (Z 0) := by
    rw [hz]
    exact ((contDiff_circularBoundaryFourthMoment γ).differentiable (by norm_num)).differentiableAt.hasFDerivAt
  have hc := houter.comp_hasDerivAt 0 hZ
  apply hc.unique
  simpa only [Function.comp_def, circularBoundaryFourthMoment, Fin.sum_univ_two, Pi.add_apply] using hsum

end Euler2D

end
