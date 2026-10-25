module

public import RequestProject.Euler.CircularBoundaryFourthMoment
public import RequestProject.Euler.CircularReferenceFourierQuadratic

/-! The entire real two-dimensional unstable plane evolves by the
actual complex growing eigenvalue, including its tangential component.
The genuine fourth moment detects the same complex coefficient. -/

@[expose] public section

set_option maxHeartbeats 4000000
set_option maxRecDepth 4000

noncomputable section

open Complex Set Filter Topology Metric
open scoped NNReal ContDiff BigOperators

namespace Euler2D

local instance (priority := 2000) complexGrowingC1_group (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) := Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)
local instance (priority := 2000) complexGrowingC1_space (γ : ℝ≥0) :
    NormedSpace ℝ (ContourC1Space γ) := Submodule.normedSpace (contourC1GraphSubmodule γ)
local instance (priority := 2000) complexGrowingLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) complexGrowingLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)
local instance (priority := 2000) complexGrowingFamily_tower (γ : ℝ≥0) :
    IsScalarTower ℝ ℝ (Fin 2 → LittleContourSpace γ) where
  smul_assoc a b Z := by
    funext i
    change (a * b) • Z i = a • (b • Z i)
    exact (smul_smul a b (Z i)).symm

theorem littleCircularMaterialContours_eq_parameterShift_reference {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (t : ℝ) :
    littleCircularMaterialContours hγ hγ1 t = contourParameterShiftFamilyCLM γ
      (fun i => circularContourAngularVelocities i * t) (littleCircularReference hγ hγ1) := by
  funext i
  apply Subtype.ext
  apply ContourC1Space.ext
  intro x
  obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective x
  change LittleContourSpace.lift γ (littleCircularMaterialContours hγ hγ1 t i) θ =
    LittleContourSpace.lift γ (contourParameterShiftLittleCLM γ
      (circularContourAngularVelocities i * t) (littleCircularReference hγ hγ1 i)) θ
  rw [lift_littleCircularMaterialContours, lift_contourParameterShiftLittleCLM]
  rfl

theorem circularBoundaryFourthMoment_material_reference {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (t : ℝ) :
    circularBoundaryFourthMoment (littleCircularMaterialContours hγ hγ1 t) = 0 := by
  rw [littleCircularMaterialContours_eq_parameterShift_reference,
    circularBoundaryFourthMoment_parameterShift, circularBoundaryFourthMoment_reference]

def circularComplexGrowingVariation {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
    (c : ℂ) (t : ℝ) : Fin 2 → LittleContourSpace γ :=
  contourParameterShiftFamilyCLM γ (fun i => circularContourAngularVelocities i * t)
    (circularNormalModeLittle hγ hγ1.le 2 (c • circularGrowingNormal t) (c • circularGrowingTangential t))

theorem circularComplexGrowingVariation_hasDerivAt {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (c : ℂ) (t : ℝ) :
    HasDerivAt (circularComplexGrowingVariation hγ hγ1 c)
      (fderiv ℝ (circularBanachField hγ hγ1) (littleCircularMaterialContours hγ hγ1 t)
        (circularComplexGrowingVariation hγ hγ1 c t)) t := by
  have hn : HasDerivAt (fun s => c • circularGrowingNormal s)
      (circularAngularNormalAmplitude 2 (c • circularGrowingNormal t)) t := by
    rw [circularAngularNormalAmplitude_smul]
    exact (circularGrowingNormal_hasDerivAt t).const_smul c
  have ht : HasDerivAt (fun s => c • circularGrowingTangential s)
      (circularAngularTangentialAmplitude 2 (c • circularGrowingNormal t) (c • circularGrowingTangential t)) t := by
    rw [circularAngularTangentialAmplitude_smul]
    exact (circularGrowingTangential_hasDerivAt t).const_smul c
  exact hasDerivAt_circularFourier_variational hγ hγ1 2 hn ht

theorem circularComplexGrowingVariation_zero {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (c : ℂ) :
    circularComplexGrowingVariation hγ hγ1 c 0 = circularUnstableEmbeddingCLM hγ hγ1.le c := by
  simp only [circularComplexGrowingVariation, circularGrowingNormal, circularGrowingTangential,
    Complex.ofReal_zero, zero_mul, exp_zero, one_smul, mul_zero]
  rw [circularUnstableEmbeddingCLM_apply]
  exact contourParameterShiftFamilyCLM_zero _

theorem circularReference_variational_operator_unstable {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {T : ℝ}
    (A : ℝ → (Fin 2 → LittleContourSpace γ) →L[ℝ] (Fin 2 → LittleContourSpace γ))
    (hAc : ContinuousOn A (Icc (0 : ℝ) T))
    (hA0 : A 0 = ContinuousLinearMap.id ℝ (Fin 2 → LittleContourSpace γ))
    (hAd : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt A
      ((fderiv ℝ (circularBanachField hγ hγ1) (littleCircularMaterialContours hγ hγ1 t)).comp (A t)) t)
    (c : ℂ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    A t (circularUnstableEmbeddingCLM hγ hγ1.le c) = circularComplexGrowingVariation hγ hγ1 c t := by
  have hYc : Continuous (circularComplexGrowingVariation hγ hγ1 c) :=
    continuous_iff_continuousAt.mpr
      (fun t => (circularComplexGrowingVariation_hasDerivAt hγ hγ1 c t).continuousAt)
  have he := banachFundamentalOperator_apply_eq_curve
    (continuous_circularReference_fieldDerivative hγ hγ1).continuousOn hAc hA0 hAd hYc.continuousOn
    (fun t _ => circularComplexGrowingVariation_hasDerivAt hγ hγ1 c t)
  rw [circularComplexGrowingVariation_zero] at he
  exact he t ht

theorem fderiv_circularBoundaryFourthMoment_complexGrowing {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (c : ℂ) (t : ℝ) :
    fderiv ℝ (@circularBoundaryFourthMoment γ) (littleCircularMaterialContours hγ hγ1 t)
      (circularComplexGrowingVariation hγ hγ1 c t) =
      circularPatchGrowingResponse * c * exp ((t : ℂ) * lamStar) := by
  rw [littleCircularMaterialContours_eq_parameterShift_reference, circularComplexGrowingVariation,
    fderiv_circularBoundaryFourthMoment_parameterShift, fderiv_circularBoundaryFourthMoment_fourthMode]
  simp only [Fin.sum_univ_two, circularGrowingNormal, Pi.smul_apply, smul_eq_mul]
  norm_num [circularContourStrengths, circularContourRadii, vPlus, circularPatchGrowingResponse]
  ring

end Euler2D

end
