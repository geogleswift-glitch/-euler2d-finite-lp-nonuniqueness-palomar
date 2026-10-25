module

public import RequestProject.Euler.CircularReferenceQuadraticFlow
public import RequestProject.Euler.BanachFundamentalCurveIdentity
public import RequestProject.Euler.CircularFourierLinearFlow
public import RequestProject.Euler.CircularReferenceCompactness
public import RequestProject.Euler.CircularContourPeriodMap

/-! A genuine full fundamental operator and a uniform quadratic
material-flow error for the original circular contour dynamics. -/

@[expose] public section

set_option maxHeartbeats 4000000
set_option maxRecDepth 4000

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) quadraticFourierReferenceC1_group (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) := Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)
local instance (priority := 2000) quadraticFourierReferenceLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) quadraticFourierReferenceLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)
local instance (priority := 2000) quadraticFourierReferenceFamily_tower (γ : ℝ≥0) :
    IsScalarTower ℝ ℝ (Fin 2 → LittleContourSpace γ) where
  smul_assoc a b Z := by
    funext i
    change (a * b) • Z i = a • (b • Z i)
    exact (smul_smul a b (Z i)).symm

theorem continuous_circularReference_fieldDerivative {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) :
    Continuous (fun t : ℝ => fderiv ℝ (circularBanachField hγ hγ1) (littleCircularMaterialContours hγ hγ1 t)) := by
  have hU : IsOpen (circularBanachDomain hγ hγ1) := isOpen_phaseAdmissibleLittleContourFamilies _ _
  have hf : ContDiffOn ℝ 1 (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1) :=
    contDiffOn_finiteContourPhaseFieldTotal hγ hγ1 _ _ _ _ _ (1 : ℕ∞)
  have hD : ContinuousOn (fderiv ℝ (circularBanachField hγ hγ1)) (circularBanachDomain hγ hγ1) :=
    (hf.fderiv_of_isOpen hU (m := 0) (by norm_num)).continuousOn
  apply continuous_iff_continuousAt.mpr
  intro t
  exact ((hD _ (phaseAdmissible_littleCircularMaterialContours hγ hγ1 t)).continuousAt
    (hU.mem_nhds (phaseAdmissible_littleCircularMaterialContours hγ hγ1 t))).comp
      (contDiff_littleCircularMaterialContours hγ hγ1).continuous.continuousAt

theorem circularReference_variational_operator_Fourier_block {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {T : ℝ}
    (A : ℝ → (Fin 2 → LittleContourSpace γ) →L[ℝ] (Fin 2 → LittleContourSpace γ))
    (hAc : ContinuousOn A (Icc (0 : ℝ) T))
    (hA0 : A 0 = ContinuousLinearMap.id ℝ (Fin 2 → LittleContourSpace γ))
    (hAd : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt A
      ((fderiv ℝ (circularBanachField hγ hγ1) (littleCircularMaterialContours hγ hγ1 t)).comp (A t)) t)
    (N : ℕ) (η τ : CircularFourierVector) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    A t (circularNormalModeLittle hγ hγ1.le N η τ) = circularFourierLinearVariation hγ hγ1 N (η, τ) t := by
  have hYc : Continuous (circularFourierLinearVariation hγ hγ1 N (η, τ)) :=
    continuous_iff_continuousAt.mpr
      (fun t => (circularFourierLinearVariation_hasDerivAt hγ hγ1 N (η, τ) t).continuousAt)
  have he := banachFundamentalOperator_apply_eq_curve
    (continuous_circularReference_fieldDerivative hγ hγ1).continuousOn hAc hA0 hAd hYc.continuousOn
    (fun t _ => circularFourierLinearVariation_hasDerivAt hγ hγ1 N (η, τ) t)
  rw [circularFourierLinearVariation_zero] at he
  exact he t ht

theorem exists_circularReference_quadratic_Fourier_variation {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {T ρ : ℝ} (hT : 0 < T) (hρ : 0 < ρ)
    {X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hX : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) ρ) T X) :
    ∃ A : ℝ → (Fin 2 → LittleContourSpace γ) →L[ℝ] (Fin 2 → LittleContourSpace γ),
      Continuous A ∧ A 0 = ContinuousLinearMap.id ℝ (Fin 2 → LittleContourSpace γ) ∧
      (∀ t ∈ Icc (0 : ℝ) T, HasDerivAt A
        ((fderiv ℝ (circularBanachField hγ hγ1) (littleCircularMaterialContours hγ hγ1 t)).comp (A t)) t) ∧
      (∀ (N : ℕ) (η τ : CircularFourierVector), ∀ t ∈ Icc (0 : ℝ) T,
        A t (circularNormalModeLittle hγ hγ1.le N η τ) = circularFourierLinearVariation hγ hγ1 N (η, τ) t) ∧
      ∃ δ > 0, ∃ C > 0, ∀ h : Fin 2 → LittleContourSpace γ, ‖h‖ ≤ δ → ∀ t ∈ Icc (0 : ℝ) T,
        ‖X (littleCircularReference hγ hγ1 + h) t - littleCircularMaterialContours hγ hγ1 t - A t h‖ ≤
          C * ‖h‖ ^ 2 := by
  obtain ⟨A, hAc, hA0, hAd, δ, hδ, C, hC, hquad⟩ := exists_circularReference_quadratic_variation hγ hγ1 hT hρ hX
  refine ⟨A, hAc, hA0, hAd, ?_, δ, hδ, C, hC, hquad⟩
  intro N η τ t ht
  exact circularReference_variational_operator_Fourier_block hγ hγ1 A hAc.continuousOn hA0 hAd N η τ ht

end Euler2D

end
