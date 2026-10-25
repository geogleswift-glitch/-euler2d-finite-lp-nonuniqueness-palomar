module

public import RequestProject.Euler.CircularPhysicalContourScaleBounds
public import RequestProject.Euler.ContourConjugateLittle
public import RequestProject.Euler.AnalyticContourCompositionLittle

/-! The actual physical full field and its exact fourth-moment
remainder belong to the original little contour space, while retaining
the proved sixth- and tenth-power normalized contour-norm budgets. -/

@[expose] public section

set_option maxHeartbeats 1500000

noncomputable section

open Complex ComplexConjugate Set Filter Topology MeasureTheory
open scoped NNReal

namespace Euler2D

theorem contour_conjugate_analytic_composition_mem_little
    {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1) {F : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hF : AnalyticOnNhd ℂ F U) (Z : LittleContourSpace γ)
    (hZ : ∀ x, ContourC1Space.toBCF γ Z.val x ∈ U)
    {B₁ B₂ B₃ : ℝ} (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (hB₃ : 0 ≤ B₃)
    (h₁ : ∀ z ∈ U, ‖deriv F z‖ ≤ B₁)
    (h₂ : ∀ z ∈ U, ‖deriv (deriv F) z‖ ≤ B₂)
    (h₃ : ∀ z ∈ U, ‖deriv (deriv (deriv F)) z‖ ≤ B₃)
    (Q : ContourC1Space γ)
    (hQ : ∀ θ, ContourC1Space.lift γ Q θ = conj (F (LittleContourSpace.lift γ Z θ))) :
    Q ∈ (LittleContourSpace γ : Set (ContourC1Space γ)) := by
  let W := analyticContourCompositionLittle hγ1 hU hF Z hZ hB₁ hB₂ hB₃ h₁ h₂ h₃
  have he : contourC1Conjugate W.val = Q := by
    apply ContourC1Space.ext
    intro x
    obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective x
    change ContourC1Space.lift γ (contourC1Conjugate W.val) θ = ContourC1Space.lift γ Q θ
    rw [lift_contourC1Conjugate, hQ θ]
    rfl
  rw [← he]
  exact contourC1Conjugate_mem_little W

theorem clusterContourFieldC1_mem_little {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1)
    {w : ℂ → ℝ} {S M₄ d : ℝ} (hS : 0 ≤ S) (hw : Integrable w)
    (hsupp : ∀ y, S < ‖y‖ → w y = 0) (hmass : ∫ y, w y = 0)
    (hsym : ∀ y, w (I * y) = w y)
    (hM : (∫ y : ℂ, ‖y‖ ^ 4 * |w y|) ≤ M₄) (hd : 0 < d) (hsep : 8 * S ≤ d)
    (Z : LittleContourSpace γ) (hZ : ∀ x, d ≤ ‖ContourC1Space.toBCF γ Z.val x‖)
    (Q : ContourC1Space γ) (hQ : ∀ θ, ContourC1Space.lift γ Q θ = velocityC w (LittleContourSpace.lift γ Z θ)) :
    Q ∈ (LittleContourSpace γ : Set (ContourC1Space γ)) := by
  let U : Set ℂ := {z | d / 2 < ‖z‖}
  have hU : IsOpen U := isOpen_lt continuous_const continuous_norm
  have hF : AnalyticOnNhd ℂ (fun z => conj (velocityC w z)) U :=
    (analyticOnNhd_conj_velocityC hw hsupp).mono (fun z hz => by dsimp [U] at hz; dsimp; linarith)
  have hZu : ∀ x, ContourC1Space.toBCF γ Z.val x ∈ U := by
    intro x
    have hx := hZ x
    change d / 2 < ‖ContourC1Space.toBCF γ Z.val x‖
    linarith
  have hMn : 0 ≤ M₄ := (integral_nonneg (fun z => by positivity)).trans hM
  have hB (m : ℕ) := clusterDerivativeBound_nonneg hMn (half_pos hd) m
  have hb (m : ℕ) : ∀ z ∈ U,
      ‖iteratedDeriv m (fun x => conj (velocityC w x)) z‖ ≤ clusterDerivativeBound M₄ (d / 2) m := by
    intro z hz
    exact cluster_iteratedDeriv_bound_on_target hS hw hsupp hmass hsym hM (half_pos hd)
      (by linarith) (le_of_lt hz) m
  apply contour_conjugate_analytic_composition_mem_little hγ1 hU hF Z hZu (hB 1) (hB 2) (hB 3)
    (by simpa only [iteratedDeriv_one] using hb 1)
    (by simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hb 2)
    (by simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hb 3) Q
  intro θ
  rw [hQ θ]
  exact (conj_conj _).symm

theorem exteriorContourRemainderC1_mem_little {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1)
    {w : ℂ → ℝ} {S M₈ d : ℝ} (hS : 0 ≤ S) (hw : Integrable w)
    (hsupp : ∀ y, S < ‖y‖ → w y = 0) (hmass : ∫ y, w y = 0)
    (hsym : ∀ y, w (I * y) = w y)
    (hM : (∫ y : ℂ, ‖y‖ ^ 8 * |w y|) ≤ M₈) (hd : 0 < d) (hsep : 8 * S ≤ d)
    (Z : LittleContourSpace γ) (hZ : ∀ x, d ≤ ‖ContourC1Space.toBCF γ Z.val x‖)
    (Q : ContourC1Space γ)
    (hQ : ∀ θ, ContourC1Space.lift γ Q θ = exteriorFourthRemainder w (LittleContourSpace.lift γ Z θ)) :
    Q ∈ (LittleContourSpace γ : Set (ContourC1Space γ)) := by
  let U : Set ℂ := {z | d / 2 < ‖z‖}
  have hU : IsOpen U := isOpen_lt continuous_const continuous_norm
  have hF : AnalyticOnNhd ℂ (exteriorFourthRemainderCauchy w) U :=
    (analyticOnNhd_exteriorFourthRemainderCauchy hS hw hsupp).mono
      (fun z hz => by dsimp [U] at hz; dsimp; linarith)
  have hZu : ∀ x, ContourC1Space.toBCF γ Z.val x ∈ U := by
    intro x
    have hx := hZ x
    change d / 2 < ‖ContourC1Space.toBCF γ Z.val x‖
    linarith
  have hMn : 0 ≤ M₈ := (integral_nonneg (fun z => by positivity)).trans hM
  have hB (m : ℕ) := exteriorFourthDerivativeBound_nonneg hMn (half_pos hd) m
  have hb (m : ℕ) : ∀ z ∈ U,
      ‖iteratedDeriv m (exteriorFourthRemainderCauchy w) z‖ ≤ exteriorFourthDerivativeBound M₈ (d / 2) m := by
    intro z hz
    exact exteriorFourth_iteratedDeriv_bound_on_target hS hw hsupp hmass hsym hM (half_pos hd)
      (by linarith) (le_of_lt hz) m
  apply contour_conjugate_analytic_composition_mem_little hγ1 hU hF Z hZu (hB 1) (hB 2) (hB 3)
    (by simpa only [iteratedDeriv_one] using hb 1)
    (by simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hb 2)
    (by simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hb 3) Q
  intro θ
  rw [hQ θ]
  exact (conj_conj _).symm

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
  (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_physical_scaled_contour_fieldLittle_ratio {η : ℝ≥0} (hη : (η : ℝ) ≤ 1)
    (t A : ℝ) {r R c L : ℝ} (hr : 0 < r) (hR : 0 < R) (hc : 0 < c)
    (hsep : 8 * r * P.physicalSupportRadius t ≤ c * R)
    (Z : LittleContourSpace η) (hZ : ∀ x, c * R ≤ ‖ContourC1Space.toBCF η Z.val x‖)
    (hL : ‖Z‖ ≤ R * L) :
    ∃ Q : LittleContourSpace η,
      (∀ θ, LittleContourSpace.lift η Q θ =
        velocityC (scaledComplexDensity A r (P.physicalVorticity t)) (LittleContourSpace.lift η Z θ)) ∧
      ‖Q‖ / R ≤
        (finiteContourPatchMassBound circularContourStrengths circularContourRadii *
          cauchyContourNormBudget 5 (η : ℝ) 1 c L) * |A| * (r / R) ^ 6 * P.physicalSupportRadius t ^ 4 := by
  have hRad := P.physicalSupportRadius_pos t
  obtain ⟨Q, hQ, hnorm⟩ := P.exists_physical_scaled_contour_fieldC1_ratio hη t A hr hR hc
    (by nlinarith) Z.val hZ hL
  have hi := integrable_scaledComplexDensity (P.integrable_physicalVorticity t) A hr.ne'
  have hs := scaledComplexDensity_support (P.physicalVorticity_support t) hr A
  have hmass : (∫ z, scaledComplexDensity A r (P.physicalVorticity t) z) = 0 := by
    rw [integral_scaledComplexDensity A hr.le, P.integral_physicalVorticity_zero t, mul_zero]
  have hmem := clusterContourFieldC1_mem_little hη (S := r * P.physicalSupportRadius t)
    (by positivity) hi hs hmass (scaledComplexDensity_fourfold (P.physicalVorticity_fourfold t) A r)
    (P.physicalClusterMomentBudget_bounds t A hr) (mul_pos hc hR) (by nlinarith) Z hZ Q hQ
  exact ⟨⟨Q, hmem⟩, hQ, hnorm⟩

theorem exists_physical_scaled_contour_remainderLittle_ratio {η : ℝ≥0} (hη : (η : ℝ) ≤ 1)
    (t A : ℝ) {r R c L : ℝ} (hr : 0 < r) (hR : 0 < R) (hc : 0 < c)
    (hsep : 8 * r * P.physicalSupportRadius t ≤ c * R)
    (Z : LittleContourSpace η) (hZ : ∀ x, c * R ≤ ‖ContourC1Space.toBCF η Z.val x‖)
    (hL : ‖Z‖ ≤ R * L) :
    ∃ Q : LittleContourSpace η,
      (∀ θ, LittleContourSpace.lift η Q θ =
        velocityC (scaledComplexDensity A r (P.physicalVorticity t)) (LittleContourSpace.lift η Z θ) -
          I / (2 * Real.pi) * ((A : ℂ) * (r : ℂ) ^ 6 * P.moment t) *
            (conj (LittleContourSpace.lift η Z θ) ^ 5)⁻¹) ∧
      ‖Q‖ / R ≤
        (finiteContourPatchMassBound circularContourStrengths circularContourRadii *
          cauchyContourNormBudget 9 (η : ℝ) 1 c L) * |A| * (r / R) ^ 10 * P.physicalSupportRadius t ^ 8 := by
  have hRad := P.physicalSupportRadius_pos t
  obtain ⟨Q, hQ, hnorm⟩ := P.exists_physical_scaled_contour_remainderC1_ratio hη t A hr hR hc
    (by nlinarith) Z.val hZ hL
  have hi := integrable_scaledComplexDensity (P.integrable_physicalVorticity t) A hr.ne'
  have hs := scaledComplexDensity_support (P.physicalVorticity_support t) hr A
  have hmass : (∫ z, scaledComplexDensity A r (P.physicalVorticity t) z) = 0 := by
    rw [integral_scaledComplexDensity A hr.le, P.integral_physicalVorticity_zero t, mul_zero]
  have hQR : ∀ θ, ContourC1Space.lift η Q θ =
      exteriorFourthRemainder (scaledComplexDensity A r (P.physicalVorticity t))
        (LittleContourSpace.lift η Z θ) := by
    intro θ
    rw [hQ θ, P.exteriorFourthRemainder_physical_scaled_eq t A hr]
    rfl
  have hmem := exteriorContourRemainderC1_mem_little hη (S := r * P.physicalSupportRadius t)
    (by positivity) hi hs hmass (scaledComplexDensity_fourfold (P.physicalVorticity_fourfold t) A r)
    (P.physicalForcingMomentBudget_bounds t A hr) (mul_pos hc hR) (by nlinarith) Z hZ Q hQR
  exact ⟨⟨Q, hmem⟩, hQ, hnorm⟩

end CircularMaterialTransferProfile

end Euler2D

end
