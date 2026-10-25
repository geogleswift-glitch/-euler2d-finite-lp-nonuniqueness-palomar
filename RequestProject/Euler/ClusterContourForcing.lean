module

public import RequestProject.Euler.CircularPhysicalContourForcing

/-! The entire real fourfold zero-circulation inner cell has an actual
C¹ Hölder exterior field bounded by its fourth absolute moment.
This is the contour-norm field budget required during capture. -/

@[expose] public section

set_option maxHeartbeats 1000000

noncomputable section

open Complex ComplexConjugate Set MeasureTheory Metric Filter Topology
open scoped NNReal

namespace Euler2D

def clusterDerivativeBound (M₄ d : ℝ) (m : ℕ) : ℝ :=
  (m.factorial : ℝ) * (8 / (15 * Real.pi) * M₄ / (d / 2) ^ 5) / (d / 2) ^ m

theorem clusterDerivativeBound_nonneg {M₄ d : ℝ} (hM : 0 ≤ M₄) (hd : 0 < d) (m : ℕ) :
    0 ≤ clusterDerivativeBound M₄ d m := by
  unfold clusterDerivativeBound
  positivity

theorem analyticOnNhd_conj_velocityC {w : ℂ → ℝ} {S : ℝ}
    (hw : Integrable w) (hsupp : ∀ y, S < ‖y‖ → w y = 0) :
    AnalyticOnNhd ℂ (fun z => conj (velocityC w z)) {z | S < ‖z‖} := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const continuous_norm)
  intro z hz
  have hh := (hasDerivAt_planarCauchyTransform hw hsupp hz).const_mul (-(I / (2 * Real.pi)))
  have he : (fun x => -(I / (2 * Real.pi)) * planarCauchyTransform w x) =
      (fun x => conj (velocityC w x)) := by
    funext x
    exact (conj_velocityC w x).symm
  rw [he] at hh
  exact hh.differentiableAt.differentiableWithinAt

theorem norm_iteratedDeriv_conj_velocityC {w : ℂ → ℝ} {S : ℝ}
    (hS : 0 ≤ S) (hw : Integrable w) (hsupp : ∀ y, S < ‖y‖ → w y = 0)
    (hmass : ∫ y, w y = 0) (hsym : ∀ y, w (I * y) = w y)
    {z : ℂ} (hz0 : z ≠ 0) (hz : 4 * S ≤ ‖z‖) (m : ℕ) :
    ‖iteratedDeriv m (fun x => conj (velocityC w x)) z‖ ≤
      clusterDerivativeBound (∫ y : ℂ, ‖y‖ ^ 4 * |w y|) ‖z‖ m := by
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hhalf : 0 < ‖z‖ / 2 := by positivity
  have hlower : ∀ x ∈ closedBall z (‖z‖ / 2), ‖z‖ / 2 ≤ ‖x‖ := by
    intro x hx
    have hh := mem_closedBall_iff_norm.mp hx
    have ht := norm_sub_norm_le z x
    rw [norm_sub_rev z x] at ht
    linarith
  have hF := analyticOnNhd_conj_velocityC hw hsupp
  have hdiff : DifferentiableOn ℂ (fun x => conj (velocityC w x))
      (closure (ball z (‖z‖ / 2))) := by
    rw [closure_ball z hhalf.ne']
    intro x hx
    have hxnorm := hlower x hx
    have hxS : S < ‖x‖ := by linarith
    exact (hF x hxS).differentiableAt.differentiableWithinAt
  apply Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le m hhalf hdiff.diffContOnCl
  intro x hx
  have hxnorm := hlower x (sphere_subset_closedBall hx)
  have hxp : 0 < ‖x‖ := hhalf.trans_le hxnorm
  rw [norm_conj]
  exact (cluster_field_pointwise hS hw hsupp hmass hsym (norm_pos_iff.mp hxp)
    (by linarith)).trans
      (div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_le_pow_left₀ hhalf.le hxnorm 5))

theorem cluster_iteratedDeriv_bound_on_target
    {w : ℂ → ℝ} {S M₄ d : ℝ} (hS : 0 ≤ S) (hw : Integrable w)
    (hsupp : ∀ y, S < ‖y‖ → w y = 0) (hmass : ∫ y, w y = 0)
    (hsym : ∀ y, w (I * y) = w y)
    (hM : (∫ y : ℂ, ‖y‖ ^ 4 * |w y|) ≤ M₄) (hd : 0 < d) (hsep : 4 * S ≤ d)
    {x : ℂ} (hx : d ≤ ‖x‖) (m : ℕ) :
    ‖iteratedDeriv m (fun z => conj (velocityC w z)) x‖ ≤ clusterDerivativeBound M₄ d m := by
  have hx0 : x ≠ 0 := norm_pos_iff.mp (hd.trans_le hx)
  have hMn : 0 ≤ M₄ := (integral_nonneg (fun y => by positivity)).trans hM
  have hb := norm_iteratedDeriv_conj_velocityC hS hw hsupp hmass hsym hx0 (hsep.trans hx) m
  refine hb.trans ?_
  unfold clusterDerivativeBound
  gcongr

theorem exists_clusterContourFieldC1 {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1)
    {w : ℂ → ℝ} {S M₄ d : ℝ} (hS : 0 ≤ S) (hw : Integrable w)
    (hsupp : ∀ y, S < ‖y‖ → w y = 0) (hmass : ∫ y, w y = 0)
    (hsym : ∀ y, w (I * y) = w y)
    (hM : (∫ y : ℂ, ‖y‖ ^ 4 * |w y|) ≤ M₄) (hd : 0 < d) (hsep : 4 * S ≤ d)
    (Z : ContourC1Space γ) (hZ : ∀ x, d ≤ ‖ContourC1Space.toBCF γ Z x‖) :
    ∃ Q : ContourC1Space γ,
      (∀ θ, ContourC1Space.lift γ Q θ = velocityC w (ContourC1Space.lift γ Z θ)) ∧
      ‖Q‖ ≤ max (clusterDerivativeBound M₄ d 0)
        (2 * (clusterDerivativeBound M₄ d 1 + Real.pi ^ (1 - (γ : ℝ)) *
          clusterDerivativeBound M₄ d 2 * ‖Z‖) * ‖Z‖) := by
  have hMn : 0 ≤ M₄ := (integral_nonneg (fun y => by positivity)).trans hM
  have hB (m : ℕ) := clusterDerivativeBound_nonneg hMn hd m
  have hF := analyticOnNhd_conj_velocityC hw hsupp
  have hZu : ∀ x, ContourC1Space.toBCF γ Z x ∈ {z : ℂ | S < ‖z‖} := by
    intro x
    have hx := hZ x
    change S < ‖ContourC1Space.toBCF γ Z x‖
    rcases eq_or_lt_of_le hS with hS0 | hS0
    · rw [← hS0]
      exact hd.trans_le hx
    · linarith
  have hder (m : ℕ) (x : ContourCircle) :=
    cluster_iteratedDeriv_bound_on_target hS hw hsupp hmass hsym hM hd hsep (hZ x) m
  have h₀ : ∀ x, ‖conj (velocityC w (ContourC1Space.toBCF γ Z x))‖ ≤
      clusterDerivativeBound M₄ d 0 := by simpa only [iteratedDeriv_zero] using hder 0
  have h₁ : ∀ x, ‖deriv (fun z => conj (velocityC w z)) (ContourC1Space.toBCF γ Z x)‖ ≤
      clusterDerivativeBound M₄ d 1 := by simpa only [iteratedDeriv_one] using hder 1
  have h₂ : ∀ x, ‖deriv (deriv (fun z => conj (velocityC w z))) (ContourC1Space.toBCF γ Z x)‖ ≤
      clusterDerivativeBound M₄ d 2 := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hder 2
  let Q := analyticContourComposition hγ1 hF Z hZu (hB 2) h₂
  refine ⟨contourC1Conjugate Q, ?_, ?_⟩
  · intro θ
    rw [lift_contourC1Conjugate, show ContourC1Space.lift γ Q θ =
      conj (velocityC w (ContourC1Space.lift γ Z θ)) from rfl]
    exact conj_conj _
  · exact (norm_contourC1Conjugate_le Q).trans
      (norm_analyticContourComposition_le hγ1 hF Z hZu (hB 0) (hB 1) (hB 2) h₀ h₁ h₂)

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
  (P : CircularMaterialTransferProfile hγ hγ1)

def physicalClusterMomentBudget (t A r : ℝ) : ℝ :=
  |A| * r ^ 6 * P.physicalSupportRadius t ^ 4 *
    finiteContourPatchMassBound circularContourStrengths circularContourRadii

theorem physicalClusterMomentBudget_bounds (t A : ℝ) {r : ℝ} (hr : 0 < r) :
    (∫ z : ℂ, ‖z‖ ^ 4 * |scaledComplexDensity A r (P.physicalVorticity t) z|) ≤
      P.physicalClusterMomentBudget t A r := by
  rw [absMoment_scaledComplexDensity A hr]
  calc
    _ ≤ |A| * r ^ 6 * (P.physicalSupportRadius t ^ 4 *
        finiteContourPatchMassBound circularContourStrengths circularContourRadii) :=
      mul_le_mul_of_nonneg_left (P.physicalVorticity_absMoment_le t 4) (by positivity)
    _ = _ := by unfold physicalClusterMomentBudget; ring

/-- The actual inner-cell field, rather than an assumed forcing,
satisfies the fourth-moment C¹γ budget throughout the full time axis. -/
theorem exists_physical_scaled_contour_fieldC1 {η : ℝ≥0} (hη : (η : ℝ) ≤ 1)
    (t A : ℝ) {r d : ℝ} (hr : 0 < r) (hd : 0 < d)
    (hsep : 4 * r * P.physicalSupportRadius t ≤ d)
    (Z : ContourC1Space η) (hZ : ∀ x, d ≤ ‖ContourC1Space.toBCF η Z x‖) :
    ∃ Q : ContourC1Space η,
      (∀ θ, ContourC1Space.lift η Q θ =
        velocityC (scaledComplexDensity A r (P.physicalVorticity t)) (ContourC1Space.lift η Z θ)) ∧
      ‖Q‖ ≤ max (clusterDerivativeBound (P.physicalClusterMomentBudget t A r) d 0)
        (2 * (clusterDerivativeBound (P.physicalClusterMomentBudget t A r) d 1 +
          Real.pi ^ (1 - (η : ℝ)) * clusterDerivativeBound (P.physicalClusterMomentBudget t A r) d 2 *
            ‖Z‖) * ‖Z‖) := by
  have hR := P.physicalSupportRadius_pos t
  have hi := integrable_scaledComplexDensity (P.integrable_physicalVorticity t) A hr.ne'
  have hs := scaledComplexDensity_support (P.physicalVorticity_support t) hr A
  have hmass : (∫ z, scaledComplexDensity A r (P.physicalVorticity t) z) = 0 := by
    rw [integral_scaledComplexDensity A hr.le, P.integral_physicalVorticity_zero t, mul_zero]
  exact exists_clusterContourFieldC1 hη (S := r * P.physicalSupportRadius t)
    (by positivity) hi hs hmass (scaledComplexDensity_fourfold (P.physicalVorticity_fourfold t) A r)
    (P.physicalClusterMomentBudget_bounds t A hr) hd (by nlinarith) Z hZ

end CircularMaterialTransferProfile

end Euler2D

end
