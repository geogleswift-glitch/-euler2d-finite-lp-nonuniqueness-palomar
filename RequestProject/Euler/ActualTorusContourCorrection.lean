module

public import RequestProject.Euler.ActualTorusCorrectionAnalytic
public import RequestProject.Euler.CircularPhysicalContourScaleBounds

/-! The actual periodic-minus-planar velocity has a true C¹ Hölder
cubic cancellation budget on a small target contour. The estimate
comes from its proved harmonic cancellation and Cauchy derivatives. -/

@[expose] public section

set_option maxHeartbeats 1500000

noncomputable section

open Complex ComplexConjugate Set Filter Topology MeasureTheory Metric
open scoped NNReal

namespace Euler2D

def torusCorrectionContourBudget (γ L : ℝ) : ℝ :=
  (L + 1) ^ 3 * max 1 (2 * (1 + 2 * Real.pi ^ (1 - γ) * L) * L)

theorem norm_iteratedDeriv_actualTorusCorrectionVelocity
    {a K R L : ℝ} (ha : 0 < a) (ha16 : a ≤ 1 / 16) (hK : 0 ≤ K) (hR : 0 < R)
    (hL : 0 ≤ L) (hsmall : (L + 1) * R ≤ a)
    {w : ℂ → ℝ} (hw : Integrable w) (hsupp : ∀ y, a < ‖y‖ → w y = 0)
    (hmass : ∫ y, w y = 0) (hsym : ∀ y, w (I * y) = w y)
    (hbound : ∀ x : ℂ, ‖x‖ ≤ a → ‖actualTorusCorrectionVelocity w x‖ ≤
      K * ‖x‖ ^ 3 * ∫ y : ℂ, ‖y‖ ^ 4 * |w y|)
    {x : ℂ} (hx : ‖x‖ ≤ L * R) (m : ℕ) :
    ‖iteratedDeriv m (fun z => conj (actualTorusCorrectionVelocity w z)) x‖ ≤
      (m.factorial : ℝ) *
        (K * ((L + 1) * R) ^ 3 * ∫ y : ℂ, ‖y‖ ^ 4 * |w y|) / R ^ m := by
  have hM : 0 ≤ ∫ y : ℂ, ‖y‖ ^ 4 * |w y| := integral_nonneg (fun y => by positivity)
  have hF := analyticOnNhd_conj_actualTorusCorrectionVelocity ha ha16 hw hsupp hmass hsym
  have hnorm : ∀ z ∈ closedBall x R, ‖z‖ ≤ (L + 1) * R := by
    intro z hz
    have hzdist : ‖z - x‖ ≤ R := mem_closedBall_iff_norm.mp hz
    have htri := norm_le_norm_sub_add z x
    nlinarith
  have hd : DifferentiableOn ℂ (fun z => conj (actualTorusCorrectionVelocity w z))
      (closure (ball x R)) := by
    rw [closure_ball x hR.ne']
    intro z hz
    have hz3 : z ∈ ball (0 : ℂ) (3 * a) := by
      rw [mem_ball_zero_iff]
      exact ((hnorm z hz).trans hsmall).trans_lt (by linarith)
    exact (hF z hz3).differentiableAt.differentiableWithinAt
  apply Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le m hR hd.diffContOnCl
  intro z hz
  have hzn := hnorm z (sphere_subset_closedBall hz)
  rw [norm_conj]
  refine (hbound z (hzn.trans hsmall)).trans ?_
  gcongr

theorem actualTorusKernelDifference_eq_correctionVelocity
    {a : ℝ} (ha16 : a ≤ 1 / 16) {w : ℂ → ℝ}
    (hsupp : ∀ y, a < ‖y‖ → w y = 0) {x : ℂ} (hx : ‖x‖ ≤ a) :
    (∫ y, w y • planeComplexEquiv
      (torusBiotSavartKernel (complexTorusPoint (x - y)) -
        kernelK (complexPhysicalPlane (x - y)))) = actualTorusCorrectionVelocity w x := by
  apply integral_congr_ae
  exact ae_of_all _ (fun y => by
    dsimp only
    by_cases hy : w y = 0
    · simp [hy]
    have hya : ‖y‖ ≤ a := not_lt.mp (fun h => hy (hsupp y h))
    have hgap : ‖x - y‖ ≤ 1 / 2 := (norm_sub_le _ _).trans (by linarith)
    rw [torusBiotSavartKernel_complexTorusPoint_sub_kernelK hgap]
    rfl)

/-- Original contour-norm cubic cancellation for the actual Fourier
torus kernel. The constant is uniform in the physical density and
target scale, and the original kernel integral is the actual lift. -/
theorem exists_actualTorusKernelCorrection_contourC1
    {a : ℝ} (ha : 0 < a) (ha16 : a ≤ 1 / 16) :
    ∃ K : ℝ, 0 < K ∧ ∀ {γ : ℝ≥0}, (γ : ℝ) ≤ 1 →
      ∀ w : ℂ → ℝ, Integrable w → (∀ y, a < ‖y‖ → w y = 0) →
      (∫ y, w y) = 0 → (∀ y, w (I * y) = w y) →
      ∀ {R L : ℝ}, 0 < R → 0 ≤ L → (L + 1) * R ≤ a →
      ∀ Z : ContourC1Space γ, ‖Z‖ ≤ L * R →
      ∃ Q : ContourC1Space γ,
        (∀ θ, ContourC1Space.lift γ Q θ =
          ∫ y, w y • planeComplexEquiv
            (torusBiotSavartKernel (complexTorusPoint (ContourC1Space.lift γ Z θ - y)) -
              kernelK (complexPhysicalPlane (ContourC1Space.lift γ Z θ - y)))) ∧
        ‖Q‖ / R ≤ K * torusCorrectionContourBudget (γ : ℝ) L * R ^ 2 *
          ∫ y : ℂ, ‖y‖ ^ 4 * |w y| := by
  obtain ⟨K, hK, hbound⟩ := actual_torusRemainderVelocity_cancellation ha ha16
  refine ⟨K, hK, ?_⟩
  intro γ hγ1 w hw hsupp hmass hsym R L hR hL hsmall Z hZ
  have hM : 0 ≤ ∫ y : ℂ, ‖y‖ ^ 4 * |w y| := integral_nonneg (fun y => by positivity)
  let C := K * ((L + 1) * R) ^ 3 * ∫ y : ℂ, ‖y‖ ^ 4 * |w y|
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hF := analyticOnNhd_conj_actualTorusCorrectionVelocity ha ha16 hw hsupp hmass hsym
  have hZu : ∀ x, ContourC1Space.toBCF γ Z x ∈ ball (0 : ℂ) (3 * a) := by
    intro x
    rw [mem_ball_zero_iff]
    have hx := (ContourC1Space.norm_eval_le Z x).trans hZ
    change ‖ContourC1Space.toBCF γ Z x‖ ≤ L * R at hx
    nlinarith
  have hb (m : ℕ) (x : ContourCircle) := norm_iteratedDeriv_actualTorusCorrectionVelocity
    ha ha16 hK.le hR hL hsmall hw hsupp hmass hsym (hbound w hw hsupp hsym hmass)
      ((ContourC1Space.norm_eval_le Z x).trans hZ) m
  have h₀ : ∀ x, ‖conj (actualTorusCorrectionVelocity w (ContourC1Space.toBCF γ Z x))‖ ≤ C := by
    simpa only [Nat.factorial_zero, Nat.cast_one, pow_zero, one_mul, div_one, iteratedDeriv_zero] using hb 0
  have h₁ : ∀ x, ‖deriv (fun z => conj (actualTorusCorrectionVelocity w z))
      (ContourC1Space.toBCF γ Z x)‖ ≤ C / R := by
    simpa only [Nat.factorial_one, Nat.cast_one, pow_one, one_mul, iteratedDeriv_one] using hb 1
  have h₂ : ∀ x, ‖deriv (deriv (fun z => conj (actualTorusCorrectionVelocity w z)))
      (ContourC1Space.toBCF γ Z x)‖ ≤ 2 * C / R ^ 2 := by
    simpa only [Nat.factorial_two, Nat.cast_ofNat, iteratedDeriv_succ, iteratedDeriv_zero] using hb 2
  let W := analyticContourComposition hγ1 hF Z hZu (show 0 ≤ 2 * C / R ^ 2 by positivity) h₂
  refine ⟨contourC1Conjugate W, ?_, ?_⟩
  · intro θ
    rw [lift_contourC1Conjugate]
    change conj (conj (actualTorusCorrectionVelocity w (ContourC1Space.lift γ Z θ))) = _
    rw [conj_conj]
    symm
    apply actualTorusKernelDifference_eq_correctionVelocity ha16 hsupp
    have hh := (ContourC1Space.norm_eval_le Z (θ : ContourCircle)).trans hZ
    change ‖ContourC1Space.lift γ Z θ‖ ≤ L * R at hh
    change ‖ContourC1Space.lift γ Z θ‖ ≤ a
    nlinarith
  · have hn := (norm_contourC1Conjugate_le W).trans
      (norm_analyticContourComposition_le hγ1 hF Z hZu hC (by positivity) (by positivity) h₀ h₁ h₂)
    have hp : 0 ≤ Real.pi ^ (1 - (γ : ℝ)) := Real.rpow_nonneg Real.pi_pos.le _
    have hn' : ‖contourC1Conjugate W‖ ≤
        max C (2 * (C / R + Real.pi ^ (1 - (γ : ℝ)) * (2 * C / R ^ 2) * (L * R)) * (L * R)) := by
      refine hn.trans (max_le_max le_rfl ?_)
      gcongr
    refine (div_le_div_of_nonneg_right hn' hR.le).trans_eq ?_
    rw [show max C (2 * (C / R + Real.pi ^ (1 - (γ : ℝ)) * (2 * C / R ^ 2) * (L * R)) * (L * R)) =
      C * max 1 (2 * (1 + 2 * Real.pi ^ (1 - (γ : ℝ)) * L) * L) by
      rw [mul_max_of_nonneg _ _ hC]
      apply congrArg₂ max
      · ring
      · field_simp [hR.ne']]
    dsimp [C, torusCorrectionContourBudget]
    field_simp [hR.ne']

end Euler2D

end
