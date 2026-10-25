module

public import RequestProject.Euler.ActualTorusContourSourceContinuity
public import RequestProject.Euler.TorusPhysicalSourceContinuity

/-! The cancellation bound applies to every actual Little forcing with
the genuine kernel lift, including the same field used by the local ODE. -/

@[expose] public section

set_option maxHeartbeats 1700000

noncomputable section

open Complex ComplexConjugate Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

theorem exists_actualTorusCorrection_contourLittle_budget
    {a : ℝ} (ha : 0 < a) (ha16 : a ≤ 1 / 16) :
    ∃ C : ℝ, 0 < C ∧ ∀ {γ : ℝ≥0}, (γ : ℝ) ≤ 1 →
      ∀ w : ℂ → ℝ, Integrable w → (∀ y, a < ‖y‖ → w y = 0) →
      (∫ y, w y) = 0 → (∀ y, w (I * y) = w y) →
      ∀ {R L : ℝ}, 0 < R → 0 ≤ L → (L + 1) * R ≤ a / 2 →
      ∀ Z : LittleContourSpace γ, ‖Z‖ ≤ L * R →
      ∀ Q : LittleContourSpace γ,
        (∀ θ, LittleContourSpace.lift γ Q θ =
          actualTorusCorrectionVelocity w (LittleContourSpace.lift γ Z θ)) →
        ‖Q‖ / R ≤ C * torusCorrectionContourBudget (γ : ℝ) L * R ^ 2 *
          ∫ y : ℂ, ‖y‖ ^ 4 * |w y| := by
  obtain ⟨C, hC, hsource⟩ := exists_actualTorusKernelCorrection_contourLittle ha ha16
  refine ⟨C, hC, ?_⟩
  intro γ hγ w hw hs hm hy R L hR hL hsmall Z hZ Q hQ
  obtain ⟨P, hP, hnorm⟩ := hsource hγ w hw hs hm hy hR hL hsmall Z hZ
  have he : P = Q := by
    apply littleContour_eq_of_lift_eq
    intro θ
    have hx := (ContourC1Space.norm_eval_le Z.val (θ : ContourCircle)).trans hZ
    change ‖LittleContourSpace.lift γ Z θ‖ ≤ L * R at hx
    exact (hP θ).trans ((actualTorusKernelDifference_eq_correctionVelocity ha16 hs
      (by nlinarith)).trans (hQ θ).symm)
  rwa [he] at hnorm

theorem actualTorusCorrectionVelocity_zero {a : ℝ} (ha : 0 < a) (ha16 : a ≤ 1 / 16)
    {w : ℂ → ℝ} (hw : Integrable w) (hs : ∀ y, a < ‖y‖ → w y = 0)
    (hm : (∫ y, w y) = 0) (hy : ∀ y, w (I * y) = w y) :
    actualTorusCorrectionVelocity w 0 = 0 := by
  obtain ⟨C, _, hpoint⟩ := actual_torusRemainderVelocity_cancellation ha ha16
  have hh := hpoint w hw hs hy hm 0 (by simpa using ha.le)
  simpa only [actualTorusCorrectionVelocity, norm_zero, zero_pow (by decide : 3 ≠ 0),
    mul_zero, zero_mul, norm_le_zero_iff] using hh

theorem actualTorusCorrection_contourLittle_zero {a : ℝ} (ha : 0 < a) (ha16 : a ≤ 1 / 16)
    {γ : ℝ≥0} {w : ℂ → ℝ} (hw : Integrable w) (hs : ∀ y, a < ‖y‖ → w y = 0)
    (hm : (∫ y, w y) = 0) (hy : ∀ y, w (I * y) = w y)
    {Q : LittleContourSpace γ}
    (hQ : ∀ θ, LittleContourSpace.lift γ Q θ = actualTorusCorrectionVelocity w 0) : Q = 0 := by
  apply littleContour_eq_of_lift_eq
  intro θ
  rw [hQ θ, actualTorusCorrectionVelocity_zero ha ha16 hw hs hm hy]
  rfl

namespace BoundedEulerParticleSystem

variable {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)

theorem exists_physicalComplexSource_contourLittle_budget
    {a : ℝ} (ha : 0 < a) (ha16 : a ≤ 1 / 16) :
    ∃ C : ℝ, 0 < C ∧ ∀ {γ : ℝ≥0}, (γ : ℝ) ≤ 1 →
      ∀ (hS : IsFourfoldBoundedEulerParticleSystem S) (w : R2 → ℝ),
      w =ᵐ[μT] (f : R2 → ℝ) → IsTorusPeriodic w →
      (∀ x, w (torusQuarterTurn x) = w x) → (∫ x in torusBox, f x) = 0 →
      ∀ t ∈ Icc (0 : ℝ) T,
      (∀ x ∈ torusBox, a < ‖x - torusCenter‖ → S.transportedScalar w t x = 0) →
      ∀ {R L : ℝ}, 0 < R → 0 ≤ L → (L + 1) * R ≤ a / 2 →
      ∀ Z : LittleContourSpace γ, ‖Z‖ ≤ L * R →
      ∀ Q : LittleContourSpace γ,
        (∀ θ, LittleContourSpace.lift γ Q θ =
          actualTorusCorrectionVelocity (S.physicalComplexSource w t)
            (LittleContourSpace.lift γ Z θ)) →
        ‖Q‖ / R ≤ C * torusCorrectionContourBudget (γ : ℝ) L * R ^ 2 *
          a ^ 4 * (scalarL2L1Constant * ‖f‖) := by
  obtain ⟨C, hC, hbudget⟩ := exists_actualTorusCorrection_contourLittle_budget ha ha16
  refine ⟨C, hC, ?_⟩
  intro γ hγ hS w hwf hwper hwrot hmean t ht hs R L hR hL hsmall Z hZ Q hQ
  have hh := hbudget hγ (S.physicalComplexSource w t)
    (S.integrable_physicalComplexSource hwf t) (S.physicalComplexSource_support hs)
    ((S.integral_physicalComplexSource hwf t).trans hmean)
    (S.physicalComplexSource_fourfold hS hwper hwrot (by linarith) ht hs)
    hR hL hsmall Z hZ Q hQ
  have hB : 0 ≤ torusCorrectionContourBudget (γ : ℝ) L := by
    unfold torusCorrectionContourBudget
    positivity
  refine hh.trans ?_
  have hm := S.physicalComplexSource_fourthAbsoluteMoment_le hwf hs
  calc
    _ ≤ C * torusCorrectionContourBudget (γ : ℝ) L * R ^ 2 *
        (a ^ 4 * (scalarL2L1Constant * ‖f‖)) :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    _ = _ := by ring

end BoundedEulerParticleSystem

end Euler2D

end
