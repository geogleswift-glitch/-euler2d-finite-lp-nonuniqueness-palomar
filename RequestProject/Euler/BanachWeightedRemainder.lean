module

public import RequestProject.Euler.BanachLocalRemainder
public import RequestProject.Euler.BanachSequenceGreenIdentity

/-! Actual weighted nonlinear remainder sequences on a closed Banach
ball. The exponential weights cancel in the Lipschitz estimate, so the
true local small constant is retained in the complete sequence space. -/

@[expose] public section

set_option maxHeartbeats 1000000

noncomputable section

open Set Filter Topology Metric
open scoped BoundedContinuousFunction

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem real_weight_inverse_pow_facts {ρ : ℝ} (hρ : 1 ≤ ρ) (n : ℕ) :
    0 ≤ ρ ^ n ∧ 0 ≤ (ρ⁻¹) ^ n ∧ (ρ⁻¹) ^ n ≤ 1 ∧ ρ ^ n * (ρ⁻¹) ^ n = 1 := by
  have hp : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ
  have hi0 : 0 ≤ ρ⁻¹ := inv_nonneg.mpr hp.le
  have hi1 : ρ⁻¹ ≤ 1 := by
    have h := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1) zero_lt_one hρ
    simpa only [one_div, div_one] using h
  refine ⟨pow_nonneg hp.le n, pow_nonneg hi0 n, pow_le_one₀ hi0 hi1, ?_⟩
  rw [← mul_pow, mul_inv_cancel₀ hp.ne', one_pow]

def weightedSequenceRemainderValue (R : E → E) (ρ : ℝ) (u : ℕ →ᵇ E) (n : ℕ) : E :=
  ρ ^ n • R ((ρ⁻¹) ^ n • u n)

theorem weightedSequence_argument_mem_closedBall {ρ r : ℝ} (hρ : 1 ≤ ρ)
    (u : ℕ →ᵇ E) (hu : ‖u‖ ≤ r) (n : ℕ) :
    (ρ⁻¹) ^ n • u n ∈ closedBall (0 : E) r := by
  have hw := real_weight_inverse_pow_facts hρ n
  rw [mem_closedBall, dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs, abs_of_nonneg hw.2.1]
  calc
    _ ≤ 1 * ‖u n‖ := mul_le_mul_of_nonneg_right hw.2.2.1 (norm_nonneg _)
    _ ≤ ‖u‖ := by simpa only [one_mul] using BoundedContinuousFunction.norm_coe_le_norm u n
    _ ≤ r := hu

theorem norm_weightedSequenceRemainderValue_sub_le {R : E → E} {ρ r δ : ℝ}
    (hρ : 1 ≤ ρ) (hδ : 0 ≤ δ)
    (hLip : ∀ x ∈ closedBall (0 : E) r, ∀ y ∈ closedBall (0 : E) r,
      ‖R x - R y‖ ≤ δ * ‖x - y‖)
    (u v : ℕ →ᵇ E) (hu : ‖u‖ ≤ r) (hv : ‖v‖ ≤ r) (n : ℕ) :
    ‖weightedSequenceRemainderValue R ρ u n - weightedSequenceRemainderValue R ρ v n‖ ≤
      δ * ‖u - v‖ := by
  have hw := real_weight_inverse_pow_facts hρ n
  rw [weightedSequenceRemainderValue, weightedSequenceRemainderValue, ← smul_sub, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg hw.1]
  calc
    _ ≤ ρ ^ n * (δ * ‖(ρ⁻¹) ^ n • u n - (ρ⁻¹) ^ n • v n‖) :=
      mul_le_mul_of_nonneg_left
        (hLip _ (weightedSequence_argument_mem_closedBall hρ u hu n)
          _ (weightedSequence_argument_mem_closedBall hρ v hv n)) hw.1
    _ = δ * ‖u n - v n‖ := by
      rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hw.2.1]
      calc
        _ = (ρ ^ n * (ρ⁻¹) ^ n) * (δ * ‖u n - v n‖) := by ring
        _ = _ := by rw [hw.2.2.2, one_mul]
    _ ≤ δ * ‖u - v‖ := mul_le_mul_of_nonneg_left
      (BoundedContinuousFunction.norm_coe_le_norm (u - v) n) hδ

theorem weightedSequenceRemainderValue_zero {R : E → E} (hR : R 0 = 0) (ρ : ℝ) (n : ℕ) :
    weightedSequenceRemainderValue R ρ (0 : ℕ →ᵇ E) n = 0 := by
  change ρ ^ n • R ((ρ⁻¹) ^ n • (0 : E)) = 0
  rw [_root_.smul_zero, hR, _root_.smul_zero]

theorem norm_weightedSequenceRemainderValue_le {R : E → E} {ρ r δ : ℝ}
    (hρ : 1 ≤ ρ) (hr : 0 ≤ r) (hδ : 0 ≤ δ) (hR : R 0 = 0)
    (hLip : ∀ x ∈ closedBall (0 : E) r, ∀ y ∈ closedBall (0 : E) r,
      ‖R x - R y‖ ≤ δ * ‖x - y‖)
    (u : ℕ →ᵇ E) (hu : ‖u‖ ≤ r) (n : ℕ) :
    ‖weightedSequenceRemainderValue R ρ u n‖ ≤ δ * ‖u‖ := by
  have h := norm_weightedSequenceRemainderValue_sub_le hρ hδ hLip u 0 hu
    (by simpa only [norm_zero] using hr) n
  simpa only [weightedSequenceRemainderValue_zero hR, sub_zero] using h

def weightedSequenceRemainder {R : E → E} {ρ r δ : ℝ}
    (hρ : 1 ≤ ρ) (hr : 0 ≤ r) (hδ : 0 ≤ δ) (hR : R 0 = 0)
    (hLip : ∀ x ∈ closedBall (0 : E) r, ∀ y ∈ closedBall (0 : E) r,
      ‖R x - R y‖ ≤ δ * ‖x - y‖)
    (u : closedBall (0 : ℕ →ᵇ E) r) : ℕ →ᵇ E :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (weightedSequenceRemainderValue R ρ u.val) (δ * r) (by
      intro n
      have hu : ‖u.val‖ ≤ r := by simpa only [mem_closedBall, dist_eq_norm, sub_zero] using u.property
      exact (norm_weightedSequenceRemainderValue_le hρ hr hδ hR hLip u.val hu n).trans
        (mul_le_mul_of_nonneg_left hu hδ))

theorem weightedSequenceRemainder_apply {R : E → E} {ρ r δ : ℝ}
    (hρ : 1 ≤ ρ) (hr : 0 ≤ r) (hδ : 0 ≤ δ) (hR : R 0 = 0)
    (hLip : ∀ x ∈ closedBall (0 : E) r, ∀ y ∈ closedBall (0 : E) r,
      ‖R x - R y‖ ≤ δ * ‖x - y‖)
    (u : closedBall (0 : ℕ →ᵇ E) r) (n : ℕ) :
    weightedSequenceRemainder hρ hr hδ hR hLip u n = weightedSequenceRemainderValue R ρ u.val n := rfl

theorem norm_weightedSequenceRemainder_le {R : E → E} {ρ r δ : ℝ}
    (hρ : 1 ≤ ρ) (hr : 0 ≤ r) (hδ : 0 ≤ δ) (hR : R 0 = 0)
    (hLip : ∀ x ∈ closedBall (0 : E) r, ∀ y ∈ closedBall (0 : E) r,
      ‖R x - R y‖ ≤ δ * ‖x - y‖)
    (u : closedBall (0 : ℕ →ᵇ E) r) :
    ‖weightedSequenceRemainder hρ hr hδ hR hLip u‖ ≤ δ * ‖u.val‖ := by
  have hu : ‖u.val‖ ≤ r := by simpa only [mem_closedBall, dist_eq_norm, sub_zero] using u.property
  apply (BoundedContinuousFunction.norm_le (mul_nonneg hδ (norm_nonneg u.val))).mpr
  intro n
  exact norm_weightedSequenceRemainderValue_le hρ hr hδ hR hLip u.val hu n

theorem norm_weightedSequenceRemainder_sub_le {R : E → E} {ρ r δ : ℝ}
    (hρ : 1 ≤ ρ) (hr : 0 ≤ r) (hδ : 0 ≤ δ) (hR : R 0 = 0)
    (hLip : ∀ x ∈ closedBall (0 : E) r, ∀ y ∈ closedBall (0 : E) r,
      ‖R x - R y‖ ≤ δ * ‖x - y‖)
    (u v : closedBall (0 : ℕ →ᵇ E) r) :
    ‖weightedSequenceRemainder hρ hr hδ hR hLip u - weightedSequenceRemainder hρ hr hδ hR hLip v‖ ≤
      δ * ‖u.val - v.val‖ := by
  have hu : ‖u.val‖ ≤ r := by simpa only [mem_closedBall, dist_eq_norm, sub_zero] using u.property
  have hv : ‖v.val‖ ≤ r := by simpa only [mem_closedBall, dist_eq_norm, sub_zero] using v.property
  apply (BoundedContinuousFunction.norm_le (mul_nonneg hδ (norm_nonneg (u.val - v.val)))).mpr
  intro n
  exact norm_weightedSequenceRemainderValue_sub_le hρ hδ hLip u.val v.val hu hv n

end Euler2D

end
