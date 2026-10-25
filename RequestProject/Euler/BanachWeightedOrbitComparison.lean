module

public import RequestProject.Euler.BanachBackwardOrbitUniqueness

/-! The actual affine Green identity for differences of two nonlinear
weighted orbits, and the resulting uniform parameter comparison. -/

@[expose] public section

set_option maxHeartbeats 2500000

noncomputable section

open Set Filter Topology Metric
open scoped BoundedContinuousFunction ContDiff

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem weightedNonlinearSequence_affine_difference
    {ρ a β C r δ : ℝ} (hρ : 1 ≤ ρ) (ha : a ≠ 0)
    (hβ : 0 ≤ β) (hβρ : β < ρ) (hC : 0 ≤ C) (hr : 0 ≤ r) (hδ : 0 ≤ δ)
    (L P : E →L[ℝ] E) (hcomm : L.comp P = P.comp L)
    (heigen : ∀ v, L (P v) = a • P v)
    (hbound : ∀ (k : ℕ) (v : E), P v = 0 → ‖(L ^ k) v‖ ≤ C * β ^ k * ‖v‖)
    (R : E → E) (hR : R 0 = 0)
    (hLip : ∀ x ∈ closedBall (0 : E) r, ∀ y ∈ closedBall (0 : E) r,
      ‖R x - R y‖ ≤ δ * ‖x - y‖)
    (G : (ℕ →ᵇ E) →L[ℝ] (ℕ →ᵇ E))
    (hGrec : ∀ (f : ℕ →ᵇ E) (n : ℕ), ρ • G f n = L (G f (n + 1)) + f (n + 1))
    (hGP : ∀ f : ℕ →ᵇ E, P (G f 0) = 0) (hsmall : ‖G‖ * δ ≤ 1 / 2)
    (u v : closedBall (0 : ℕ →ᵇ E) r)
    (hurec : ∀ n, ρ • u.val n = L (u.val (n + 1)) +
      weightedSequenceRemainder hρ hr hδ hR hLip u (n + 1))
    (hvrec : ∀ n, ρ • v.val n = L (v.val (n + 1)) +
      weightedSequenceRemainder hρ hr hδ hR hLip v (n + 1))
    (s : ℕ →ᵇ E) (hsrec : ∀ n, ρ • s n = L (s (n + 1)))
    (hsP : P (s 0) = P (u.val 0) - P (v.val 0)) :
    u.val - v.val = s + G (weightedSequenceRemainder hρ hr hδ hR hLip u -
      weightedSequenceRemainder hρ hr hδ hR hLip v) ∧
      ‖u.val - v.val‖ ≤ 2 * ‖s‖ := by
  let N := weightedSequenceRemainder hρ hr hδ hR hLip
  let f : ℕ →ᵇ E := N u - N v
  let w : ℕ →ᵇ E := u.val - v.val - s - G f
  have hwrec (n : ℕ) : ρ • w n = L (w (n + 1)) := by
    change ρ • (u.val n - v.val n - s n - G f n) =
      L (u.val (n + 1) - v.val (n + 1) - s (n + 1) - G f (n + 1))
    rw [smul_sub, smul_sub, smul_sub, hurec n, hvrec n, hsrec n, hGrec f n,
      L.map_sub, L.map_sub, L.map_sub]
    change (L (u.val (n + 1)) + N u (n + 1)) -
      (L (v.val (n + 1)) + N v (n + 1)) - L (s (n + 1)) -
      (L (G f (n + 1)) + (N u (n + 1) - N v (n + 1))) = _
    abel
  have hwP : P (w 0) = 0 := by
    change P (u.val 0 - v.val 0 - s 0 - G f 0) = 0
    rw [P.map_sub, P.map_sub, P.map_sub, hsP, hGP]
    abel
  have hw : w = 0 := bounded_weighted_homogeneous_backward_eq_zero
    (lt_of_lt_of_le zero_lt_one hρ) ha hβ hβρ hC L P hcomm heigen hbound w hwrec hwP
  have hdiff : u.val - v.val = s + G f := by
    have hh : u.val - v.val - s - G f = 0 := hw
    exact sub_eq_iff_eq_add.mp (sub_eq_zero.mp hh) |>.trans (add_comm _ _)
  refine ⟨hdiff, ?_⟩
  have hN : ‖f‖ ≤ δ * ‖u.val - v.val‖ :=
    norm_weightedSequenceRemainder_sub_le hρ hr hδ hR hLip u v
  have hnorm : ‖u.val - v.val‖ ≤ ‖s‖ + (‖G‖ * δ) * ‖u.val - v.val‖ := by
    calc
      _ = ‖s + G f‖ := congrArg norm hdiff
      _ ≤ ‖s‖ + ‖G f‖ := norm_add_le _ _
      _ ≤ ‖s‖ + ‖G‖ * ‖f‖ := add_le_add le_rfl (G.le_opNorm f)
      _ ≤ ‖s‖ + ‖G‖ * (δ * ‖u.val - v.val‖) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hN (norm_nonneg G))
      _ = _ := by ring
  have hh := mul_le_mul_of_nonneg_right hsmall (norm_nonneg (u.val - v.val))
  nlinarith

theorem norm_weightedSequenceRemainder_sub_le_quadratic
    {R : E → E} {ρ r δ C : ℝ}
    (hρ : 1 ≤ ρ) (hr : 0 ≤ r) (hδ : 0 ≤ δ) (hC : 0 ≤ C) (hR : R 0 = 0)
    (hLip : ∀ x ∈ closedBall (0 : E) r, ∀ y ∈ closedBall (0 : E) r,
      ‖R x - R y‖ ≤ δ * ‖x - y‖)
    (hquad : ∀ x ∈ closedBall (0 : E) r, ∀ y ∈ closedBall (0 : E) r,
      ‖R x - R y‖ ≤ C * (‖x‖ + ‖y‖) * ‖x - y‖)
    (u v : closedBall (0 : ℕ →ᵇ E) r) :
    ‖weightedSequenceRemainder hρ hr hδ hR hLip u - weightedSequenceRemainder hρ hr hδ hR hLip v‖ ≤
      C * (‖u.val‖ + ‖v.val‖) * ‖u.val - v.val‖ := by
  have hu : ‖u.val‖ ≤ r := by simpa only [mem_closedBall, dist_zero_right] using u.property
  have hv : ‖v.val‖ ≤ r := by simpa only [mem_closedBall, dist_zero_right] using v.property
  apply (BoundedContinuousFunction.norm_le (by positivity :
    0 ≤ C * (‖u.val‖ + ‖v.val‖) * ‖u.val - v.val‖)).mpr
  intro n
  have hw := real_weight_inverse_pow_facts hρ n
  have hux : ‖(ρ⁻¹) ^ n • u.val n‖ ≤ ‖u.val‖ := by
    simpa only [mem_closedBall, dist_zero_right] using
      weightedSequence_argument_mem_closedBall hρ u.val le_rfl n
  have hvx : ‖(ρ⁻¹) ^ n • v.val n‖ ≤ ‖v.val‖ := by
    simpa only [mem_closedBall, dist_zero_right] using
      weightedSequence_argument_mem_closedBall hρ v.val le_rfl n
  change ‖ρ ^ n • R ((ρ⁻¹) ^ n • u.val n) - ρ ^ n • R ((ρ⁻¹) ^ n • v.val n)‖ ≤ _
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hw.1]
  calc
    _ ≤ ρ ^ n * (C * (‖(ρ⁻¹) ^ n • u.val n‖ + ‖(ρ⁻¹) ^ n • v.val n‖) *
        ‖(ρ⁻¹) ^ n • u.val n - (ρ⁻¹) ^ n • v.val n‖) :=
      mul_le_mul_of_nonneg_left
        (hquad _ (weightedSequence_argument_mem_closedBall hρ u.val hu n)
          _ (weightedSequence_argument_mem_closedBall hρ v.val hv n)) hw.1
    _ ≤ ρ ^ n * (C * (‖u.val‖ + ‖v.val‖) *
        ‖(ρ⁻¹) ^ n • u.val n - (ρ⁻¹) ^ n • v.val n‖) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (add_le_add hux hvx) hC) (norm_nonneg _)) hw.1
    _ = C * (‖u.val‖ + ‖v.val‖) * ‖u.val n - v.val n‖ := by
      rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hw.2.1]
      calc
        _ = (ρ ^ n * (ρ⁻¹) ^ n) * (C * (‖u.val‖ + ‖v.val‖) * ‖u.val n - v.val n‖) := by ring
        _ = _ := by rw [hw.2.2.2, one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (BoundedContinuousFunction.norm_coe_le_norm (u.val - v.val) n) (by positivity)

end Euler2D

end
