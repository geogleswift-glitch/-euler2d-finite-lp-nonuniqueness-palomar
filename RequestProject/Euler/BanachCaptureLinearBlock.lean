module

public import RequestProject.Euler.CaptureBlockPowerGap

@[expose] public section

set_option maxHeartbeats 1500000

noncomputable section

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem continuousLinearMap_pow_eigen (L : E →L[ℝ] E) {a : ℝ} {v : E}
    (he : L v = a • v) (n : ℕ) : (L ^ n) v = a ^ n • v := by
  induction n with
  | zero => simp only [pow_zero, ContinuousLinearMap.one_apply, one_smul]
  | succ n ih =>
    rw [pow_succ', ContinuousLinearMap.mul_apply, ih, L.map_smul, he, smul_smul, pow_succ']
    rw [mul_comm (a ^ n) a]

theorem exists_banach_capture_linear_block (L P : E →L[ℝ] E) {lam C : ℝ}
    (hlam : 2 < lam) (heigen : ∀ v, (L ^ 2) (P v) = lam ^ 2 • P v)
    (hbound : ∀ (n : ℕ) (v : E), P v = 0 → ‖((L ^ 2) ^ n) v‖ ≤ C * 2 ^ n * ‖v‖) :
    ∃ k : ℕ, 0 < k ∧ ∃ q : ℝ, 1 < q ∧ q ^ 2 < (lam ^ 2) ^ k ∧
      (∀ v, P v = 0 → ‖((L ^ 2) ^ k) v‖ ≤ q * ‖v‖) ∧
      ∀ v, ((L ^ 2) ^ k) (P v) = (lam ^ 2) ^ k • P v := by
  obtain ⟨k, hk, q, hq, hCq, hgap⟩ := exists_capture_block_power_gap (C := C) hlam
  refine ⟨k, hk, q, hq, hgap, ?_, ?_⟩
  · intro v hv
    exact (hbound k v hv).trans (mul_le_mul_of_nonneg_right hCq (norm_nonneg v))
  · intro v
    exact continuousLinearMap_pow_eigen (L ^ 2) (heigen v) k

end Euler2D

end
