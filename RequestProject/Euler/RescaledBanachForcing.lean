module

public import Mathlib

@[expose] public section

set_option maxHeartbeats 1600000

noncomputable section

open Set Metric
open scoped NNReal

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def rescaledBanachForcing (q : ℝ → E → E) (A R : ℝ) (t : ℝ) (x : E) : E :=
  (A * R)⁻¹ • q (t / A) (R • x)

theorem norm_rescaledBanachForcing (q : ℝ → E → E) {A R : ℝ}
    (hA : 0 < A) (hR : 0 < R) (t : ℝ) (x : E) :
    ‖rescaledBanachForcing q A R t x‖ = ‖q (t / A) (R • x)‖ / R / A := by
  rw [rescaledBanachForcing, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (mul_nonneg hA.le hR.le))]
  field_simp

theorem lipschitzOnWith_rescaledBanachForcing (q : ℝ → E → E) {A R L a : ℝ}
    (hA : 0 < A) (hR : 0 < R) (htarget : R * L < a) {K : ℝ≥0} (t : ℝ)
    (hLip : LipschitzOnWith K (q (t / A)) (ball 0 a)) :
    LipschitzOnWith (⟨(K : ℝ) / A, div_nonneg K.coe_nonneg hA.le⟩ : ℝ≥0)
      (rescaledBanachForcing q A R t) (ball 0 L) := by
  have hnorm (x : E) : ‖R • x‖ = R * ‖x‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hR]
  have hm (x : E) (hx : x ∈ ball 0 L) : R • x ∈ ball 0 a := by
    apply mem_ball_zero_iff.mpr
    rw [hnorm]
    exact (mul_lt_mul_of_pos_left (mem_ball_zero_iff.mp hx) hR).trans htarget
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have hh := hLip.dist_le_mul (R • x) (hm x hx) (R • y) (hm y hy)
  have hd : dist (R • x) (R • y) = R * dist x y := by
    rw [dist_eq_norm, ← smul_sub, hnorm, dist_eq_norm]
  have hqd : dist (rescaledBanachForcing q A R t x) (rescaledBanachForcing q A R t y) =
      (A * R)⁻¹ * dist (q (t / A) (R • x)) (q (t / A) (R • y)) := by
    rw [rescaledBanachForcing, rescaledBanachForcing, dist_eq_norm, ← smul_sub,
      norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (mul_nonneg hA.le hR.le)), dist_eq_norm]
  rw [hqd]
  rw [hd] at hh
  calc
    _ ≤ (A * R)⁻¹ * ((K : ℝ) * (R * dist x y)) := mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by change _ = ((K : ℝ) / A) * dist x y; field_simp <;> ring

theorem continuous_rescaledBanachForcing (q : ℝ → E → E) {A R L a : ℝ}
    (hA : 0 < A) (hR : 0 < R) (htarget : R * L < a)
    (hc : ∀ x ∈ ball (0 : E) a, Continuous (fun t => q t x))
    {x : E} (hx : x ∈ ball 0 L) : Continuous (fun t => rescaledBanachForcing q A R t x) := by
  have hm : R • x ∈ ball 0 a := by
    apply mem_ball_zero_iff.mpr
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hR]
    exact (mul_lt_mul_of_pos_left (mem_ball_zero_iff.mp hx) hR).trans htarget
  exact continuous_const.smul ((hc _ hm).comp (continuous_id.div_const A))

end Euler2D

end
