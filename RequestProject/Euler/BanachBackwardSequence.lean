module

public import RequestProject.Euler.BanachWeightedRemainder

/-! Genuine bounded geometric source sequences and removal of the
exponential weight from an actual nonlinear backward recurrence. -/

@[expose] public section

set_option maxHeartbeats 1000000

noncomputable section

open Set Filter Topology Metric
open scoped BoundedContinuousFunction

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def geometricBanachSequence (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (ξ : E) : ℕ →ᵇ E :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete (fun n => q ^ n • ξ) ‖ξ‖ (by
    intro n
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hq0 n)]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (pow_le_one₀ hq0 hq1) (norm_nonneg ξ))

theorem geometricBanachSequence_apply (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (ξ : E) (n : ℕ) :
    geometricBanachSequence q hq0 hq1 ξ n = q ^ n • ξ := rfl

theorem geometricBanachSequence_zero (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (ξ : E) :
    geometricBanachSequence q hq0 hq1 ξ 0 = ξ := by
  rw [geometricBanachSequence_apply, pow_zero, one_smul]

theorem norm_geometricBanachSequence (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (ξ : E) :
    ‖geometricBanachSequence q hq0 hq1 ξ‖ = ‖ξ‖ := by
  apply le_antisymm
  · apply (BoundedContinuousFunction.norm_le (norm_nonneg ξ)).mpr
    intro n
    rw [geometricBanachSequence_apply, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg hq0 n)]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (pow_le_one₀ hq0 hq1) (norm_nonneg ξ)
  · have h := BoundedContinuousFunction.norm_coe_le_norm (geometricBanachSequence q hq0 hq1 ξ) 0
    rwa [geometricBanachSequence_zero] at h

theorem geometricBanachSequence_backward {ρ a : ℝ} (hρ : 0 < ρ) (hρa : ρ < a)
    (L : E →L[ℝ] E) (ξ : E) (hξ : L ξ = a • ξ) (n : ℕ) :
    ρ • geometricBanachSequence (ρ / a) (div_nonneg hρ.le (hρ.trans hρa).le)
        ((div_lt_one (hρ.trans hρa)).mpr hρa).le ξ n =
      L (geometricBanachSequence (ρ / a) (div_nonneg hρ.le (hρ.trans hρa).le)
        ((div_lt_one (hρ.trans hρa)).mpr hρa).le ξ (n + 1)) := by
  rw [geometricBanachSequence_apply, geometricBanachSequence_apply, map_smul, hξ, smul_smul, smul_smul]
  congr 1
  rw [pow_succ]
  have ha : a ≠ 0 := (hρ.trans hρa).ne'
  field_simp [ha] <;> ring

theorem tendsto_unweightedBoundedSequence {ρ : ℝ} (hρ : 1 < ρ) (u : ℕ →ᵇ E) :
    Tendsto (fun n : ℕ => (ρ⁻¹) ^ n • u n) atTop (𝓝 (0 : E)) := by
  have hp : 0 < ρ := zero_lt_one.trans hρ
  have hi0 : 0 ≤ ρ⁻¹ := inv_nonneg.mpr hp.le
  have hi1 : ρ⁻¹ < 1 := by simpa only [one_div, inv_one] using (one_div_lt_one_div_of_lt zero_lt_one hρ)
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one hi0 hi1).mul_const ‖u‖
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (g := fun n : ℕ => (ρ⁻¹) ^ n * ‖u‖) (fun n => norm_nonneg _)
  · intro n
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hi0 n)]
    exact mul_le_mul_of_nonneg_left (BoundedContinuousFunction.norm_coe_le_norm u n)
      (pow_nonneg hi0 n)
  · simpa only [zero_mul] using ht

theorem unweightedBoundedSequence_backward {ρ : ℝ} (hρ : 1 ≤ ρ)
    (F : E → E) (u : ℕ →ᵇ E)
    (hrec : ∀ n : ℕ, ρ • u n = (fderiv ℝ F 0) (u (n + 1)) +
      ρ ^ (n + 1) • banachLocalRemainder F ((ρ⁻¹) ^ (n + 1) • u (n + 1))) :
    ∀ n : ℕ, F ((ρ⁻¹) ^ (n + 1) • u (n + 1)) = (ρ⁻¹) ^ n • u n := by
  intro n
  have hp : ρ ≠ 0 := (lt_of_lt_of_le zero_lt_one hρ).ne'
  have he1 : (ρ⁻¹) ^ (n + 1) • (ρ • u n) = (ρ⁻¹) ^ n • u n := by
    rw [smul_smul, pow_succ, mul_assoc, inv_mul_cancel₀ hp, mul_one]
  have he2 : (ρ⁻¹) ^ (n + 1) • ((fderiv ℝ F 0) (u (n + 1)) +
      ρ ^ (n + 1) • banachLocalRemainder F ((ρ⁻¹) ^ (n + 1) • u (n + 1))) =
        F ((ρ⁻¹) ^ (n + 1) • u (n + 1)) := by
    rw [smul_add, smul_smul,
      show (ρ⁻¹) ^ (n + 1) * ρ ^ (n + 1) = 1 by
        rw [← mul_pow, inv_mul_cancel₀ hp, one_pow], one_smul]
    rw [← (fderiv ℝ F 0).map_smul, banachLocalRemainder]
    abel
  exact (he1.symm.trans ((congrArg (fun v : E => (ρ⁻¹) ^ (n + 1) • v) (hrec n)).trans he2)).symm

end Euler2D

end
