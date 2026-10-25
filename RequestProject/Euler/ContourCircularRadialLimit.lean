module

public import RequestProject.Euler.ContourCircularRadialBounds

/-! Actual radial dominated convergence reaches the singular circle
and evaluates every nonzero logarithmic Fourier coefficient. -/

@[expose] public section

noncomputable section

open Complex MeasureTheory Set Filter Topology
open scoped Interval

namespace Euler2D

theorem tendsto_contourCircular_logNorm_integral {q : ℕ → ℝ}
    (hq0 : ∀ n, 0 ≤ q n) (hq1 : ∀ n, q n ≤ 1)
    (hq : Tendsto q atTop (𝓝 1)) (m : ℕ) :
    Tendsto (fun n => ∫ θ in (-Real.pi : ℝ)..Real.pi,
      (Real.log ‖1 - (q n : ℂ) * contourCircleCharacter 1 θ‖ : ℂ) *
        contourCircleCharacter (m : ℤ) θ) atTop
      (𝓝 (∫ θ in (-Real.pi : ℝ)..Real.pi,
        (Real.log ‖1 - contourCircleCharacter 1 θ‖ : ℂ) * contourCircleCharacter (m : ℤ) θ)) := by
  let B : ℝ → ℝ := fun θ => |Real.log (1 / Real.pi)| + |Real.log (2 : ℝ)| + |Real.log θ|
  have hB : IntervalIntegrable B volume (-Real.pi) Real.pi :=
    (intervalIntegrable_const).add (intervalIntegral.intervalIntegrable_log').abs
  have hangle {θ : ℝ} (hθ : θ ∈ Ι (-Real.pi) Real.pi) : |θ| ≤ Real.pi := by
    rw [uIoc_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)] at hθ
    exact abs_le.mpr ⟨hθ.1.le, hθ.2⟩
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence B
  · apply Eventually.of_forall
    intro n
    have hn : Continuous (fun θ : ℝ => ‖1 - (q n : ℂ) * contourCircleCharacter 1 θ‖) :=
      (continuous_const.sub (continuous_const.mul (continuous_contourCircleCharacter 1))).norm
    exact ((Complex.measurable_ofReal.comp hn.measurable.log).mul
      (continuous_contourCircleCharacter (m : ℤ)).measurable).aestronglyMeasurable
  · apply Eventually.of_forall
    intro n
    filter_upwards [volume.ae_ne (0 : ℝ)] with θ hθ0
    intro hθ
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_contourCircleCharacter, mul_one]
    exact contourCircular_radial_log_bound (hq0 n) (hq1 n) (hangle hθ) hθ0
  · exact hB
  · filter_upwards [volume.ae_ne (0 : ℝ)] with θ hθ0
    intro hθ
    have hlower := contourCircular_radial_chord_lower (q := (1 : ℝ)) zero_le_one le_rfl (hangle hθ)
    simp only [Complex.ofReal_one, one_mul] at hlower
    have hn0 : ‖1 - contourCircleCharacter 1 θ‖ ≠ 0 :=
      (lt_of_lt_of_le (mul_pos (by positivity) (abs_pos.mpr hθ0)) hlower).ne'
    have hqn : Tendsto (fun n => (q n : ℂ)) atTop (𝓝 (1 : ℂ)) :=
      Complex.continuous_ofReal.continuousAt.tendsto.comp hq
    have hn : Tendsto (fun n => ‖1 - (q n : ℂ) * contourCircleCharacter 1 θ‖) atTop
        (𝓝 ‖1 - contourCircleCharacter 1 θ‖) := by
      simpa only [one_mul] using
        (tendsto_const_nhds.sub (hqn.mul_const (contourCircleCharacter 1 θ))).norm
    have hl := (Real.continuousAt_log hn0).tendsto.comp hn
    exact (Complex.continuous_ofReal.continuousAt.tendsto.comp hl).mul_const
      (contourCircleCharacter (m : ℤ) θ)

theorem integral_contourCircular_unit_logNorm {m : ℕ} (hm : 0 < m) :
    (∫ θ in (-Real.pi : ℝ)..Real.pi,
      (Real.log ‖1 - contourCircleCharacter 1 θ‖ : ℂ) * contourCircleCharacter (m : ℤ) θ) =
      -(1 / (m : ℂ)) * (Real.pi : ℂ) := by
  let q : ℕ → ℝ := fun n => 1 - 1 / ((n : ℝ) + 1)
  have hq0 (n : ℕ) : 0 ≤ q n := by
    have h : 1 / ((n : ℝ) + 1) ≤ 1 :=
      (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
    dsimp only [q]
    linarith
  have hq1 (n : ℕ) : q n < 1 := by
    dsimp only [q]
    have h : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  have hq : Tendsto q atTop (𝓝 1) := by
    simpa only [sub_zero] using
      (tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_one_div_add_atTop_nhds_zero_nat
  have hi := tendsto_contourCircular_logNorm_integral hq0 (fun n => (hq1 n).le) hq m
  have he (n : ℕ) := integral_contourCircular_logNorm_real_symmetric (hq0 n) (hq1 n) hm
  have hcq : Tendsto (fun n => (q n : ℂ)) atTop (𝓝 (1 : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp hq
  have hr := ((hcq.pow m).div_const (m : ℂ)).neg.mul_const (Real.pi : ℂ)
  simp only [one_pow] at hr
  have hr' := hr.congr' (Eventually.of_forall (fun n => (he n).symm))
  exact tendsto_nhds_unique hi hr'

end Euler2D

end
