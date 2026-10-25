module

public import Mathlib

/-!
# The first variation of the fourth moment at a circle (Lemma `pc:moment-variation`)

For a domain `D ⊂ ℂ` put `J_m(D) = ∫_D \bar z^m dA` (`momentJ`). For a continuous positive
radial function `r` the star-shaped domain `D_r = {z : |z| < r(arg z)}` (`starDomain`) has
`J_m(D_r) = ∫_{-π}^{π} e^{-imθ} r(θ)^{m+2}/(m+2) dθ` (`momentJ_starDomain`).

For the relative fourth-mode radial variation of the circle of radius `d`,
`r_ε(θ) = d(1 + ε Re(η e^{4iθ}))`, we prove `d/dε J_4(D_{r_ε})|_{ε=0} = π d⁶ η`
(`fourth_moment_first_variation`), which is the identity `δJ₄(D_j) = π d_j⁶ η_j` of the paper.
-/

@[expose] public section

open MeasureTheory Complex ComplexConjugate Set Real

namespace Euler2D

/-- The moment `J_m(D) = ∫_D \bar z^m dA`. -/
noncomputable def momentJ (D : Set ℂ) (m : ℕ) : ℂ := ∫ z in D, conj z ^ m
/-- The star-shaped domain `{z : |z| < r(arg z)}`. -/
def starDomain (r : ℝ → ℝ) : Set ℂ := {z | ‖z‖ < r (arg z)}

/-- Polar formula: `J_m(D_r) = ∫_{-π}^{π} e^{-imθ} r(θ)^{m+2}/(m+2) dθ` for continuous positive `r`. -/
theorem momentJ_starDomain {r : ℝ → ℝ} (hr : Continuous r) (hpos : ∀ θ, 0 < r θ) (m : ℕ) :
    momentJ (starDomain r) m =
      ∫ θ in Ioo (-π) π, exp (-(m * θ * I)) * ((r θ) ^ (m + 2) / (m + 2) : ℝ) := by
  have hmeasD : MeasurableSet (starDomain r) :=
    measurableSet_lt measurable_norm (hr.measurable.comp Complex.measurable_arg)
  set H : ℝ × ℝ → ℂ := fun q => if q.2 < r q.1 then ((q.2 ^ (m + 1) : ℝ) : ℂ) * exp (-(m * q.1 * I))
    else 0 with hH
  have hmeasS : MeasurableSet {q : ℝ × ℝ | q.2 < r q.1} :=
    measurableSet_lt measurable_snd (hr.measurable.comp measurable_fst)
  have hHmeas : Measurable H := by
    refine Measurable.ite hmeasS ?_ measurable_const
    fun_prop
  obtain ⟨Rm, hRm⟩ : ∃ Rm, ∀ θ ∈ Icc (-π) π, ‖r θ‖ ≤ Rm :=
    isCompact_Icc.exists_bound_of_continuousOn hr.continuousOn
  set R := max Rm 0 + 1 with hR
  have hR0 : 0 < R := by positivity
  have hHint : IntegrableOn H (Ioo (-π) π ×ˢ Ioi 0) := by
    have h1 : IntegrableOn H (Ioo (-π) π ×ˢ Ioo 0 R) := by
      refine Measure.integrableOn_of_bounded (M := R ^ (m + 1)) ?_ hHmeas.aestronglyMeasurable ?_
      · rw [Measure.volume_eq_prod, Measure.prod_prod]
        simp [ENNReal.mul_eq_top]
      · refine (ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)).mono fun q hq => ?_
        simp only [hH]
        split_ifs
        · rw [norm_mul, Complex.norm_exp]
          simp only [neg_re, mul_re, natCast_re, ofReal_re, natCast_im, ofReal_im, mul_zero,
            sub_zero, I_re, mul_im, zero_mul, add_zero, I_im, mul_one, sub_self, neg_zero,
            Real.exp_zero, Complex.norm_real, Real.norm_eq_abs]
          rw [abs_of_pos (pow_pos hq.2.1 _)]
          exact pow_le_pow_left₀ hq.2.1.le hq.2.2.le _
        · simp; positivity
    refine h1.of_forall_diff_eq_zero (measurableSet_Ioo.prod measurableSet_Ioi) ?_
    rintro ⟨θ, ρ⟩ ⟨⟨hθ, hρ⟩, hn⟩
    simp only [mem_prod, not_and] at hn hθ hρ
    have hρR : R ≤ ρ := by
      by_contra h; exact hn hθ ⟨hρ, lt_of_not_ge h⟩
    have hrR : r θ < ρ := by
      have := hRm θ (Ioo_subset_Icc_self hθ)
      have := le_abs_self (r θ)
      rw [Real.norm_eq_abs] at *
      linarith [le_max_left Rm 0]
    simp [hH, not_lt.mpr hrR.le]
  have hpt : EqOn (fun p : ℝ × ℝ => p.1 • (starDomain r).indicator (fun z => conj z ^ m)
      (Complex.polarCoord.symm p)) (fun p => H p.swap) polarCoord.target := by
    rintro ⟨ρ, θ⟩ ⟨hρ, hθ⟩
    simp only [mem_Ioi, mem_Ioo] at hρ hθ
    have he : Complex.polarCoord.symm (ρ, θ) = ρ * exp (θ * I) := by
      simp only [Complex.polarCoord_symm_apply, Complex.exp_mul_I, Complex.ofReal_cos,
        Complex.ofReal_sin]
    have hnorm : ‖(ρ : ℂ) * exp (θ * I)‖ = ρ := by
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hρ]
    have harg : arg ((ρ : ℂ) * exp (θ * I)) = θ := by
      rw [Complex.exp_mul_I]
      exact Complex.arg_mul_cos_add_sin_mul_I hρ ⟨hθ.1, hθ.2.le⟩
    simp only [he, hH, Prod.swap, indicator, starDomain, mem_setOf_eq, hnorm, harg]
    split_ifs
    · rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, mul_pow, ← Complex.exp_nat_mul]
      simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, real_smul]
      push_cast
      ring_nf
    · simp
  have hinner : ∀ θ ∈ Ioo (-π) π, ∫ ρ in Ioi 0, H (θ, ρ) =
      exp (-(m * θ * I)) * ((r θ) ^ (m + 2) / (m + 2) : ℝ) := by
    intro θ _
    have : (fun ρ => H (θ, ρ)) = (Iio (r θ)).indicator
        (fun ρ : ℝ => ((ρ ^ (m + 1) : ℝ) : ℂ) * exp (-(m * θ * I))) := by
      funext ρ; simp [hH, indicator]
    rw [this, setIntegral_indicator measurableSet_Iio, Ioi_inter_Iio,
      ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (hpos θ).le,
      intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal, integral_pow]
    push_cast
    ring
  rw [momentJ, ← integral_indicator hmeasD, ← Complex.integral_comp_polarCoord_symm,
    setIntegral_congr_fun polarCoord.open_target.measurableSet hpt,
    polarCoord_target, Measure.volume_eq_prod, setIntegral_prod_swap (Ioo (-π) π) (Ioi 0) H,
    setIntegral_prod H hHint]
  exact setIntegral_congr_fun measurableSet_Ioo hinner

/-- `∫_{-π}^{π} e^{-4iθ} Re(η e^{4iθ}) dθ = π η`. -/
lemma integral_fourth_mode (η : ℂ) :
    ∫ θ in Ioo (-π) π, exp (-(4 * θ * I)) * ((η * exp (4 * θ * I)).re : ℂ) = π * η := by
  have hpt : ∀ θ : ℝ, exp (-(4 * θ * I)) * ((η * exp (4 * θ * I)).re : ℂ) =
      η / 2 + conj η / 2 * exp ((-8 * I) * θ) := by
    intro θ
    rw [Complex.re_eq_add_conj, map_mul, ← Complex.exp_conj]
    have hc : conj (4 * (θ : ℂ) * I) = -(4 * θ * I) := by
      simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]; ring
    rw [hc]
    have e1 : exp (-(4 * θ * I)) * exp (4 * θ * I) = 1 := by
      rw [← Complex.exp_add]; simp
    have e2 : exp (-(4 * θ * I)) * exp (-(4 * θ * I)) = exp ((-8 * I) * θ) := by
      rw [← Complex.exp_add]; ring_nf
    linear_combination (η / 2) * e1 + (conj η / 2) * e2
  simp_rw [hpt]
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith [pi_pos])]
  rw [intervalIntegral.integral_add intervalIntegrable_const
    ((Continuous.intervalIntegrable (by fun_prop) _ _)), intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul, integral_exp_mul_complex (by simp [Complex.ext_iff])]
  have h1 : exp (-8 * I * π) = 1 := by
    rw [show -8 * I * (π : ℂ) = ((-4 : ℤ) : ℂ) * (2 * π * I) by push_cast; ring]
    exact Complex.exp_int_mul_two_pi_mul_I _
  have h2 : exp (-8 * I * ((-π : ℝ) : ℂ)) = 1 := by
    rw [show -8 * I * ((-π : ℝ) : ℂ) = ((4 : ℤ) : ℂ) * (2 * π * I) by push_cast; ring]
    exact Complex.exp_int_mul_two_pi_mul_I _
  rw [h1, h2]
  simp; ring

/-- **Lemma `pc:moment-variation`** (first variation at a circle). For `d > 0` and `η ∈ ℂ`, the
fourth moment `J₄` of the domain bounded by `r_ε(θ) = d(1 + ε Re(η e^{4iθ}))` has derivative
`π d⁶ η` at `ε = 0`. -/
theorem fourth_moment_first_variation {d : ℝ} (hd : 0 < d) (η : ℂ) :
    HasDerivAt (fun ε : ℝ => momentJ
        (starDomain fun θ => d * (1 + ε * (η * exp (4 * θ * I)).re)) 4)
      (π * d ^ 6 * η) 0 := by
  set a : ℝ → ℝ := fun θ => (η * exp (4 * θ * I)).re with ha
  have ha_cont : Continuous a := by fun_prop
  have ha_le : ∀ θ, |a θ| ≤ ‖η‖ := by
    intro θ
    calc |a θ| ≤ ‖η * exp (4 * θ * I)‖ := Complex.abs_re_le_norm _
      _ = ‖η‖ := by
        rw [norm_mul, show (4 * (θ : ℂ) * I) = ((4 * θ : ℝ) : ℂ) * I by push_cast; ring,
          Complex.norm_exp_ofReal_mul_I, mul_one]
  set c : ℕ → ℂ := fun k => ∫ θ in Ioo (-π) π,
    exp (-(4 * θ * I)) * ((d ^ 6 * (Nat.choose 6 k) * a θ ^ k / 6 : ℝ) : ℂ) with hc
  set P : ℝ → ℂ := fun ε => ∑ k ∈ Finset.range 7, (ε : ℂ) ^ k * c k with hP
  have hint : ∀ k : ℕ, IntegrableOn (fun θ : ℝ =>
      exp (-(4 * θ * I)) * ((d ^ 6 * (Nat.choose 6 k) * a θ ^ k / 6 : ℝ) : ℂ)) (Ioo (-π) π) := by
    intro k
    exact (Continuous.integrableOn_Icc (by fun_prop)).mono_set Ioo_subset_Icc_self
  have hEq : ∀ᶠ ε in nhds (0 : ℝ), momentJ
      (starDomain fun θ => d * (1 + ε * (η * exp (4 * θ * I)).re)) 4 = P ε := by
    have hmem : Ioo (-(1 / (‖η‖ + 1))) (1 / (‖η‖ + 1)) ∈ nhds (0 : ℝ) :=
      Ioo_mem_nhds (by simp; positivity) (by positivity)
    filter_upwards [hmem] with ε hε
    have hεa : ∀ θ, |ε * a θ| < 1 := by
      intro θ
      rw [abs_mul]
      have h1 : |ε| < 1 / (‖η‖ + 1) := abs_lt.mpr hε
      calc |ε| * |a θ| ≤ |ε| * ‖η‖ := mul_le_mul_of_nonneg_left (ha_le θ) (abs_nonneg _)
        _ ≤ 1 / (‖η‖ + 1) * ‖η‖ := mul_le_mul_of_nonneg_right h1.le (norm_nonneg _)
        _ < 1 := by rw [div_mul_eq_mul_div, one_mul, div_lt_one (by positivity)]; linarith
    have hpos : ∀ θ, 0 < d * (1 + ε * a θ) := fun θ => by
      have := (abs_lt.mp (hεa θ)).1
      have : 0 < 1 + ε * a θ := by linarith
      positivity
    have := momentJ_starDomain (r := fun θ => d * (1 + ε * a θ)) (by fun_prop) hpos 4
    simp only [ha] at this
    rw [this, hP]
    simp only [hc]
    simp_rw [← integral_const_mul]
    rw [← integral_finset_sum _ fun k _ => (hint k).const_mul _]
    refine setIntegral_congr_fun measurableSet_Ioo fun θ _ => ?_
    simp only [ha, Finset.sum_range_succ, Finset.sum_range_zero]
    push_cast
    norm_num [Nat.choose]
    ring
  have hPd : HasDerivAt P (c 1) 0 := by
    have h := HasDerivAt.sum (u := Finset.range 7) (fun k _ =>
      (((hasDerivAt_id (0 : ℝ)).ofReal_comp).pow k).mul_const (c k))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
    convert h using 1
    · funext ε; simp [hP, Finset.sum_range_succ]
    · simp
  have hc1 : c 1 = π * d ^ 6 * η := by
    simp only [hc]
    have : ∀ θ : ℝ, exp (-(4 * θ * I)) * ((d ^ 6 * (Nat.choose 6 1) * a θ ^ 1 / 6 : ℝ) : ℂ) =
        (d ^ 6 : ℂ) * (exp (-(4 * θ * I)) * ((η * exp (4 * θ * I)).re : ℂ)) := by
      intro θ; simp [ha]; ring
    simp_rw [this]
    rw [integral_const_mul, integral_fourth_mode]
    ring
  rw [← hc1]
  exact hPd.congr_of_eventuallyEq hEq

end Euler2D

end
