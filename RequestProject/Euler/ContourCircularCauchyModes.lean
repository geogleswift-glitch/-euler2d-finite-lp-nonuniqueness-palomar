module

public import RequestProject.Euler.ContourCircularResolvent
public import RequestProject.Euler.ContourCircleCharacterCalculus

/-! Exact Fourier integrals of the actual two-radius Cauchy kernel,
with both source-inside and source-outside orientations. -/

@[expose] public section

noncomputable section

open Complex Set MeasureTheory
open scoped ComplexConjugate

namespace Euler2D

def circularCauchyMode (r s : ℝ) (k : ℤ) : ℂ :=
  ∫ θ in (-Real.pi : ℝ)..Real.pi,
    ((r : ℂ) - (s : ℂ) * contourCircleCharacter 1 θ)⁻¹ * contourCircleCharacter k θ

theorem intervalIntegrable_contourCircular_resolvent {q : ℂ} (hq : ‖q‖ < 1) (k : ℤ) :
    IntervalIntegrable (fun θ : ℝ => (1 - q * contourCircleCharacter 1 θ)⁻¹ *
      contourCircleCharacter k θ) volume (-Real.pi) Real.pi := by
  have hn (θ : ℝ) : 1 - q * contourCircleCharacter 1 θ ≠ 0 := by
    intro hz
    have he := congrArg norm (sub_eq_zero.mp hz)
    simp only [norm_one, norm_mul, norm_contourCircleCharacter, mul_one] at he
    linarith
  exact (((continuous_const.sub (continuous_const.mul (continuous_contourCircleCharacter 1))).inv₀ hn).mul
    (continuous_contourCircleCharacter k)).intervalIntegrable _ _

theorem integral_contourCircular_reverse_resolvent {q : ℝ}
    (hq : ‖(q : ℂ)‖ < 1) (k : ℤ) :
    (∫ θ in (-Real.pi : ℝ)..Real.pi,
      (1 - (q : ℂ) * contourCircleCharacter (-1) θ)⁻¹ * contourCircleCharacter k θ) =
      conj (∫ θ in (-Real.pi : ℝ)..Real.pi,
        (1 - (q : ℂ) * contourCircleCharacter 1 θ)⁻¹ * contourCircleCharacter (-k) θ) := by
  have h := Complex.conjCLE.toContinuousLinearMap.intervalIntegral_comp_comm
    (intervalIntegrable_contourCircular_resolvent hq (-k))
  change (∫ θ in (-Real.pi : ℝ)..Real.pi,
    conj ((1 - (q : ℂ) * contourCircleCharacter 1 θ)⁻¹ * contourCircleCharacter (-k) θ)) = _ at h
  simpa only [ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply,
    map_mul, map_inv₀, map_sub, map_one, Complex.conj_ofReal,
    conj_contourCircleCharacter, neg_neg] using h

theorem circularCauchyMode_inside_factor {r s : ℝ} (hr : 0 < r) (k : ℤ) :
    circularCauchyMode r s k = (r : ℂ)⁻¹ *
      ∫ θ in (-Real.pi : ℝ)..Real.pi,
        (1 - ((s / r : ℝ) : ℂ) * contourCircleCharacter 1 θ)⁻¹ * contourCircleCharacter k θ := by
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hf (θ : ℝ) : (r : ℂ) - (s : ℂ) * contourCircleCharacter 1 θ =
      (r : ℂ) * (1 - ((s / r : ℝ) : ℂ) * contourCircleCharacter 1 θ) := by
    push_cast
    field_simp
    <;> ring
  unfold circularCauchyMode
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro θ _
  dsimp only
  rw [hf, mul_inv_rev]
  ring

theorem circularCauchyMode_inside_positive {r s : ℝ}
    (hr : 0 < r) (hs : 0 ≤ s) (hsr : s < r) (m : ℕ) :
    circularCauchyMode r s ((m + 1 : ℕ) : ℤ) = 0 := by
  have hq : ‖((s / r : ℝ) : ℂ)‖ < 1 := by
    rw [Complex.norm_of_nonneg (div_nonneg hs hr.le)]
    exact (div_lt_one hr).mpr hsr
  rw [circularCauchyMode_inside_factor hr,
    integral_contourCircular_resolvent_symmetric,
    integral_contourCircular_resolvent_positive hq (Nat.succ_pos m), mul_zero]

theorem circularCauchyMode_inside_negative {r s : ℝ}
    (hr : 0 < r) (hs : 0 ≤ s) (hsr : s < r) (m : ℕ) :
    circularCauchyMode r s (-(m : ℤ)) =
      (r : ℂ)⁻¹ * (((s / r : ℝ) : ℂ) ^ m * (2 * Real.pi : ℂ)) := by
  have hq : ‖((s / r : ℝ) : ℂ)‖ < 1 := by
    rw [Complex.norm_of_nonneg (div_nonneg hs hr.le)]
    exact (div_lt_one hr).mpr hsr
  rw [circularCauchyMode_inside_factor hr,
    integral_contourCircular_resolvent_symmetric, integral_contourCircular_resolvent_negative hq]

theorem circularCauchyMode_outside_factor {r s : ℝ} (hs : 0 < s) (k : ℤ) :
    circularCauchyMode r s k = -(s : ℂ)⁻¹ *
      ∫ θ in (-Real.pi : ℝ)..Real.pi,
        (1 - ((r / s : ℝ) : ℂ) * contourCircleCharacter (-1) θ)⁻¹ *
          contourCircleCharacter (k - 1) θ := by
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hf (θ : ℝ) : (r : ℂ) - (s : ℂ) * contourCircleCharacter 1 θ =
      (-(s : ℂ) * contourCircleCharacter 1 θ) *
        (1 - ((r / s : ℝ) : ℂ) * contourCircleCharacter (-1) θ) := by
    have hu : contourCircleCharacter 1 θ * contourCircleCharacter (-1) θ = 1 := by
      rw [contourCircleCharacter_mul]
      norm_num
    calc
      _ = -(s : ℂ) * contourCircleCharacter 1 θ + (r : ℂ) *
          (contourCircleCharacter 1 θ * contourCircleCharacter (-1) θ) := by rw [hu]; ring
      _ = _ := by push_cast; field_simp; ring
  unfold circularCauchyMode
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro θ _
  dsimp only
  calc
    _ = -(s : ℂ)⁻¹ * ((1 - ((r / s : ℝ) : ℂ) * contourCircleCharacter (-1) θ)⁻¹ *
          (contourCircleCharacter (-1) θ * contourCircleCharacter k θ)) := by
      rw [hf, mul_inv_rev, mul_inv_rev, inv_neg, inv_contourCircleCharacter]
      ring
    _ = _ := by rw [contourCircleCharacter_mul, show (-1 : ℤ) + k = k - 1 by ring]

theorem circularCauchyMode_outside_positive {r s : ℝ}
    (hr : 0 ≤ r) (hs : 0 < s) (hrs : r < s) (m : ℕ) :
    circularCauchyMode r s ((m + 1 : ℕ) : ℤ) =
      -(s : ℂ)⁻¹ * (((r / s : ℝ) : ℂ) ^ m * (2 * Real.pi : ℂ)) := by
  have hq : ‖((r / s : ℝ) : ℂ)‖ < 1 := by
    rw [Complex.norm_of_nonneg (div_nonneg hr hs.le)]
    exact (div_lt_one hs).mpr hrs
  rw [circularCauchyMode_outside_factor hs]
  simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
  rw [integral_contourCircular_reverse_resolvent hq, integral_contourCircular_resolvent_symmetric,
    integral_contourCircular_resolvent_negative hq]
  simp only [map_mul, map_pow, Complex.conj_ofReal, map_ofNat]

theorem circularCauchyMode_outside_negative {r s : ℝ}
    (hr : 0 ≤ r) (hs : 0 < s) (hrs : r < s) (m : ℕ) :
    circularCauchyMode r s (-(m : ℤ)) = 0 := by
  have hq : ‖((r / s : ℝ) : ℂ)‖ < 1 := by
    rw [Complex.norm_of_nonneg (div_nonneg hr hs.le)]
    exact (div_lt_one hs).mpr hrs
  rw [circularCauchyMode_outside_factor hs,
    show -(m : ℤ) - 1 = -((m + 1 : ℕ) : ℤ) by push_cast; ring,
    integral_contourCircular_reverse_resolvent hq]
  simp only [neg_neg]
  rw [integral_contourCircular_resolvent_symmetric,
    integral_contourCircular_resolvent_positive hq (Nat.succ_pos m), map_zero, mul_zero]

end Euler2D

end
