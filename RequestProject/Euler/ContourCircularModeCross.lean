module

public import RequestProject.Euler.ContourCircularModeVariation

/-! Closed values of the actual cross-interface first variation on
both Fourier branches of every normal mode of order at least two. -/

@[expose] public section

noncomputable section

open Complex
open scoped ComplexConjugate

namespace Euler2D

theorem circularLogMode_positive {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    {m : ℕ} (hm : 0 < m) :
    circularLogMode r s (m : ℤ) =
      -(((min r s / max r s : ℝ) : ℂ) ^ m / (m : ℂ)) * (Real.pi : ℂ) :=
  integral_contourCircular_two_radii_logMode hr hs hm

theorem circularLogMode_negative {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    {m : ℕ} (hm : 0 < m) :
    circularLogMode r s (-(m : ℤ)) =
      -(((min r s / max r s : ℝ) : ℂ) ^ m / (m : ℂ)) * (Real.pi : ℂ) :=
  integral_contourCircular_two_radii_logMode_negative hr hs hm

set_option maxHeartbeats 600000 in
theorem circularContourModeVariation_inside_positive {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hsr : s < r) (N : ℕ) (a b : ℂ) :
    circularContourModeVariation r s ((N + 2 : ℕ) : ℤ) a b =
      I * (Real.pi : ℂ) * (((s / r : ℝ) : ℂ) ^ 2 * conj a - ((s / r : ℝ) : ℂ) ^ (N + 2) * b) := by
  have hA1 : circularCauchyMode r s 1 = 0 := circularCauchyMode_inside_positive hr hs.le hsr 0
  have hAp : circularCauchyMode r s ((N + 3 : ℕ) : ℤ) = 0 :=
    circularCauchyMode_inside_positive hr hs.le hsr (N + 2)
  have hAm : circularCauchyMode r s ((N + 1 : ℕ) : ℤ) = 0 :=
    circularCauchyMode_inside_positive hr hs.le hsr N
  have hAn : circularCauchyMode r s (-1) =
      (r : ℂ)⁻¹ * (((s / r : ℝ) : ℂ) * (2 * Real.pi : ℂ)) := by
    simpa only [pow_one, Nat.cast_one] using circularCauchyMode_inside_negative hr hs.le hsr 1
  rw [circularContourModeVariation_formula hr hs hsr.ne' ,
    show ((N + 2 : ℕ) : ℤ) + 1 = ((N + 3 : ℕ) : ℤ) by omega,
    show ((N + 2 : ℕ) : ℤ) - 1 = ((N + 1 : ℕ) : ℤ) by omega,
    hA1, hAp, hAm, hAn, circularLogMode_positive hr hs (by omega : 0 < N + 2)]
  simp only [min_eq_right hsr.le, max_eq_left hsr.le, map_zero, map_mul, map_inv₀,
    Complex.conj_ofReal, map_ofNat, zero_mul, mul_zero, zero_add, add_zero, sub_zero, zero_sub,
    Int.cast_natCast]
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hNC : ((N + 2 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (show N + 2 ≠ 0 by omega)
  push_cast at hNC ⊢
  field_simp [hrC, hNC]
  <;> ring

set_option maxHeartbeats 600000 in
theorem circularContourModeVariation_inside_negative {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hsr : s < r) (N : ℕ) (a b : ℂ) :
    circularContourModeVariation r s (-((N + 1 : ℕ) : ℤ)) a b =
      I * (Real.pi : ℂ) * (((s / r : ℝ) : ℂ) ^ 2 * conj a -
        ((s / r : ℝ) : ℂ) ^ (N + 3) * conj b) := by
  have hA1 : circularCauchyMode r s 1 = 0 := circularCauchyMode_inside_positive hr hs.le hsr 0
  rw [circularContourModeVariation_formula hr hs hsr.ne',
    show -((N + 1 : ℕ) : ℤ) + 1 = -(N : ℤ) by omega,
    show -((N + 1 : ℕ) : ℤ) - 1 = -((N + 2 : ℕ) : ℤ) by omega,
    hA1, circularCauchyMode_inside_negative hr hs.le hsr N,
    show (-1 : ℤ) = -((1 : ℕ) : ℤ) by norm_num,
    circularCauchyMode_inside_negative hr hs.le hsr 1,
    circularCauchyMode_inside_negative hr hs.le hsr (N + 2),
    circularLogMode_negative hr hs (by omega : 0 < N + 1)]
  simp only [min_eq_right hsr.le, max_eq_left hsr.le, map_mul, map_inv₀, map_pow,
    Complex.conj_ofReal, map_ofNat, pow_one, map_zero, zero_mul, mul_zero, zero_add,
    Int.cast_neg, Int.cast_natCast]
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hNC : ((N + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (show N + 1 ≠ 0 by omega)
  push_cast at hNC ⊢
  simp only [pow_succ]
  field_simp [hrC, hNC]
  <;> ring

set_option maxHeartbeats 600000 in
theorem circularContourModeVariation_outside_positive {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hrs : r < s) (N : ℕ) (a b : ℂ) :
    circularContourModeVariation r s ((N + 2 : ℕ) : ℤ) a b =
      I * (Real.pi : ℂ) * (-a + ((r / s : ℝ) : ℂ) ^ N * conj b) := by
  have hA1 : circularCauchyMode r s 1 = -(s : ℂ)⁻¹ * (2 * Real.pi : ℂ) := by
    simpa only [Nat.cast_one, pow_zero, one_mul] using circularCauchyMode_outside_positive hr.le hs hrs 0
  have hAp : circularCauchyMode r s ((N + 3 : ℕ) : ℤ) =
      -(s : ℂ)⁻¹ * (((r / s : ℝ) : ℂ) ^ (N + 2) * (2 * Real.pi : ℂ)) :=
    circularCauchyMode_outside_positive hr.le hs hrs (N + 2)
  have hAm : circularCauchyMode r s ((N + 1 : ℕ) : ℤ) =
      -(s : ℂ)⁻¹ * (((r / s : ℝ) : ℂ) ^ N * (2 * Real.pi : ℂ)) :=
    circularCauchyMode_outside_positive hr.le hs hrs N
  have hAn : circularCauchyMode r s (-1) = 0 := circularCauchyMode_outside_negative hr.le hs hrs 1
  rw [circularContourModeVariation_formula hr hs hrs.ne,
    show ((N + 2 : ℕ) : ℤ) + 1 = ((N + 3 : ℕ) : ℤ) by omega,
    show ((N + 2 : ℕ) : ℤ) - 1 = ((N + 1 : ℕ) : ℤ) by omega,
    hA1, hAp, hAm, hAn, circularLogMode_positive hr hs (by omega : 0 < N + 2)]
  simp only [min_eq_left hrs.le, max_eq_right hrs.le, map_zero, map_mul, map_inv₀,
    map_neg, map_pow, Complex.conj_ofReal, map_ofNat, zero_mul, mul_zero, add_zero, Int.cast_natCast]
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hNC : ((N + 2 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (show N + 2 ≠ 0 by omega)
  push_cast at hNC ⊢
  field_simp [hsC, hNC]
  <;> ring

set_option maxHeartbeats 600000 in
theorem circularContourModeVariation_outside_negative {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hrs : r < s) (N : ℕ) (a b : ℂ) :
    circularContourModeVariation r s (-((N + 1 : ℕ) : ℤ)) a b =
      I * (Real.pi : ℂ) * (-a + ((r / s : ℝ) : ℂ) ^ (N + 1) * b) := by
  have hA1 : circularCauchyMode r s 1 = -(s : ℂ)⁻¹ * (2 * Real.pi : ℂ) := by
    simpa only [Nat.cast_one, pow_zero, one_mul] using circularCauchyMode_outside_positive hr.le hs hrs 0
  rw [circularContourModeVariation_formula hr hs hrs.ne,
    show -((N + 1 : ℕ) : ℤ) + 1 = -(N : ℤ) by omega,
    show -((N + 1 : ℕ) : ℤ) - 1 = -((N + 2 : ℕ) : ℤ) by omega,
    hA1, circularCauchyMode_outside_negative hr.le hs hrs N,
    show (-1 : ℤ) = -((1 : ℕ) : ℤ) by norm_num,
    circularCauchyMode_outside_negative hr.le hs hrs 1,
    circularCauchyMode_outside_negative hr.le hs hrs (N + 2),
    circularLogMode_negative hr hs (by omega : 0 < N + 1)]
  simp only [min_eq_left hrs.le, max_eq_right hrs.le, map_zero, zero_mul, mul_zero,
    sub_zero, add_zero, Int.cast_neg, Int.cast_natCast]
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hNC : ((N + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (show N + 1 ≠ 0 by omega)
  push_cast at hNC ⊢
  field_simp [hsC, hNC]
  <;> ring

end Euler2D

end
