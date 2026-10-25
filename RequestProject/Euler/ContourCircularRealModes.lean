module

public import RequestProject.Euler.ContourCircleCharacterCalculus
public import RequestProject.Euler.ContourCircularKernel

/-! Real Fourier modes, finite character sums, and the actual
pole-cancelling divided differences used by self interaction. -/

@[expose] public section

noncomputable section

open Complex Set MeasureTheory
open scoped ComplexConjugate BigOperators

namespace Euler2D

theorem integral_contourCircular_realMode (a : ℂ) (k l : ℤ) :
    (∫ θ in (-Real.pi : ℝ)..Real.pi,
      ((a * contourCircleCharacter k θ).re : ℂ) * contourCircleCharacter l θ) =
      (a * (if k + l = 0 then (2 * Real.pi : ℂ) else 0) +
        conj a * (if l - k = 0 then (2 * Real.pi : ℂ) else 0)) / 2 := by
  have he (θ : ℝ) : ((a * contourCircleCharacter k θ).re : ℂ) * contourCircleCharacter l θ =
      (a * contourCircleCharacter (k + l) θ + conj a * contourCircleCharacter (l - k) θ) / 2 := by
    rw [Complex.re_eq_add_conj, show l - k = -k + l by ring,
      ← contourCircleCharacter_mul k l θ, ← contourCircleCharacter_mul (-k) l θ]
    simp only [map_mul, conj_contourCircleCharacter]
    ring
  simp_rw [he]
  have hi1 : IntervalIntegrable (fun θ : ℝ => a * contourCircleCharacter (k + l) θ)
      volume (-Real.pi) Real.pi :=
    (continuous_const.mul (continuous_contourCircleCharacter (k + l))).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun θ : ℝ => conj a * contourCircleCharacter (l - k) θ)
      volume (-Real.pi) Real.pi :=
    (continuous_const.mul (continuous_contourCircleCharacter (l - k))).intervalIntegrable _ _
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add hi1 hi2]
  simp only [intervalIntegral.integral_const_mul, integral_contourCircleCharacter_symmetric]

theorem integral_contourCircular_realMode_sum {α : Type*} (s : Finset α)
    (a : ℂ) (k : α → ℤ) (l : ℤ) :
    (∫ θ in (-Real.pi : ℝ)..Real.pi,
      ((a * ∑ i ∈ s, contourCircleCharacter (k i) θ).re : ℂ) * contourCircleCharacter l θ) =
      ∑ i ∈ s, ∫ θ in (-Real.pi : ℝ)..Real.pi,
        ((a * contourCircleCharacter (k i) θ).re : ℂ) * contourCircleCharacter l θ := by
  classical
  have he : (fun θ : ℝ => ((a * ∑ i ∈ s, contourCircleCharacter (k i) θ).re : ℂ) *
      contourCircleCharacter l θ) = (fun θ => ∑ i ∈ s,
        ((a * contourCircleCharacter (k i) θ).re : ℂ) * contourCircleCharacter l θ) := by
    funext θ
    rw [Finset.mul_sum]
    change ((Complex.reCLM (∑ i ∈ s, a * contourCircleCharacter (k i) θ) : ℝ) : ℂ) * _ = _
    rw [map_sum, Complex.ofReal_sum, Finset.sum_mul]
    rfl
  rw [he]
  apply intervalIntegral.integral_finset_sum
  intro i _
  exact ((Complex.continuous_ofReal.comp (Complex.continuous_re.comp
    (continuous_const.mul (continuous_contourCircleCharacter (k i))))).mul
      (continuous_contourCircleCharacter l)).intervalIntegrable _ _

theorem integral_contourCircular_real_positive_sum (a : ℂ) {M : ℕ} (hM : 2 ≤ M) :
    (∫ θ in (-Real.pi : ℝ)..Real.pi,
      ((a * ∑ k ∈ Finset.range M, contourCircleCharacter (k : ℤ) θ).re : ℂ) *
        contourCircleCharacter 1 θ) = (Real.pi : ℂ) * conj a := by
  rw [integral_contourCircular_realMode_sum]
  have ht (k : ℕ) : (∫ θ in (-Real.pi : ℝ)..Real.pi,
      ((a * contourCircleCharacter (k : ℤ) θ).re : ℂ) * contourCircleCharacter 1 θ) =
      if k = 1 then (Real.pi : ℂ) * conj a else 0 := by
    rw [integral_contourCircular_realMode]
    have hp : (k : ℤ) + 1 ≠ 0 := by omega
    by_cases hk : k = 1
    · subst k
      norm_num
      ring
    · have hn : 1 - (k : ℤ) ≠ 0 := by omega
      simp only [if_neg hp, if_neg hn, if_neg hk, mul_zero, zero_add, zero_div]
  simp_rw [ht]
  rw [Finset.sum_eq_single 1]
  · simp
  · intro k _ hk
    exact if_neg hk
  · intro h
    exact False.elim (h (Finset.mem_range.mpr (by omega)))

theorem integral_contourCircular_real_negative_sum (a : ℂ) {M : ℕ} (hM : 0 < M) :
    (∫ θ in (-Real.pi : ℝ)..Real.pi,
      ((a * ∑ k ∈ Finset.range M, contourCircleCharacter (-((k + 1 : ℕ) : ℤ)) θ).re : ℂ) *
        contourCircleCharacter 1 θ) = (Real.pi : ℂ) * a := by
  rw [integral_contourCircular_realMode_sum]
  have ht (k : ℕ) : (∫ θ in (-Real.pi : ℝ)..Real.pi,
      ((a * contourCircleCharacter (-((k + 1 : ℕ) : ℤ)) θ).re : ℂ) * contourCircleCharacter 1 θ) =
      if k = 0 then (Real.pi : ℂ) * a else 0 := by
    rw [integral_contourCircular_realMode]
    have hn : 1 - -((k + 1 : ℕ) : ℤ) ≠ 0 := by omega
    by_cases hk : k = 0
    · subst k
      norm_num
      ring
    · have hp : -((k + 1 : ℕ) : ℤ) + 1 ≠ 0 := by omega
      simp only [if_neg hp, if_neg hn, if_neg hk, mul_zero, add_zero, zero_div]
  simp_rw [ht]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro k _ hk
    exact if_neg hk
  · intro h
    exact False.elim (h (Finset.mem_range.mpr hM))

theorem contourCircleCharacter_divided_positive (M : ℕ) (θ : ℝ)
    (hn : 1 - contourCircleCharacter 1 θ ≠ 0) :
    (1 - contourCircleCharacter (M : ℤ) θ) / (1 - contourCircleCharacter 1 θ) =
      ∑ k ∈ Finset.range M, contourCircleCharacter (k : ℤ) θ := by
  have hz : contourCircleCharacter 1 θ ≠ 1 := by
    intro h
    exact hn (by rw [h, sub_self])
  have he : (∑ k ∈ Finset.range M, contourCircleCharacter (k : ℤ) θ) =
      ∑ k ∈ Finset.range M, contourCircleCharacter 1 θ ^ k := by
    apply Finset.sum_congr rfl
    intro k _
    exact (contourCircleCharacter_pow k θ).symm
  rw [he, geom_sum_eq hz, ← contourCircleCharacter_pow M θ]
  have ha : 1 - contourCircleCharacter 1 θ ^ M = -(contourCircleCharacter 1 θ ^ M - 1) := by ring
  have hb : 1 - contourCircleCharacter 1 θ = -(contourCircleCharacter 1 θ - 1) := by ring
  rw [ha, hb, neg_div_neg_eq]

theorem contourCircleCharacter_divided_negative (M : ℕ) (θ : ℝ)
    (hn : 1 - contourCircleCharacter 1 θ ≠ 0) :
    (1 - contourCircleCharacter (-(M : ℤ)) θ) / (1 - contourCircleCharacter 1 θ) =
      -(∑ k ∈ Finset.range M, contourCircleCharacter (-((k + 1 : ℕ) : ℤ)) θ) := by
  let w : ℂ := contourCircleCharacter (-1) θ
  have hp (k : ℕ) : contourCircleCharacter (-(k : ℤ)) θ = w ^ k := by
    rw [← conj_contourCircleCharacter, ← contourCircleCharacter_pow, map_pow,
      conj_contourCircleCharacter]
  have hu : w * contourCircleCharacter 1 θ = 1 := by
    dsimp only [w]
    rw [contourCircleCharacter_mul]
    norm_num
  have he : (∑ k ∈ Finset.range M, contourCircleCharacter (-((k + 1 : ℕ) : ℤ)) θ) =
      (∑ k ∈ Finset.range M, w ^ k) * w := by
    simp_rw [hp, pow_succ]
    rw [Finset.sum_mul]
  have hg : (∑ k ∈ Finset.range M, w ^ k) * w * (1 - contourCircleCharacter 1 θ) = w ^ M - 1 := by
    calc
      _ = (∑ k ∈ Finset.range M, w ^ k) * (w - 1) := by rw [mul_assoc, mul_sub, mul_one, hu]
      _ = _ := geom_sum_mul w M
  rw [div_eq_iff hn, he, neg_mul, hg, hp]
  ring

end Euler2D

end
