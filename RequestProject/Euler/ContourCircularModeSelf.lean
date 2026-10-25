module

public import RequestProject.Euler.ContourCircularRealModes
public import RequestProject.Euler.ContourCircularModeCross

/-! Actual singular self-interaction on the two Fourier branches.
The numerator cancels the pole before integration; all identities at
the diagonal are used only almost everywhere. -/

@[expose] public section

noncomputable section

open Complex Set Filter MeasureTheory
open scoped ComplexConjugate BigOperators Interval

namespace Euler2D

theorem contourCircle_unit_chord_ne_zero {θ : ℝ} (hθ : |θ| ≤ Real.pi) (hne : θ ≠ 0) :
    1 - contourCircleCharacter 1 θ ≠ 0 := by
  have h := contourCircular_radial_chord_lower (q := 1) (by norm_num) le_rfl hθ
  simp only [Complex.ofReal_one, one_mul] at h
  exact norm_pos_iff.mp ((mul_pos (by positivity) (abs_pos.mpr hne)).trans_le h)

set_option maxHeartbeats 600000 in
theorem circularSelfRational_of_divided {r : ℝ} (hr : 0 < r) (n : ℤ) (a : ℂ)
    (P : ℝ → ℂ) (hP : Continuous P)
    (hquot : ∀ θ, |θ| ≤ Real.pi → θ ≠ 0 →
      (1 - contourCircleCharacter n θ) / (1 - contourCircleCharacter 1 θ) = P θ) :
    IntervalIntegrable (fun θ : ℝ =>
      ((a - a * contourCircleCharacter n θ) /
        ((r : ℂ) - (r : ℂ) * contourCircleCharacter 1 θ)).re •
          (I * (r : ℂ) * contourCircleCharacter 1 θ)) volume (-Real.pi) Real.pi ∧
    (∫ θ in (-Real.pi : ℝ)..Real.pi,
      ((a - a * contourCircleCharacter n θ) /
        ((r : ℂ) - (r : ℂ) * contourCircleCharacter 1 θ)).re •
          (I * (r : ℂ) * contourCircleCharacter 1 θ)) =
      I * (r : ℂ) * ∫ θ in (-Real.pi : ℝ)..Real.pi,
        (((a / (r : ℂ)) * P θ).re : ℂ) * contourCircleCharacter 1 θ := by
  let R : ℝ → ℂ := fun θ =>
    ((a - a * contourCircleCharacter n θ) /
      ((r : ℂ) - (r : ℂ) * contourCircleCharacter 1 θ)).re •
        (I * (r : ℂ) * contourCircleCharacter 1 θ)
  let G : ℝ → ℂ := fun θ => I * (r : ℂ) *
    ((((a / (r : ℂ)) * P θ).re : ℂ) * contourCircleCharacter 1 θ)
  have hGc : Continuous G := continuous_const.mul
    ((Complex.continuous_ofReal.comp (Complex.continuous_re.comp (continuous_const.mul hP))).mul
      (continuous_contourCircleCharacter 1))
  have hiG := hGc.intervalIntegrable (μ := volume) (-Real.pi) Real.pi
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have he : R =ᵐ[volume.restrict (Ι (-Real.pi) Real.pi)] G := by
    filter_upwards [ae_restrict_mem measurableSet_uIoc, ae_restrict_of_ae (volume.ae_ne (0 : ℝ))]
      with θ hθ hθ0
    rw [uIoc_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)] at hθ
    have ha : |θ| ≤ Real.pi := abs_le.mpr ⟨hθ.1.le, hθ.2⟩
    have hn := contourCircle_unit_chord_ne_zero ha hθ0
    have hq : (a - a * contourCircleCharacter n θ) /
        ((r : ℂ) - (r : ℂ) * contourCircleCharacter 1 θ) =
        (a / (r : ℂ)) * ((1 - contourCircleCharacter n θ) / (1 - contourCircleCharacter 1 θ)) := by
      have hf : (r : ℂ) - (r : ℂ) * contourCircleCharacter 1 θ =
          (r : ℂ) * (1 - contourCircleCharacter 1 θ) := by ring
      rw [hf]
      field_simp [hrC, hn]
      <;> ring
    dsimp only [R, G]
    rw [hq, hquot θ ha hθ0, Complex.real_smul]
    ring
  refine ⟨hiG.congr_ae he.symm, ?_⟩
  calc
    (∫ θ in (-Real.pi : ℝ)..Real.pi, R θ) = ∫ θ in (-Real.pi : ℝ)..Real.pi, G θ :=
      intervalIntegral.integral_congr_ae_restrict he
    _ = _ := intervalIntegral.integral_const_mul _ _

theorem circularContourModeVariation_self_split {r : ℝ} (hr : 0 < r) (n : ℤ) (a : ℂ)
    (hi : IntervalIntegrable (fun θ : ℝ =>
      ((a - a * contourCircleCharacter n θ) /
        ((r : ℂ) - (r : ℂ) * contourCircleCharacter 1 θ)).re •
          (I * (r : ℂ) * contourCircleCharacter 1 θ)) volume (-Real.pi) Real.pi) :
    circularContourModeVariation r r n a a =
      (∫ θ in (-Real.pi : ℝ)..Real.pi,
        ((a - a * contourCircleCharacter n θ) /
          ((r : ℂ) - (r : ℂ) * contourCircleCharacter 1 θ)).re •
            (I * (r : ℂ) * contourCircleCharacter 1 θ)) +
      (I * (n : ℂ) * a) * circularLogMode r r n := by
  have hf : (fun θ : ℝ => Real.log ‖(r : ℂ) - (r : ℂ) * contourCircleCharacter 1 θ‖ •
      (I * (n : ℂ) * a * contourCircleCharacter n θ)) =
      (fun θ : ℝ => (I * (n : ℂ) * a) *
        ((Real.log ‖(r : ℂ) - (r : ℂ) * contourCircleCharacter 1 θ‖ : ℂ) * contourCircleCharacter n θ)) := by
    funext θ
    rw [Complex.real_smul]
    ring
  have hL : IntervalIntegrable (fun θ : ℝ =>
      Real.log ‖(r : ℂ) - (r : ℂ) * contourCircleCharacter 1 θ‖ •
        (I * (n : ℂ) * a * contourCircleCharacter n θ)) volume (-Real.pi) Real.pi := by
    rw [hf]
    exact (intervalIntegrable_contourCircular_two_radii_logMode hr hr n).const_mul _
  unfold circularContourModeVariation
  rw [intervalIntegral.integral_add hi hL, hf, intervalIntegral.integral_const_mul]
  rfl

set_option maxHeartbeats 600000 in
theorem circularContourModeVariation_self_positive {r : ℝ} (hr : 0 < r)
    (M : ℕ) (hM : 2 ≤ M) (a : ℂ) :
    circularContourModeVariation r r (M : ℤ) a a = I * (Real.pi : ℂ) * (conj a - a) := by
  have hP : Continuous (fun θ : ℝ => ∑ k ∈ Finset.range M, contourCircleCharacter (k : ℤ) θ) :=
    continuous_finset_sum _ (fun k _ => continuous_contourCircleCharacter (k : ℤ))
  obtain ⟨hi, he⟩ := circularSelfRational_of_divided hr (M : ℤ) a _ hP
    (fun θ hθ hn => contourCircleCharacter_divided_positive M θ (contourCircle_unit_chord_ne_zero hθ hn))
  rw [circularContourModeVariation_self_split hr (M : ℤ) a hi, he,
    integral_contourCircular_real_positive_sum (a / (r : ℂ)) hM,
    circularLogMode_positive hr hr (by omega : 0 < M)]
  simp only [min_self, max_self, div_self hr.ne', Complex.ofReal_one, one_pow,
    map_div₀, Complex.conj_ofReal, Int.cast_natCast]
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hMC : (M : ℂ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
  field_simp [hrC, hMC]
  <;> ring

set_option maxHeartbeats 600000 in
theorem circularContourModeVariation_self_negative {r : ℝ} (hr : 0 < r)
    (M : ℕ) (hM : 0 < M) (a : ℂ) :
    circularContourModeVariation r r (-(M : ℤ)) a a = 0 := by
  have hP : Continuous (fun θ : ℝ => -(∑ k ∈ Finset.range M,
      contourCircleCharacter (-((k + 1 : ℕ) : ℤ)) θ)) :=
    (continuous_finset_sum _ (fun k _ => continuous_contourCircleCharacter (-((k + 1 : ℕ) : ℤ)))).neg
  obtain ⟨hi, he⟩ := circularSelfRational_of_divided hr (-(M : ℤ)) a _ hP
    (fun θ hθ hn => contourCircleCharacter_divided_negative M θ (contourCircle_unit_chord_ne_zero hθ hn))
  have hInt : (∫ θ in (-Real.pi : ℝ)..Real.pi,
      (((a / (r : ℂ)) * -(∑ k ∈ Finset.range M,
        contourCircleCharacter (-((k + 1 : ℕ) : ℤ)) θ)).re : ℂ) * contourCircleCharacter 1 θ) =
      (Real.pi : ℂ) * (-(a / (r : ℂ))) := by
    have hf : (fun θ : ℝ =>
        (((a / (r : ℂ)) * -(∑ k ∈ Finset.range M,
          contourCircleCharacter (-((k + 1 : ℕ) : ℤ)) θ)).re : ℂ) * contourCircleCharacter 1 θ) =
        (fun θ : ℝ =>
          (((-(a / (r : ℂ))) * (∑ k ∈ Finset.range M,
            contourCircleCharacter (-((k + 1 : ℕ) : ℤ)) θ)).re : ℂ) * contourCircleCharacter 1 θ) := by
      funext θ
      simp only [mul_neg, neg_mul]
    rw [hf, integral_contourCircular_real_negative_sum _ hM]
  rw [circularContourModeVariation_self_split hr (-(M : ℤ)) a hi, he, hInt,
    circularLogMode_negative hr hr hM]
  simp only [min_self, max_self, div_self hr.ne', Complex.ofReal_one, one_pow,
    Int.cast_neg, Int.cast_natCast]
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hMC : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  field_simp [hrC, hMC]
  <;> ring

end Euler2D

end
