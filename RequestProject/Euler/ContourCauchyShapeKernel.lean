module

public import RequestProject.Euler.ContourNormalizedChord

/-! # Actual anisotropic differences of the contour Cauchy remainder -/

@[expose] public section

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal BoundedContinuousFunction

namespace Euler2D

open HolderFunctionSpace

def contourCauchyShapeUniformConstant (c M : ℝ) : ℝ := 1 / c + M / c ^ 2

def contourCauchyShapeParameterConstant (c M : ℝ) : ℝ :=
  2 * inverseBound c M + 8 * M * (inverseBound c M) ^ 2

theorem contourCauchyShapeUniformConstant_nonneg {c M : ℝ} (hc : 0 < c) (hM : 0 ≤ M) :
    0 ≤ contourCauchyShapeUniformConstant c M := by
  unfold contourCauchyShapeUniformConstant
  positivity

theorem contourCauchyShapeParameterConstant_nonneg {c M : ℝ} (hc : 0 < c) (hM : 0 ≤ M) :
    0 ≤ contourCauchyShapeParameterConstant c M := by
  have hB := (inverseBound_pos hc M).le
  unfold contourCauchyShapeParameterConstant
  positivity

theorem norm_contourNormalizedChord_lower {γ : ℝ≥0} (hγ : 0 < (γ : ℝ))
    (Z : ContourC1Space γ) {c τ : ℝ} (hτ : τ ≠ 0)
    (hchord : ∀ θ, c * |τ| ≤
      ‖ContourC1Space.lift γ Z θ - ContourC1Space.lift γ Z (θ + τ)‖)
    (x : ContourCircle) : c ≤ ‖contourNormalizedChord hγ Z τ x‖ := by
  obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective x
  rw [contourNormalizedChord_apply, contourNormalizedChordFunction_coe Z hτ,
    norm_smul, Real.norm_eq_abs, abs_inv]
  calc
    c = |τ|⁻¹ * (c * |τ|) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (hchord θ) (inv_nonneg.mpr (abs_nonneg _))

/-- A genuine Hölder-norm estimate for a difference of two actual quotients. -/
theorem norm_divideOfNormLower_sub_le_uniform {γ : ℝ≥0}
    (f g a b : ContourHolderSpace γ) {c M δ : ℝ} (hc : 0 < c) (hM : 0 ≤ M)
    (ha : ∀ x, c ≤ ‖a x‖) (hb : ∀ x, c ≤ ‖b x‖)
    (hg : ‖g‖ ≤ M) (haM : ‖a‖ ≤ M) (hbM : ‖b‖ ≤ M)
    (hfg : ‖f - g‖ ≤ δ) (hab : ‖a - b‖ ≤ δ) :
    ‖divideOfNormLower f a hc ha - divideOfNormLower g b hc hb‖ ≤
      contourCauchyShapeParameterConstant c M * δ := by
  let ia := inverseOfNormLower a hc ha
  let ib := inverseOfNormLower b hc hb
  have hB := (inverseBound_pos hc M).le
  have hδ : 0 ≤ δ := (norm_nonneg _).trans hfg
  have hia : ‖ia‖ ≤ inverseBound c M := norm_inverseOfNormLower_le_uniform a hc ha haM
  have hib : ‖ia - ib‖ ≤ (4 * (inverseBound c M) ^ 2) * δ :=
    (norm_sub_inverseOfNormLower_le_uniform a b hc ha hb haM hbM).trans
      (mul_le_mul_of_nonneg_left hab (by positivity))
  have he : divideOfNormLower f a hc ha - divideOfNormLower g b hc hb =
      pointwiseMul (f - g) ia + pointwiseMul g (ia - ib) := by
    apply HolderFunctionSpace.ext
    intro x
    change f x * ia x - g x * ib x = (f x - g x) * ia x + g x * (ia x - ib x)
    ring
  rw [he]
  calc
    _ ≤ ‖pointwiseMul (f - g) ia‖ + ‖pointwiseMul g (ia - ib)‖ := norm_add_le _ _
    _ ≤ 2 * ‖f - g‖ * ‖ia‖ + 2 * ‖g‖ * ‖ia - ib‖ :=
      add_le_add (norm_pointwiseMul_le _ _) (norm_pointwiseMul_le _ _)
    _ ≤ 2 * δ * inverseBound c M + 2 * M * ((4 * (inverseBound c M) ^ 2) * δ) := by
      apply add_le_add
      · exact mul_le_mul (mul_le_mul_of_nonneg_left hfg (by norm_num)) hia
          (norm_nonneg _) (by positivity)
      · exact mul_le_mul (mul_le_mul_of_nonneg_left hg (by norm_num)) hib
          (norm_nonneg _) (by positivity)
    _ = _ := by unfold contourCauchyShapeParameterConstant; ring

def contourNormalizedKernelQuotient {γ : ℝ≥0} (hγ : 0 < (γ : ℝ))
    (Z : ContourC1Space γ) {c τ : ℝ} (hc : 0 < c) (hτ : τ ≠ 0)
    (hchord : ∀ θ, c * |τ| ≤
      ‖ContourC1Space.lift γ Z θ - ContourC1Space.lift γ Z (θ + τ)‖) : ContourHolderSpace γ :=
  divideOfNormLower (contourHolderShift (ContourC1Space.derivative γ Z) τ)
    (contourNormalizedChord hγ Z τ) hc (norm_contourNormalizedChord_lower hγ Z hτ hchord)

theorem contourNormalizedKernelQuotient_coe {γ : ℝ≥0} (hγ : 0 < (γ : ℝ))
    (Z : ContourC1Space γ) {c τ : ℝ} (hc : 0 < c) (hτ : τ ≠ 0)
    (hchord : ∀ θ, c * |τ| ≤
      ‖ContourC1Space.lift γ Z θ - ContourC1Space.lift γ Z (θ + τ)‖) (θ : ℝ) :
    contourNormalizedKernelQuotient hγ Z hc hτ hchord (θ : ContourCircle) =
      deriv (ContourC1Space.lift γ Z) (θ + τ) /
        contourNormalizedChord hγ Z τ (θ : ContourCircle) := by
  simp only [contourNormalizedKernelQuotient, divideOfNormLower_apply,
    contourHolderShift_apply, ContourC1Space.deriv_lift, AddCircle.coe_add]

theorem contourCauchyPoleIntegrand_eq_normalized {γ : ℝ≥0} (hγ : 0 < (γ : ℝ))
    (Z : ContourC1Space γ) {τ : ℝ} (hτ : τ ≠ 0) (θ : ℝ) :
    contourCauchyPoleIntegrand (ContourC1Space.lift γ Z) (deriv (ContourC1Space.lift γ Z)) θ τ =
      (τ : ℂ)⁻¹ * (deriv (ContourC1Space.lift γ Z) (θ + τ) /
        contourNormalizedChord hγ Z τ (θ : ContourCircle) + 1) := by
  rw [contourNormalizedChord_apply, contourNormalizedChordFunction_coe Z hτ, Complex.real_smul]
  simp only [Complex.ofReal_inv]
  unfold contourCauchyPoleIntegrand
  have ht : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ
  by_cases hd : ContourC1Space.lift γ Z θ - ContourC1Space.lift γ Z (θ + τ) = 0
  · simp [hd]
  · field_simp

theorem norm_contourNormalizedKernelQuotient_sub_le {γ : ℝ≥0} (hγ : 0 < (γ : ℝ))
    (Z W : ContourC1Space γ) {c M τ : ℝ} (hc : 0 < c) (hM : 0 ≤ M) (hτ : τ ≠ 0)
    (hZ : ∀ θ, c * |τ| ≤
      ‖ContourC1Space.lift γ Z θ - ContourC1Space.lift γ Z (θ + τ)‖)
    (hW : ∀ θ, c * |τ| ≤
      ‖ContourC1Space.lift γ W θ - ContourC1Space.lift γ W (θ + τ)‖)
    (hZM : ‖Z‖ ≤ M) (hWM : ‖W‖ ≤ M) :
    ‖contourNormalizedKernelQuotient hγ Z hc hτ hZ -
      contourNormalizedKernelQuotient hγ W hc hτ hW‖ ≤
      contourCauchyShapeParameterConstant c M * ‖Z - W‖ := by
  apply norm_divideOfNormLower_sub_le_uniform _ _ _ _ hc hM
    (norm_contourNormalizedChord_lower hγ Z hτ hZ)
    (norm_contourNormalizedChord_lower hγ W hτ hW)
  · exact (norm_contourHolderShift_le _ τ).trans ((ContourC1Space.norm_derivative_le W).trans hWM)
  · exact (norm_contourNormalizedChord_le hγ Z τ).trans hZM
  · exact (norm_contourNormalizedChord_le hγ W τ).trans hWM
  · rw [← contourHolderShift_sub, ← map_sub]
    exact (norm_contourHolderShift_le _ τ).trans (ContourC1Space.norm_derivative_le (Z - W))
  · exact norm_contourNormalizedChord_sub_le hγ Z W τ

/-- Actual Hölder variation in the base point, with the curve difference retained. -/
theorem norm_contourCauchyPoleIntegrand_shape_parameter_sub_le {γ : ℝ≥0}
    (hγ : 0 < (γ : ℝ)) (Z W : ContourC1Space γ) {c M θ η τ : ℝ}
    (hc : 0 < c) (hM : 0 ≤ M)
    (hZ : ∀ s, c * |τ| ≤ ‖ContourC1Space.lift γ Z s - ContourC1Space.lift γ Z (s + τ)‖)
    (hW : ∀ s, c * |τ| ≤ ‖ContourC1Space.lift γ W s - ContourC1Space.lift γ W (s + τ)‖)
    (hZM : ‖Z‖ ≤ M) (hWM : ‖W‖ ≤ M) :
    ‖(contourCauchyPoleIntegrand (ContourC1Space.lift γ Z) (deriv (ContourC1Space.lift γ Z)) θ τ -
        contourCauchyPoleIntegrand (ContourC1Space.lift γ W) (deriv (ContourC1Space.lift γ W)) θ τ) -
      (contourCauchyPoleIntegrand (ContourC1Space.lift γ Z) (deriv (ContourC1Space.lift γ Z)) η τ -
        contourCauchyPoleIntegrand (ContourC1Space.lift γ W) (deriv (ContourC1Space.lift γ W)) η τ)‖ ≤
      (contourCauchyShapeParameterConstant c M * ‖Z - W‖) * |θ - η| ^ (γ : ℝ) / |τ| := by
  by_cases hτ : τ = 0
  · subst τ
    simp [contourCauchyPoleIntegrand]
  let q := contourNormalizedKernelQuotient hγ Z hc hτ hZ -
    contourNormalizedKernelQuotient hγ W hc hτ hW
  have hq : ‖q‖ ≤ contourCauchyShapeParameterConstant c M * ‖Z - W‖ :=
    norm_contourNormalizedKernelQuotient_sub_le hγ Z W hc hM hτ hZ hW hZM hWM
  have hb := (norm_contourHolder_lift_sub_global_le q θ η).trans
    (mul_le_mul_of_nonneg_right hq (Real.rpow_nonneg (abs_nonneg _) _))
  have he : (contourCauchyPoleIntegrand (ContourC1Space.lift γ Z) (deriv (ContourC1Space.lift γ Z)) θ τ -
        contourCauchyPoleIntegrand (ContourC1Space.lift γ W) (deriv (ContourC1Space.lift γ W)) θ τ) -
      (contourCauchyPoleIntegrand (ContourC1Space.lift γ Z) (deriv (ContourC1Space.lift γ Z)) η τ -
        contourCauchyPoleIntegrand (ContourC1Space.lift γ W) (deriv (ContourC1Space.lift γ W)) η τ) =
      (τ : ℂ)⁻¹ * (q (θ : ContourCircle) - q (η : ContourCircle)) := by
    simp only [contourCauchyPoleIntegrand_eq_normalized hγ _ hτ,
      q, HolderFunctionSpace.sub_apply, contourNormalizedKernelQuotient_coe]
    ring
  rw [he, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs]
  simpa only [div_eq_mul_inv, mul_comm] using
    mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (abs_nonneg τ))

theorem norm_complex_div_sub_div_le {e f a b : ℂ} {c : ℝ} (hc : 0 < c)
    (ha : c ≤ ‖a‖) (hb : c ≤ ‖b‖) :
    ‖e / a - f / b‖ ≤ ‖e - f‖ / c + ‖f‖ * ‖a - b‖ / c ^ 2 := by
  have hna : a ≠ 0 := norm_pos_iff.mp (hc.trans_le ha)
  have hnb : b ≠ 0 := norm_pos_iff.mp (hc.trans_le hb)
  have hinv : ‖a⁻¹ - b⁻¹‖ ≤ ‖a - b‖ / c ^ 2 := by
    have he : ‖a⁻¹ - b⁻¹‖ = ‖a - b‖ / (‖a‖ * ‖b‖) := by
      simpa only [dist_eq_norm] using dist_inv_inv₀ hna hnb
    rw [he]
    exact div_le_div_of_nonneg_left (norm_nonneg _) (sq_pos_of_pos hc)
      (by simpa only [pow_two] using mul_le_mul ha hb hc.le (norm_nonneg a))
  have he : e / a - f / b = (e - f) / a + f * (a⁻¹ - b⁻¹) := by
    simp only [div_eq_mul_inv]
    ring
  rw [he]
  calc
    _ ≤ ‖(e - f) / a‖ + ‖f * (a⁻¹ - b⁻¹)‖ := norm_add_le _ _
    _ = ‖e - f‖ / ‖a‖ + ‖f‖ * ‖a⁻¹ - b⁻¹‖ := by rw [norm_div, norm_mul]
    _ ≤ ‖e - f‖ / c + ‖f‖ * (‖a - b‖ / c ^ 2) :=
      add_le_add (div_le_div_of_nonneg_left (norm_nonneg _) hc ha)
        (mul_le_mul_of_nonneg_left hinv (norm_nonneg _))
    _ = _ := by ring

/-- Taylor cancellation gives the integrable small-increment bound with
the actual norm of the difference of the curves. -/
theorem norm_contourCauchyPoleIntegrand_shape_sub_le {γ : ℝ≥0}
    (hγ : 0 < (γ : ℝ)) (Z W : ContourC1Space γ) {c M θ τ : ℝ}
    (hc : 0 < c) (hM : 0 ≤ M)
    (hZ : ∀ s, c * |τ| ≤ ‖ContourC1Space.lift γ Z s - ContourC1Space.lift γ Z (s + τ)‖)
    (hW : ∀ s, c * |τ| ≤ ‖ContourC1Space.lift γ W s - ContourC1Space.lift γ W (s + τ)‖)
    (hWM : ‖W‖ ≤ M) :
    ‖contourCauchyPoleIntegrand (ContourC1Space.lift γ Z) (deriv (ContourC1Space.lift γ Z)) θ τ -
      contourCauchyPoleIntegrand (ContourC1Space.lift γ W) (deriv (ContourC1Space.lift γ W)) θ τ‖ ≤
      (contourCauchyShapeUniformConstant c M * ‖Z - W‖) * |τ| ^ ((γ : ℝ) - 1) := by
  by_cases hτ : τ = 0
  · subst τ
    simp only [contourCauchyPoleIntegrand, add_zero, sub_self, div_zero,
      Complex.ofReal_zero, inv_zero, add_zero, norm_zero]
    exact mul_nonneg (mul_nonneg (contourCauchyShapeUniformConstant_nonneg hc hM)
      (norm_nonneg _)) (Real.rpow_nonneg (abs_nonneg _) _)
  let a := contourNormalizedChord hγ Z τ (θ : ContourCircle)
  let b := contourNormalizedChord hγ W τ (θ : ContourCircle)
  let e := deriv (ContourC1Space.lift γ Z) (θ + τ) + a
  let f := deriv (ContourC1Space.lift γ W) (θ + τ) + b
  have ha : c ≤ ‖a‖ := norm_contourNormalizedChord_lower hγ Z hτ hZ _
  have hb : c ≤ ‖b‖ := norm_contourNormalizedChord_lower hγ W hτ hW _
  have hna : a ≠ 0 := norm_pos_iff.mp (hc.trans_le ha)
  have hnb : b ≠ 0 := norm_pos_iff.mp (hc.trans_le hb)
  have hab : ‖a - b‖ ≤ ‖Z - W‖ :=
    (HolderFunctionSpace.norm_eval_le
      (contourNormalizedChord hγ Z τ - contourNormalizedChord hγ W τ) _).trans
        (norm_contourNormalizedChord_sub_le hγ Z W τ)
  have hf : ‖f‖ ≤ M * |τ| ^ (γ : ℝ) :=
    (norm_contourNormalizedChord_error_le hγ W hτ θ).trans
      (mul_le_mul_of_nonneg_right hWM (Real.rpow_nonneg (abs_nonneg _) _))
  have hef : ‖e - f‖ ≤ ‖Z - W‖ * |τ| ^ (γ : ℝ) := by
    have ht := norm_contourNormalizedChord_error_le hγ (Z - W) hτ θ
    have heq : deriv (ContourC1Space.lift γ (Z - W)) (θ + τ) +
        contourNormalizedChord hγ (Z - W) τ (θ : ContourCircle) = e - f := by
      rw [ContourC1Space.deriv_lift, map_sub, HolderFunctionSpace.sub_apply,
        contourNormalizedChord_sub, HolderFunctionSpace.sub_apply]
      dsimp only [e, f, a, b]
      rw [ContourC1Space.deriv_lift, ContourC1Space.deriv_lift]
      ring
    rwa [heq] at ht
  have hquot : ‖e / a - f / b‖ ≤
      (‖Z - W‖ * |τ| ^ (γ : ℝ)) / c +
        (M * |τ| ^ (γ : ℝ)) * ‖Z - W‖ / c ^ 2 := by
    apply (norm_complex_div_sub_div_le hc ha hb).trans
    apply add_le_add (div_le_div_of_nonneg_right hef hc.le)
    exact div_le_div_of_nonneg_right (mul_le_mul hf hab (norm_nonneg _) (by positivity)) (sq_nonneg c)
  have heq : contourCauchyPoleIntegrand (ContourC1Space.lift γ Z)
        (deriv (ContourC1Space.lift γ Z)) θ τ -
      contourCauchyPoleIntegrand (ContourC1Space.lift γ W)
        (deriv (ContourC1Space.lift γ W)) θ τ = (τ : ℂ)⁻¹ * (e / a - f / b) := by
    rw [contourCauchyPoleIntegrand_eq_normalized hγ Z hτ,
      contourCauchyPoleIntegrand_eq_normalized hγ W hτ]
    change (τ : ℂ)⁻¹ * (deriv (ContourC1Space.lift γ Z) (θ + τ) / a + 1) -
      (τ : ℂ)⁻¹ * (deriv (ContourC1Space.lift γ W) (θ + τ) / b + 1) = _
    dsimp only [e, f]
    field_simp
    <;> ring
  rw [heq, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ |τ|⁻¹ * ((‖Z - W‖ * |τ| ^ (γ : ℝ)) / c +
        (M * |τ| ^ (γ : ℝ)) * ‖Z - W‖ / c ^ 2) :=
      mul_le_mul_of_nonneg_left hquot (inv_nonneg.mpr (abs_nonneg _))
    _ = _ := by
      rw [Real.rpow_sub_one (abs_pos.mpr hτ).ne']
      unfold contourCauchyShapeUniformConstant
      ring

end Euler2D

end
