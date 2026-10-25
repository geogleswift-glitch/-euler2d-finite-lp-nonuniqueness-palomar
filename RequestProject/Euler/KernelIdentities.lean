module

public import RequestProject.Euler.CircularCell

/-!
# The gradient kernel (Definition `np:def:kernel`, Lemma `np:kernel-identities`)

For `x ≠ 0` let `k(x) = ∇K(x)` be the gradient of the planar Biot–Savart kernel
`K(x) = Jx/(2π|x|²)`. Direct differentiation gives
`k(x) = (2π)⁻¹ J (|x|⁻² I - 2|x|⁻⁴ x ⊗ x)`.
This file proves the pointwise statements of Lemma `np:kernel-identities`:

* `hasFDerivAt_kernelK`: `K` is differentiable at every `x ≠ 0` with derivative `gradKernel x`;
* `gradKernel_neg`: `k` is even;
* `gradKernel_smul`: `k` is homogeneous of degree `-2`;
* `gradKernel_circle_mean`: `k` has zero mean on the unit circle;
* `norm_gradKernel_le`: `|k(x)| ≤ C|x|⁻²`;
* `norm_fderiv_gradKernel_le`: `|∇k(x)| ≤ C|x|⁻³`.

The distributional identity `∇K = pv k + ½ J δ₀` is not formalized.
-/

@[expose] public section

open MeasureTheory Real Metric

namespace Euler2D

/-- The rotation `J` as a continuous linear map. -/
noncomputable def perpJL : R2 →L[ℝ] R2 :=
  LinearMap.toContinuousLinearMap
    { toFun := perpJ
      map_add' := fun x y => by ext i; fin_cases i <;> (simp [perpJ]; try ring)
      map_smul' := fun c x => perpJ_smul c x }

@[simp] lemma perpJL_apply (x : R2) : perpJL x = perpJ x := rfl

/-- The gradient kernel `k(x) v = (2π)⁻¹ (|x|⁻² J v - 2|x|⁻⁴ ⟨x, v⟩ J x)`. -/
noncomputable def gradKernel (x : R2) : R2 →L[ℝ] R2 :=
  (2 * π)⁻¹ • ((‖x‖ ^ 2)⁻¹ • perpJL -
    (2 * (‖x‖ ^ 2)⁻¹ ^ 2) • (innerSL ℝ x).smulRight (perpJ x))

lemma gradKernel_apply (x v : R2) :
    gradKernel x v = (2 * π)⁻¹ • ((‖x‖ ^ 2)⁻¹ • perpJ v -
      (2 * (‖x‖ ^ 2)⁻¹ ^ 2 * inner ℝ x v) • perpJ x) := by
  simp [gradKernel, smul_smul]

/-- `K` is differentiable away from the origin, with derivative `k`. -/
theorem hasFDerivAt_kernelK {x : R2} (hx : x ≠ 0) : HasFDerivAt kernelK (gradKernel x) x := by
  have hx2 : ‖x‖ ^ 2 ≠ 0 := by positivity
  have h1 : HasFDerivAt (fun y : R2 => 2 * π * ‖y‖ ^ 2) ((2 * π) • (2 • innerSL ℝ x)) x :=
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (2 * π)
  have h1' := (hasFDerivAt_inv (𝕜 := ℝ) (show 2 * π * ‖x‖ ^ 2 ≠ 0 by positivity)).comp x h1
  have h2 := h1'.smul perpJL.hasFDerivAt
  have hker := h2.congr_of_eventuallyEq (f₁ := kernelK)
    (Filter.Eventually.of_forall fun y => by
      simp only [kernelK, Pi.smul_apply', Function.comp_apply, perpJL_apply])
  apply hker.congr_fderiv
  ext v i
  fin_cases i <;>
    simp [gradKernel_apply, perpJ, Function.comp_def] <;>
    field_simp [hx2, Real.pi_ne_zero] <;> ring

/-- `k` is even. -/
theorem gradKernel_neg (x : R2) : gradKernel (-x) = gradKernel x := by
  ext v i
  fin_cases i <;> simp [gradKernel_apply, perpJ, inner_neg_left] <;> ring

/-- `k` is homogeneous of degree `-2`. -/
theorem gradKernel_smul {c : ℝ} (hc : c ≠ 0) (x : R2) :
    gradKernel (c • x) = (c ^ 2)⁻¹ • gradKernel x := by
  ext v i
  fin_cases i <;>
  · simp [gradKernel_apply, perpJ, norm_smul, inner_smul_left, mul_pow, smul_smul]
    field_simp

/-- `k` has zero mean on the unit circle. -/
theorem gradKernel_circle_mean (v : R2) :
    ∫ θ in (0 : ℝ)..(2 * π), gradKernel !₂[Real.cos θ, Real.sin θ] v = 0 := by
  set a : R2 := (2 * π)⁻¹ • !₂[v 0, -v 1]
  set b : R2 := (2 * π)⁻¹ • !₂[-v 1, -v 0]
  have hpt : ∀ θ : ℝ, gradKernel !₂[Real.cos θ, Real.sin θ] v =
      Real.sin (2 * θ) • a + Real.cos (2 * θ) • b := by
    intro θ
    have hn : ‖(!₂[Real.cos θ, Real.sin θ] : R2)‖ = 1 := by
      rw [EuclideanSpace.norm_eq]; simp [Fin.sum_univ_two]
    rw [gradKernel_apply, hn]
    ext i
    have h := Real.sin_sq_add_cos_sq θ
    fin_cases i
    · simp [a, b, perpJ, Real.sin_two_mul, Real.cos_two_mul, EuclideanSpace.inner_eq_star_dotProduct,
        Fin.sum_univ_two, dotProduct]
      linear_combination π⁻¹ * v.ofLp 1 * h
    · simp [a, b, perpJ, Real.sin_two_mul, Real.cos_two_mul, EuclideanSpace.inner_eq_star_dotProduct,
        Fin.sum_univ_two, dotProduct]
      ring
  simp_rw [hpt]
  have hs : ∫ θ in (0 : ℝ)..(2 * π), Real.sin (2 * θ) = 0 := by
    rw [intervalIntegral.integral_comp_mul_left (fun θ => Real.sin θ) two_ne_zero]
    simp [integral_sin]
    have := Real.cos_nat_mul_two_pi 2
    push_cast at this
    linarith
  have hc : ∫ θ in (0 : ℝ)..(2 * π), Real.cos (2 * θ) = 0 := by
    rw [intervalIntegral.integral_comp_mul_left (fun θ => Real.cos θ) two_ne_zero]
    simp [integral_cos]
    have := Real.sin_nat_mul_pi 4
    push_cast at this
    rw [← this]; ring_nf
  rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop), intervalIntegral.integral_smul_const,
    intervalIntegral.integral_smul_const, hs, hc]
  simp

/-- `|k(x)| ≤ C |x|⁻²`, with `C = 3/(2π)`. -/
theorem norm_gradKernel_le (x : R2) : ‖gradKernel x‖ ≤ 3 / (2 * π) * (‖x‖ ^ 2)⁻¹ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  rcases eq_or_ne x 0 with rfl | hx
  · simp [gradKernel_apply]
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hperp : ∀ w : R2, ‖perpJ w‖ = ‖w‖ := by
    intro w
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    simp [perpJ, Fin.sum_univ_two, add_comm]
  rw [gradKernel_apply, norm_smul, norm_inv, Real.norm_of_nonneg (by positivity)]
  have hin : |inner ℝ x v| ≤ ‖x‖ * ‖v‖ := abs_real_inner_le_norm x v
  have key : ‖(‖x‖ ^ 2)⁻¹ • perpJ v - (2 * (‖x‖ ^ 2)⁻¹ ^ 2 * inner ℝ x v) • perpJ x‖ ≤
      3 * (‖x‖ ^ 2)⁻¹ * ‖v‖ := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul, norm_smul, hperp, hperp, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (by positivity), abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * (‖x‖ ^ 2)⁻¹ ^ 2)]
    have : 2 * (‖x‖ ^ 2)⁻¹ ^ 2 * |inner ℝ x v| * ‖x‖ ≤ 2 * (‖x‖ ^ 2)⁻¹ ^ 2 * (‖x‖ * ‖v‖) * ‖x‖ := by
      gcongr
    have e : 2 * (‖x‖ ^ 2)⁻¹ ^ 2 * (‖x‖ * ‖v‖) * ‖x‖ = 2 * (‖x‖ ^ 2)⁻¹ * ‖v‖ := by
      field_simp
    linarith
  calc (2 * π)⁻¹ * ‖(‖x‖ ^ 2)⁻¹ • perpJ v - (2 * (‖x‖ ^ 2)⁻¹ ^ 2 * inner ℝ x v) • perpJ x‖
      ≤ (2 * π)⁻¹ * (3 * (‖x‖ ^ 2)⁻¹ * ‖v‖) := by gcongr
    _ = 3 / (2 * π) * (‖x‖ ^ 2)⁻¹ * ‖v‖ := by ring

/-- `k` is smooth away from the origin. -/
lemma contDiffAt_gradKernel {x : R2} (hx : x ≠ 0) : ContDiffAt ℝ 1 gradKernel x := by
  have hn : ContDiffAt ℝ 1 (fun y : R2 => (‖y‖ ^ 2)⁻¹) x :=
    (contDiff_norm_sq ℝ).contDiffAt.inv (by positivity)
  have hsr : ContDiffAt ℝ 1 (fun y : R2 => (innerSL ℝ y).smulRight (perpJL y)) x :=
    ((innerSL ℝ : R2 →L[ℝ] R2 →L[ℝ] ℝ).contDiff.contDiffAt).smulRight
      perpJL.contDiff.contDiffAt
  have h : gradKernel = fun y : R2 => (2 * π)⁻¹ • ((‖y‖ ^ 2)⁻¹ • perpJL -
      (2 * (‖y‖ ^ 2)⁻¹ ^ 2) • (innerSL ℝ y).smulRight (perpJL y)) := rfl
  have hA : ContDiffAt ℝ 1 (fun y : R2 => (‖y‖ ^ 2)⁻¹ • perpJL) x :=
    hn.smul (contDiffAt_const (c := perpJL))
  have hB : ContDiffAt ℝ 1 (fun y : R2 => 2 * (‖y‖ ^ 2)⁻¹ ^ 2) x :=
    contDiffAt_const.mul (hn.pow 2)
  have hAB := hA.sub (hB.smul hsr)
  rw [h]
  exact hAB.const_smul ((2 * π)⁻¹ : ℝ)

/-- The derivative of `k` is homogeneous of degree `-3`. -/
lemma fderiv_gradKernel_smul {c : ℝ} (hc : 0 < c) {x : R2} (hx : x ≠ 0) :
    fderiv ℝ gradKernel (c • x) = (c ^ 3)⁻¹ • fderiv ℝ gradKernel x := by
  have hcx : c • x ≠ 0 := smul_ne_zero hc.ne' hx
  have hD1 := ((contDiffAt_gradKernel hcx).differentiableAt one_ne_zero).hasFDerivAt
  have hD2 := ((contDiffAt_gradKernel hx).differentiableAt one_ne_zero).hasFDerivAt
  have hL : HasFDerivAt (fun y : R2 => c • y) (c • ContinuousLinearMap.id ℝ R2) x :=
    (ContinuousLinearMap.id ℝ R2).hasFDerivAt.const_smul c
  have h1 : HasFDerivAt (fun y => gradKernel (c • y))
      ((fderiv ℝ gradKernel (c • x)).comp (c • ContinuousLinearMap.id ℝ R2)) x :=
    hD1.comp x hL
  have h2 : HasFDerivAt (fun y => gradKernel (c • y)) ((c ^ 2)⁻¹ • fderiv ℝ gradKernel x) x := by
    have : (fun y => gradKernel (c • y)) = fun y => (c ^ 2)⁻¹ • gradKernel y :=
      funext (gradKernel_smul hc.ne')
    rw [this]
    exact hD2.const_smul ((c ^ 2)⁻¹ : ℝ)
  have heq := h1.unique h2
  have : (fderiv ℝ gradKernel (c • x)).comp (c • ContinuousLinearMap.id ℝ R2) =
      c • fderiv ℝ gradKernel (c • x) := by
    ext v; simp
  rw [this] at heq
  have hc3 : (c ^ 3)⁻¹ = c⁻¹ * (c ^ 2)⁻¹ := by rw [← mul_inv, ← pow_succ']
  rw [hc3, mul_smul, ← heq, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]

/-- `|∇k(x)| ≤ C |x|⁻³` for `x ≠ 0`. -/
theorem norm_fderiv_gradKernel_le :
    ∃ C : ℝ, ∀ x : R2, x ≠ 0 → ‖fderiv ℝ gradKernel x‖ ≤ C * (‖x‖ ^ 3)⁻¹ := by
  have hcont : ContinuousOn (fun x => ‖fderiv ℝ gradKernel x‖) (sphere (0 : R2) 1) := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_mem_sphere hx one_ne_zero
    exact ((contDiffAt_gradKernel hx0).continuousAt_fderiv one_ne_zero).norm.continuousWithinAt
  obtain ⟨C, hC⟩ := (isCompact_sphere (0 : R2) 1).exists_bound_of_continuousOn hcont
  refine ⟨C, fun x hx => ?_⟩
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hu1 : ‖x‖⁻¹ • x ∈ sphere (0 : R2) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hr.ne']
  have hu0 : ‖x‖⁻¹ • x ≠ 0 := ne_of_mem_sphere hu1 one_ne_zero
  have key : fderiv ℝ gradKernel x = (‖x‖ ^ 3)⁻¹ • fderiv ℝ gradKernel (‖x‖⁻¹ • x) := by
    have := fderiv_gradKernel_smul hr hu0
    rwa [smul_smul, mul_inv_cancel₀ hr.ne', one_smul] at this
  have hCu : ‖fderiv ℝ gradKernel (‖x‖⁻¹ • x)‖ ≤ C := (le_abs_self _).trans (hC _ hu1)
  rw [key]
  calc ‖(‖x‖ ^ 3)⁻¹ • fderiv ℝ gradKernel (‖x‖⁻¹ • x)‖
      ≤ ‖(‖x‖ ^ 3)⁻¹‖ * ‖fderiv ℝ gradKernel (‖x‖⁻¹ • x)‖ :=
        ContinuousLinearMap.opNorm_smul_le _ _
    _ = (‖x‖ ^ 3)⁻¹ * ‖fderiv ℝ gradKernel (‖x‖⁻¹ • x)‖ := by
        rw [Real.norm_of_nonneg (by positivity)]
    _ ≤ (‖x‖ ^ 3)⁻¹ * C := mul_le_mul_of_nonneg_left hCu (by positivity)
    _ = C * (‖x‖ ^ 3)⁻¹ := mul_comm _ _

end Euler2D

end
