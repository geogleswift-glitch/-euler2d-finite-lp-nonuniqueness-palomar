module

public import RequestProject.Euler.ContourFanGreen

/-! Smooth logarithmic potentials with their actual real gradients and
the uniform locally integrable inverse-distance bound. -/

@[expose] public section

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ComplexConjugate ContDiff

namespace Euler2D

def regularizedLogPotential (x : ℂ) (δ : ℝ) (y : ℂ) : ℝ :=
  (1 / 2) * Real.log (δ ^ 2 + ‖y - x‖ ^ 2)

def regularizedLogPotentialDerivative (x : ℂ) (δ : ℝ) (y : ℂ) : ℂ →L[ℝ] ℝ :=
  (δ ^ 2 + ‖y - x‖ ^ 2)⁻¹ • innerSL ℝ (y - x)

def regularizedLogGradient (x : ℂ) (δ : ℝ) (y : ℂ) : ℂ :=
  (δ ^ 2 + ‖y - x‖ ^ 2)⁻¹ • (y - x)

theorem complexRealGradient_innerSL (w : ℂ) :
    complexRealGradient (innerSL ℝ w) = w := by
  apply Complex.ext <;>
    simp [complexRealGradient, innerSL_apply_apply, Complex.inner]

theorem complexRealGradient_smul (a : ℝ) (l : ℂ →L[ℝ] ℝ) :
    complexRealGradient (a • l) = a • complexRealGradient l := by
  apply Complex.ext <;> simp [complexRealGradient, Complex.real_smul] <;> ring

theorem complexRealGradient_regularizedLogPotentialDerivative (x : ℂ) (δ : ℝ) (y : ℂ) :
    complexRealGradient (regularizedLogPotentialDerivative x δ y) =
      regularizedLogGradient x δ y := by
  rw [regularizedLogPotentialDerivative, complexRealGradient_smul, complexRealGradient_innerSL]
  rfl

theorem hasFDerivAt_regularizedLogPotential (x : ℂ) {δ : ℝ} (hδ : δ ≠ 0) (y : ℂ) :
    HasFDerivAt (regularizedLogPotential x δ) (regularizedLogPotentialDerivative x δ y) y := by
  have hpos : 0 < δ ^ 2 + ‖y - x‖ ^ 2 :=
    add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hδ) (sq_nonneg _)
  have hd := (((hasFDerivAt_id y).sub_const x).norm_sq.const_add (δ ^ 2)).log hpos.ne'
  have hh := hd.const_mul (1 / 2 : ℝ)
  convert hh using 1
  ext w
  simp [regularizedLogPotentialDerivative, innerSL_apply_apply]
  ring

theorem contDiff_regularizedLogPotential (x : ℂ) {δ : ℝ} (hδ : δ ≠ 0) :
    ContDiff ℝ ∞ (regularizedLogPotential x δ) := by
  have hn : ContDiff ℝ ∞ (fun y : ℂ => δ ^ 2 + ‖y - x‖ ^ 2) :=
    contDiff_const.add ((contDiff_id.sub contDiff_const).norm_sq ℝ)
  exact contDiff_const.mul (hn.log (fun y => (add_pos_of_pos_of_nonneg
    (sq_pos_of_ne_zero hδ) (sq_nonneg ‖y - x‖)).ne'))

theorem continuous_regularizedLogPotentialDerivative (x : ℂ) {δ : ℝ} (hδ : δ ≠ 0) :
    Continuous (regularizedLogPotentialDerivative x δ) := by
  have hn : Continuous (fun y : ℂ => δ ^ 2 + ‖y - x‖ ^ 2) :=
    continuous_const.add ((continuous_id.sub continuous_const).norm.pow 2)
  exact (hn.inv₀ (fun y => (add_pos_of_pos_of_nonneg
    (sq_pos_of_ne_zero hδ) (sq_nonneg ‖y - x‖)).ne')).smul
      ((innerSL ℝ).continuous.comp (continuous_id.sub continuous_const))

theorem norm_regularizedLogGradient_le (x : ℂ) (δ : ℝ) (y : ℂ) :
    ‖regularizedLogGradient x δ y‖ ≤ ‖y - x‖⁻¹ := by
  by_cases hw : y - x = 0
  · simp [regularizedLogGradient, hw]
  have hr : 0 < ‖y - x‖ := norm_pos_iff.mpr hw
  have hd : 0 < δ ^ 2 + ‖y - x‖ ^ 2 :=
    add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hr)
  rw [regularizedLogGradient, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr hd.le)]
  calc
    _ = ‖y - x‖ / (δ ^ 2 + ‖y - x‖ ^ 2) := by ring
    _ ≤ ‖y - x‖ / ‖y - x‖ ^ 2 :=
      div_le_div_of_nonneg_left hr.le (sq_pos_of_pos hr) (le_add_of_nonneg_left (sq_nonneg δ))
    _ = ‖y - x‖⁻¹ := by rw [pow_two]; field_simp

theorem tendsto_regularizedLogGradient {ι : Type*} {l : Filter ι} {δ : ι → ℝ}
    (hδ : Tendsto δ l (𝓝 0)) (x y : ℂ) :
    Tendsto (fun i => regularizedLogGradient x (δ i) y) l
      (𝓝 ((‖y - x‖ ^ 2)⁻¹ • (y - x))) := by
  by_cases hw : y - x = 0
  · simpa only [regularizedLogGradient, hw, smul_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ι => (0 : ℂ)) l (𝓝 0))
  have hn : ‖y - x‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hw)
  have hd : Tendsto (fun i => δ i ^ 2 + ‖y - x‖ ^ 2) l (𝓝 (‖y - x‖ ^ 2)) := by
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add] using
      (hδ.pow 2).add tendsto_const_nhds
  exact (hd.inv₀ hn).smul tendsto_const_nhds

theorem measurable_regularizedLogGradient (x : ℂ) (δ : ℝ) :
    Measurable (regularizedLogGradient x δ) :=
  (measurable_const.add ((measurable_id.sub measurable_const).norm.pow_const 2)).inv.smul
    (measurable_id.sub measurable_const)

/-- The actual regularized gradient integrals converge whenever the
genuine inverse-distance singularity is integrable. -/
theorem tendsto_integral_regularizedLogGradient {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] {δ : ι → ℝ} (hδ : Tendsto δ l (𝓝 0))
    (x : ℂ) {μ : Measure ℂ} (hdom : Integrable (fun y => ‖y - x‖⁻¹) μ) :
    Tendsto (fun i => ∫ y, regularizedLogGradient x (δ i) y ∂μ) l
      (𝓝 (∫ y, (‖y - x‖ ^ 2)⁻¹ • (y - x) ∂μ)) := by
  exact tendsto_integral_filter_of_dominated_convergence (fun y => ‖y - x‖⁻¹)
    (Eventually.of_forall (fun i => (measurable_regularizedLogGradient x (δ i)).aestronglyMeasurable))
    (Eventually.of_forall (fun i => ae_of_all μ (norm_regularizedLogGradient_le x (δ i))))
    hdom (ae_of_all μ (fun y => tendsto_regularizedLogGradient hδ x y))

end Euler2D

end
