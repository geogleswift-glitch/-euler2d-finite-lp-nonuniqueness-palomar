module

public import RequestProject.Euler.ActualTorusCancellation
public import RequestProject.Euler.TorusSmoothKernelBounds
public import RequestProject.Euler.VorticityMomentum
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# The actual velocity in the torus remainder cancellation

The real continuous linear map `D ↦ -D(I) + I D(1)` is the perpendicular
gradient under this project's physical complex-coordinate convention.
Moving that actual map through the integral identifies the velocity with
the derivative of the scalar convolution.  Its norm is exactly the
operator norm of that derivative.
-/

@[expose] public section

noncomputable section

open MeasureTheory Complex Metric Set Filter Topology
open scoped ContDiff NNReal ComplexConjugate

namespace Euler2D

theorem norm_cpartial_eq_fderiv (h : ℂ → ℝ) (z : ℂ) :
    ‖cpartial h z‖ = ‖fderiv ℝ h z‖ := by
  apply le_antisymm _ (norm_fderiv_le_cpartial h z)
  by_cases hc : cpartial h z = 0
  · simp only [hc, norm_zero, norm_nonneg]
  have hcpos : 0 < ‖cpartial h z‖ := norm_pos_iff.mpr hc
  have hb := (fderiv ℝ h z).le_opNorm (conj (cpartial h z))
  have he : fderiv ℝ h z (conj (cpartial h z)) = ‖cpartial h z‖ ^ 2 := by
    rw [fderiv_eq_re_cpartial, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  rw [he, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), norm_conj, pow_two] at hb
  exact (mul_le_mul_iff_left₀ hcpos).mp hb

/-- The actual real linear perpendicular-gradient operator in complex
coordinates `x₀+i x₁`. -/
def complexPerpGradientOperator : (ℂ →L[ℝ] ℝ) →L[ℝ] ℂ :=
  -(Complex.ofRealCLM.comp (ContinuousLinearMap.apply ℝ ℝ I)) +
    I • (Complex.ofRealCLM.comp (ContinuousLinearMap.apply ℝ ℝ 1))

@[simp] lemma complexPerpGradientOperator_apply (D : ℂ →L[ℝ] ℝ) :
    complexPerpGradientOperator D = -(D I : ℂ) + I * (D 1 : ℂ) := by
  simp [complexPerpGradientOperator, smul_eq_mul]

lemma complexPerpGradientOperator_eq_cpartial (h : ℂ → ℝ) (z : ℂ) :
    complexPerpGradientOperator (fderiv ℝ h z) = I * conj (cpartial h z) := by
  apply Complex.ext <;> simp [cpartial]

theorem norm_complexPerpGradientOperator (D : ℂ →L[ℝ] ℝ) :
    ‖complexPerpGradientOperator D‖ = ‖D‖ := by
  have he := complexPerpGradientOperator_eq_cpartial (fun z => D z) 0
  have hn := norm_cpartial_eq_fderiv (fun z => D z) 0
  have he' := congrArg norm he
  rw [norm_mul, norm_I, norm_conj, one_mul] at he'
  simpa only [ContinuousLinearMap.fderiv] using he'.trans hn

lemma actualComplexGreenCorrection_smooth : ContDiff ℝ ∞ actualComplexGreenCorrection :=
  torusGreenCorrection_smooth.comp complexTorusPoint_smooth

theorem actualComplexGreenCorrection_global_bounds :
    ∃ C : ℝ≥0, (∀ z, ‖actualComplexGreenCorrection z‖ ≤ C) ∧
      LipschitzWith C actualComplexGreenCorrection := by
  obtain ⟨C, hC, _, hLip⟩ := exists_bounded_lipschitz_of_contDiff_periodic
    (torusGreenCorrection_smooth.of_le (by decide)) torusGreenCorrection_periodic
  refine ⟨C, fun z => hC (complexTorusPoint z), ?_⟩
  have hpoint : LipschitzWith 1 complexTorusPoint := by
    apply LipschitzWith.of_dist_le_mul
    intro z w
    simpa only [complexTorusPoint, dist_add_right] using
      complexPhysicalPlane.lipschitz.dist_le_mul z w
  simpa only [mul_one] using hLip.comp hpoint

namespace ComplexKernelConvolution

variable {h ζ : ℂ → ℝ} {C M : ℝ≥0}
    (hh : ContDiff ℝ 1 h) (hLip : LipschitzWith C h)
    (hM : ∀ z, ‖h z‖ ≤ M) (hζ : Integrable ζ)

include hh hM hζ in
lemma integrable_kernel (x : ℂ) : Integrable (fun y => h (x - y) * ζ y) := by
  apply (hζ.norm.const_mul (M : ℝ)).mono'
  · exact (hh.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable.mul
      hζ.aestronglyMeasurable
  · exact Eventually.of_forall fun y => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)

include hh hLip hζ in
lemma integrable_derivative (x : ℂ) :
    Integrable (fun y => ζ y • fderiv ℝ h (x - y)) := by
  apply (hζ.norm.const_mul (C : ℝ)).mono'
  · exact hζ.aestronglyMeasurable.smul
      ((hh.continuous_fderiv one_ne_zero).comp
        (continuous_const.sub continuous_id)).aestronglyMeasurable
  · exact Eventually.of_forall fun y => by
      rw [norm_smul, mul_comm (C : ℝ)]
      exact mul_le_mul_of_nonneg_left (norm_fderiv_le_of_lipschitz ℝ hLip) (norm_nonneg _)

include hh hLip hM hζ in
theorem hasFDerivAt_convolution (x : ℂ) :
    HasFDerivAt (fun x => ∫ y, h (x - y) * ζ y)
      (∫ y, ζ y • fderiv ℝ h (x - y)) x := by
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun x y => h (x - y) * ζ y)
    (F' := fun x y => ζ y • fderiv ℝ h (x - y))
    (bound := fun y => (C : ℝ) * ‖ζ y‖) (s := univ) (by simp)
  · exact Eventually.of_forall fun x => (integrable_kernel hh hM hζ x).aestronglyMeasurable
  · exact integrable_kernel hh hM hζ x
  · exact (integrable_derivative hh hLip hζ x).aestronglyMeasurable
  · exact Eventually.of_forall fun y x _ => by
      rw [norm_smul, mul_comm (C : ℝ)]
      exact mul_le_mul_of_nonneg_left (norm_fderiv_le_of_lipschitz ℝ hLip) (norm_nonneg _)
  · exact hζ.norm.const_mul _
  · exact Eventually.of_forall fun y x _ => by
      have hd := ((hh.differentiable one_ne_zero _).hasFDerivAt.comp x
        ((hasFDerivAt_id x).sub_const y)).mul_const (ζ y)
      simpa only [ContinuousLinearMap.comp_id] using hd

end ComplexKernelConvolution

theorem hasFDerivAt_actualComplexGreenCorrection_convolution
    {ζ : ℂ → ℝ} (hζ : Integrable ζ) (x : ℂ) :
    HasFDerivAt (fun x => ∫ y, actualComplexGreenCorrection (x - y) * ζ y)
      (∫ y, ζ y • fderiv ℝ actualComplexGreenCorrection (x - y)) x := by
  obtain ⟨C, hC, hLip⟩ := actualComplexGreenCorrection_global_bounds
  exact ComplexKernelConvolution.hasFDerivAt_convolution
    (actualComplexGreenCorrection_smooth.of_le (by decide)) hLip hC hζ x

lemma integrable_actualComplexGreenCorrection_derivative
    {ζ : ℂ → ℝ} (hζ : Integrable ζ) (x : ℂ) :
    Integrable (fun y => ζ y • fderiv ℝ actualComplexGreenCorrection (x - y)) := by
  obtain ⟨C, _, hLip⟩ := actualComplexGreenCorrection_global_bounds
  exact ComplexKernelConvolution.integrable_derivative
    (actualComplexGreenCorrection_smooth.of_le (by decide)) hLip hζ x

lemma hasFDerivAt_complexTorusPoint (z : ℂ) :
    HasFDerivAt complexTorusPoint complexPhysicalPlane.toLinearIsometry.toContinuousLinearMap z :=
  complexPhysicalPlane.toLinearIsometry.toContinuousLinearMap.hasFDerivAt.add_const torusCenter

lemma fderiv_actualComplexGreenCorrection_apply (z w : ℂ) :
    fderiv ℝ actualComplexGreenCorrection z w =
      fderiv ℝ torusGreenCorrection (complexTorusPoint z) (complexPhysicalPlane w) := by
  have hd := (torusGreenCorrection_smooth.differentiable (by simp) (complexTorusPoint z)).hasFDerivAt.comp z
    (hasFDerivAt_complexTorusPoint z)
  change HasFDerivAt actualComplexGreenCorrection _ z at hd
  rw [hd.fderiv]
  rfl

/-- The actual physical correction velocity, using `x₀+i x₁` coordinates. -/
def actualComplexRemainderKernel (z : ℂ) : ℂ :=
  planeComplexEquiv (perpGradient torusGreenCorrection (complexTorusPoint z))

lemma actualComplexRemainderKernel_eq_operator (z : ℂ) :
    actualComplexRemainderKernel z =
      complexPerpGradientOperator (fderiv ℝ actualComplexGreenCorrection z) := by
  rw [complexPerpGradientOperator_apply, fderiv_actualComplexGreenCorrection_apply,
    fderiv_actualComplexGreenCorrection_apply, complexPhysicalPlane_I, complexPhysicalPlane_one]
  simp only [actualComplexRemainderKernel, planeComplexEquiv_apply,
    perpGradient_zero, perpGradient_one, pd, Complex.ofReal_neg]
  ring

/-- The actual velocity integral equals the perpendicular gradient of
the actual scalar convolution, by continuous linearity of the integral. -/
theorem integral_actualComplexRemainderKernel_eq_derivative
    {ζ : ℂ → ℝ} (hζ : Integrable ζ) (x : ℂ) :
    (∫ y, ζ y • actualComplexRemainderKernel (x - y)) =
      complexPerpGradientOperator
        (fderiv ℝ (fun x => ∫ y, actualComplexGreenCorrection (x - y) * ζ y) x) := by
  have hi := integrable_actualComplexGreenCorrection_derivative hζ x
  calc
    _ = ∫ y, complexPerpGradientOperator
        (ζ y • fderiv ℝ actualComplexGreenCorrection (x - y)) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun y => by
        dsimp only
        rw [map_smul, actualComplexRemainderKernel_eq_operator]
    _ = complexPerpGradientOperator (∫ y, ζ y • fderiv ℝ actualComplexGreenCorrection (x - y)) :=
      complexPerpGradientOperator.integral_comp_comm hi
    _ = _ := by rw [(hasFDerivAt_actualComplexGreenCorrection_convolution hζ x).fderiv]

theorem norm_integral_actualComplexRemainderKernel
    {ζ : ℂ → ℝ} (hζ : Integrable ζ) (x : ℂ) :
    ‖∫ y, ζ y • actualComplexRemainderKernel (x - y)‖ =
      ‖fderiv ℝ (fun x => ∫ y, actualComplexGreenCorrection (x - y) * ζ y) x‖ := by
  rw [integral_actualComplexRemainderKernel_eq_derivative hζ, norm_complexPerpGradientOperator]

/-- Cubic cancellation directly for the genuine velocity of the constructed
torus correction, with all derivatives identified by true integral formulas. -/
theorem actual_torusRemainderVelocity_cancellation {a : ℝ}
    (ha : 0 < a) (ha16 : a ≤ 1 / 16) :
    ∃ K : ℝ, 0 < K ∧ ∀ ζ : ℂ → ℝ, Integrable ζ →
      (∀ y, a < ‖y‖ → ζ y = 0) → (∀ y, ζ (I * y) = ζ y) →
      (∫ y, ζ y) = 0 → ∀ x : ℂ, ‖x‖ ≤ a →
        ‖∫ y, ζ y • actualComplexRemainderKernel (x - y)‖ ≤
          K * ‖x‖ ^ 3 * ∫ y, ‖y‖ ^ 4 * |ζ y| := by
  obtain ⟨K, hK0, hK⟩ := actual_torusGreenCorrection_cancellation ha ha16
  refine ⟨K, hK0, fun ζ hζ hsupp hsym hmass x hx => ?_⟩
  rw [norm_integral_actualComplexRemainderKernel hζ]
  exact hK ζ hζ hsupp hsym hmass x hx

lemma complexPhysicalPlane_symm_eq_planeComplexEquiv (x : R2) :
    complexPhysicalPlane.symm x = planeComplexEquiv x := by
  have he : complexPhysicalPlane (planeComplexEquiv x) = x := by
    rw [complexPhysicalPlane_eq_planeComplexEquiv_symm, planeComplexEquiv.symm_apply_apply]
  exact (congrArg complexPhysicalPlane.symm he).symm.trans
    (complexPhysicalPlane.symm_apply_apply (planeComplexEquiv x))

/-- The same actual velocity integral, now retaining the physical `R2`
codomain.  The coordinate change is the proved linear isometry. -/
theorem norm_integral_physicalTorusRemainderVelocity
    {ζ : ℂ → ℝ} (hζ : Integrable ζ) (x : ℂ) :
    ‖∫ y, ζ y • perpGradient torusGreenCorrection (complexTorusPoint (x - y))‖ =
      ‖fderiv ℝ (fun x => ∫ y, actualComplexGreenCorrection (x - y) * ζ y) x‖ := by
  have he : (∫ y, ζ y • actualComplexRemainderKernel (x - y)) =
      complexPhysicalPlane.symm
        (∫ y, ζ y • perpGradient torusGreenCorrection (complexTorusPoint (x - y))) := by
    calc
      _ = ∫ y, complexPhysicalPlane.symm
          (ζ y • perpGradient torusGreenCorrection (complexTorusPoint (x - y))) := by
        apply integral_congr_ae
        exact Eventually.of_forall fun y => by
          dsimp only
          rw [map_smul, complexPhysicalPlane_symm_eq_planeComplexEquiv]
          rfl
      _ = _ := complexPhysicalPlane.symm.toLinearIsometry.integral_comp_comm _
  have hn := congrArg norm he
  rw [LinearIsometryEquiv.norm_map] at hn
  exact hn.symm.trans (norm_integral_actualComplexRemainderKernel hζ x)

/-- Cubic cancellation directly for the genuine physical correction
velocity, without any assumption that a Green function or gradient exists. -/
theorem actual_physicalTorusRemainderVelocity_cancellation {a : ℝ}
    (ha : 0 < a) (ha16 : a ≤ 1 / 16) :
    ∃ K : ℝ, 0 < K ∧ ∀ ζ : ℂ → ℝ, Integrable ζ →
      (∀ y, a < ‖y‖ → ζ y = 0) → (∀ y, ζ (I * y) = ζ y) →
      (∫ y, ζ y) = 0 → ∀ x : ℂ, ‖x‖ ≤ a →
        ‖∫ y, ζ y • perpGradient torusGreenCorrection (complexTorusPoint (x - y))‖ ≤
          K * ‖x‖ ^ 3 * ∫ y, ‖y‖ ^ 4 * |ζ y| := by
  obtain ⟨K, hK0, hK⟩ := actual_torusGreenCorrection_cancellation ha ha16
  refine ⟨K, hK0, fun ζ hζ hsupp hsym hmass x hx => ?_⟩
  rw [norm_integral_physicalTorusRemainderVelocity hζ]
  exact hK ζ hζ hsupp hsym hmass x hx

end Euler2D

end
