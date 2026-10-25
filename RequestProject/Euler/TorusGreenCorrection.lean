module

public import RequestProject.Euler.SmoothPoisson
public import RequestProject.Euler.TorusKernelSource
public import RequestProject.Euler.PlanarKernelWeak

/-!
# The actual smooth correction of the torus Green kernel

The forcing is the periodized error of the explicit planar cutoff kernel,
with its proved mass and the physical reciprocal-area constant.  Fourier
Poisson inversion constructs its smooth periodic correction.  Adding the
explicit quadratic term gives a harmonic remainder near the kernel pole.
-/

@[expose] public section

noncomputable section

open MeasureTheory Real Set Filter Topology Metric
open scoped ContDiff ENNReal
open Laplacian

namespace Euler2D

/-- Coordinate second derivatives are the genuine Hessian evaluations. -/
lemma pd_pd_eq_hessian {f : R2 → ℝ} (hf : ContDiff ℝ 2 f) (i j : Fin 2) (x : R2) :
    pd i (pd j f) x = fderiv ℝ (fderiv ℝ f) x
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
  have hfd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((hf.fderiv_right (by norm_num) : ContDiff ℝ 1 (fderiv ℝ f)).differentiable one_ne_zero x)
  unfold pd
  rw [fderiv_clm_apply hfd (differentiableAt_const (EuclideanSpace.single j 1))]
  simp

/-- The project's coordinate Laplacian agrees with Mathlib's intrinsic
Laplacian for the actual Euclidean two-dimensional metric. -/
lemma laplacian_eq_pd_sum {f : R2 → ℝ} (hf : ContDiff ℝ 2 f) (x : R2) :
    Δ f x = pd 0 (pd 0 f) x + pd 1 (pd 1 f) x := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f
    (EuclideanSpace.basisFun (Fin 2) ℝ)]
  simp [Fin.sum_univ_two, EuclideanSpace.basisFun_apply, iteratedFDeriv_two_apply,
    pd_pd_eq_hessian hf]

/-- The real forcing associated with the canonical explicit planar error. -/
def canonicalTorusCorrectionSource : R2 → ℝ :=
  torusCorrectionSource localPlanarKernelError

lemma isScalarTest_canonicalTorusCorrectionSource : IsScalarTest canonicalTorusCorrectionSource :=
  isScalarTest_torusCorrectionSource contDiff_localPlanarKernelError
    (fun _ hx => localPlanarKernelError_eq_zero_of_one_le_norm hx)

lemma integral_canonicalTorusCorrectionSource :
    (∫ x in torusBox, canonicalTorusCorrectionSource x) = 0 :=
  integral_torusCorrectionSource contDiff_localPlanarKernelError
    (fun _ hx => localPlanarKernelError_eq_zero_of_one_le_norm hx) integral_localPlanarKernelError

/-- The correction is an explicit Fourier inverse of the actual source. -/
def torusGreenCorrection : R2 → ℝ := smoothPoisson canonicalTorusCorrectionSource

theorem torusGreenCorrection_smooth : ContDiff ℝ ∞ torusGreenCorrection :=
  smoothPoisson_smooth isScalarTest_canonicalTorusCorrectionSource

theorem torusGreenCorrection_periodic : IsTorusPeriodic torusGreenCorrection :=
  smoothPoisson_periodic _

theorem torusGreenCorrection_laplacian (x : R2) :
    Δ torusGreenCorrection x = canonicalTorusCorrectionSource x := by
  rw [laplacian_eq_pd_sum (torusGreenCorrection_smooth.of_le (by decide))]
  exact laplacian_smoothPoisson isScalarTest_canonicalTorusCorrectionSource
    integral_canonicalTorusCorrectionSource x

lemma canonicalTorusCorrectionSource_eq_near_pole {x : R2}
    (hx : x ∈ ball torusCenter (1 / 2)) :
    canonicalTorusCorrectionSource x = -((2 * π) ^ 2)⁻¹ := by
  have hn : ‖x - torusCenter‖ < 1 / 2 := by simpa only [mem_ball, dist_eq_norm] using hx
  have hbox : x ∈ torusBox := norm_sub_center_lt_one_mem_box (by linarith)
  change -periodicCenteredSource localPlanarKernelError x - ((2 * π) ^ 2)⁻¹ = _
  rw [periodicCenteredSource_eq_on_box
    (fun _ hy => localPlanarKernelError_eq_zero_of_one_le_norm hy) hbox,
    localPlanarKernelError_eq_zero_of_norm_lt_half hn]
  simp

/-- The explicit quadratic term removing the constant local Laplacian. -/
def torusGreenQuadratic (x : R2) : ℝ :=
  ‖x - torusCenter‖ ^ 2 / (4 * (2 * π) ^ 2)

lemma torusGreenQuadratic_smooth : ContDiff ℝ ∞ torusGreenQuadratic :=
  ((contDiff_id.sub contDiff_const).norm_sq (𝕜 := ℝ)).div_const _

lemma pd_torusGreenQuadratic (i : Fin 2) (x : R2) :
    pd i torusGreenQuadratic x =
      (2 * (4 * (2 * π) ^ 2)⁻¹) * (x - torusCenter) i := by
  have hz : HasFDerivAt (fun y : R2 => y - torusCenter) (ContinuousLinearMap.id ℝ R2) x :=
    (hasFDerivAt_id (𝕜 := ℝ) x).sub_const torusCenter
  have hd := hz.norm_sq.const_mul ((4 * (2 * π) ^ 2)⁻¹)
  have he : torusGreenQuadratic = fun y =>
      ((4 * (2 * π) ^ 2)⁻¹) * ‖y - torusCenter‖ ^ 2 := by
    funext y
    simp only [torusGreenQuadratic, div_eq_mul_inv]
    ring
  rw [he]
  unfold pd
  rw [hd.fderiv]
  simp [EuclideanSpace.inner_single_right]
  ring

lemma pd_pd_torusGreenQuadratic (i : Fin 2) (x : R2) :
    pd i (pd i torusGreenQuadratic) x = 2 * (4 * (2 * π) ^ 2)⁻¹ := by
  have he : pd i torusGreenQuadratic = fun y : R2 =>
      (2 * (4 * (2 * π) ^ 2)⁻¹) * (y i - torusCenter i) := by
    funext y
    rw [pd_torusGreenQuadratic]
    rfl
  have hd := (((EuclideanSpace.proj i : R2 →L[ℝ] ℝ).hasFDerivAt (x := x)).sub_const
    (torusCenter i)).const_mul (2 * (4 * (2 * π) ^ 2)⁻¹)
  change HasFDerivAt (fun y : R2 => (2 * (4 * (2 * π) ^ 2)⁻¹) *
    (y i - torusCenter i)) _ x at hd
  rw [he]
  unfold pd
  rw [hd.fderiv]
  simp [EuclideanSpace.single_apply]

lemma laplacian_torusGreenQuadratic (x : R2) :
    Δ torusGreenQuadratic x = ((2 * π) ^ 2)⁻¹ := by
  rw [laplacian_eq_pd_sum (torusGreenQuadratic_smooth.of_le (by decide)),
    pd_pd_torusGreenQuadratic, pd_pd_torusGreenQuadratic]
  field_simp [Real.pi_ne_zero]
  ring

/-- The actual smooth local remainder after the singular logarithmic and
constant-curvature terms have been separated. -/
def torusGreenHarmonicRemainder : R2 → ℝ :=
  torusGreenCorrection + torusGreenQuadratic

theorem torusGreenHarmonicRemainder_smooth : ContDiff ℝ ∞ torusGreenHarmonicRemainder :=
  torusGreenCorrection_smooth.add torusGreenQuadratic_smooth

/-- Harmonicity of the constructed remainder is a conclusion, rather than
an additional hypothesis on a Green function. -/
theorem harmonicOnNhd_torusGreenHarmonicRemainder :
    InnerProductSpace.HarmonicOnNhd torusGreenHarmonicRemainder (ball torusCenter (1 / 2)) := by
  have hH : ContDiff ℝ 2 torusGreenCorrection := torusGreenCorrection_smooth.of_le (by decide)
  have hQ : ContDiff ℝ 2 torusGreenQuadratic := torusGreenQuadratic_smooth.of_le (by decide)
  intro x hx
  refine ⟨(torusGreenHarmonicRemainder_smooth.of_le (by decide)).contDiffAt, ?_⟩
  filter_upwards [isOpen_ball.mem_nhds hx] with y hy
  change Δ (torusGreenCorrection + torusGreenQuadratic) y = 0
  rw [hH.contDiffAt.laplacian_add hQ.contDiffAt, torusGreenCorrection_laplacian,
    laplacian_torusGreenQuadratic, canonicalTorusCorrectionSource_eq_near_pole hy]
  simp

end Euler2D

end
