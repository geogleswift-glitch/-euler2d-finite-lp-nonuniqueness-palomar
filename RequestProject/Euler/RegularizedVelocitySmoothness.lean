module

public import RequestProject.Euler.RegularizedParticleExistence
public import RequestProject.Euler.SpatialC1ParticleFlow
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Spatial regularity of the actual label integral

The derivative is obtained by differentiating the weighted kernel integral.
Its joint continuity uses the actual integrable bound supplied by the global
Lipschitz constant of the kernel.  In particular, the smoothness and
divergence conditions used for particle volume preservation are conclusions
about the constructed velocity, not additional assumptions about that flow.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal ContDiff BoundedContinuousFunction

namespace Euler2D

/-- The genuine integral of the spatial derivatives of the kernel. -/
def regularizedLabelDerivative (K : R2 → R2) (w : R2 → ℝ)
    (η : ParticleDisplacement) (x : R2) : R2 →L[ℝ] R2 :=
  ∫ b, w b • fderiv ℝ K (x - (b + η b) + torusCenter) ∂μT

namespace RegularizedVelocityRegularity

variable {K : R2 → R2} {w : R2 → ℝ} {L : ℝ≥0}
    (hKC1 : ContDiff ℝ 1 K) (hKL : LipschitzWith L K) (hw : Integrable w μT)

include hKC1 hw in
lemma aestronglyMeasurable_label_derivative (η : ParticleDisplacement) (x : R2) :
    AEStronglyMeasurable
      (fun b => w b • fderiv ℝ K (x - (b + η b) + torusCenter)) μT := by
  exact hw.aestronglyMeasurable.smul
    ((hKC1.continuous_fderiv one_ne_zero).comp
      ((continuous_const.sub (continuous_id.add η.continuous)).add continuous_const)).aestronglyMeasurable

include hKL in
lemma norm_label_derivative_le (η : ParticleDisplacement) (x b : R2) :
    ‖w b • fderiv ℝ K (x - (b + η b) + torusCenter)‖ ≤ (L : ℝ) * ‖w b‖ := by
  rw [norm_smul, mul_comm (L : ℝ)]
  exact mul_le_mul_of_nonneg_left (norm_fderiv_le_of_lipschitz ℝ hKL) (norm_nonneg _)

include hKC1 hKL hw in
lemma integrable_label_derivative (η : ParticleDisplacement) (x : R2) :
    Integrable (fun b => w b • fderiv ℝ K (x - (b + η b) + torusCenter)) μT := by
  exact (hw.norm.const_mul (L : ℝ)).mono'
    (aestronglyMeasurable_label_derivative hKC1 hw η x)
    (Eventually.of_forall fun b => norm_label_derivative_le hKL η x b)

end RegularizedVelocityRegularity

theorem hasFDerivAt_regularizedLabelVelocity {K : R2 → R2} {w : R2 → ℝ}
    {L M : ℝ≥0} (hKC1 : ContDiff ℝ 1 K) (hKL : LipschitzWith L K)
    (hM : ∀ x, ‖K x‖ ≤ M) (hw : Integrable w μT)
    (η : ParticleDisplacement) (x : R2) :
    HasFDerivAt (regularizedLabelVelocity K w η) (regularizedLabelDerivative K w η x) x := by
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := μT)
    (F := fun x b => w b • K (x - (b + η b) + torusCenter))
    (F' := fun x b => w b • fderiv ℝ K (x - (b + η b) + torusCenter))
    (bound := fun b => (L : ℝ) * ‖w b‖) (s := univ) (by simp)
  · exact Eventually.of_forall fun y =>
      (RegularizedParticleConstruction.integrable_label_integrand hKL hM hw η y).aestronglyMeasurable
  · exact RegularizedParticleConstruction.integrable_label_integrand hKL hM hw η x
  · exact RegularizedVelocityRegularity.aestronglyMeasurable_label_derivative hKC1 hw η x
  · exact Eventually.of_forall fun b y _ =>
      RegularizedVelocityRegularity.norm_label_derivative_le hKL η y b
  · exact hw.norm.const_mul _
  · exact Eventually.of_forall fun b y _ => by
      have hd := ((hKC1.differentiable one_ne_zero _).hasFDerivAt.comp y
        (((hasFDerivAt_id y).sub_const (b + η b)).add_const torusCenter)).const_smul (w b)
      simpa only [Pi.smul_def, Function.comp_def, id_eq, ContinuousLinearMap.comp_id] using hd

theorem fderiv_regularizedLabelVelocity {K : R2 → R2} {w : R2 → ℝ}
    {L M : ℝ≥0} (hKC1 : ContDiff ℝ 1 K) (hKL : LipschitzWith L K)
    (hM : ∀ x, ‖K x‖ ≤ M) (hw : Integrable w μT)
    (η : ParticleDisplacement) (x : R2) :
    fderiv ℝ (regularizedLabelVelocity K w η) x = regularizedLabelDerivative K w η x :=
  (hasFDerivAt_regularizedLabelVelocity hKC1 hKL hM hw η x).fderiv

/-- Joint continuity needs no time derivative of the displacement curve. -/
theorem continuous_regularizedLabelDerivative {K : R2 → R2} {w : R2 → ℝ}
    {L : ℝ≥0} (hKC1 : ContDiff ℝ 1 K) (hKL : LipschitzWith L K)
    (hw : Integrable w μT) {η : ℝ → ParticleDisplacement} (hη : Continuous η) :
    Continuous (fun p : ℝ × R2 => regularizedLabelDerivative K w (η p.1) p.2) := by
  apply continuous_of_dominated
    (F := fun p : ℝ × R2 => fun b =>
      w b • fderiv ℝ K (p.2 - (b + η p.1 b) + torusCenter))
    (bound := fun b => (L : ℝ) * ‖w b‖)
  · intro p
    exact RegularizedVelocityRegularity.aestronglyMeasurable_label_derivative hKC1 hw _ _
  · intro p
    exact Eventually.of_forall fun b =>
      RegularizedVelocityRegularity.norm_label_derivative_le hKL _ _ b
  · exact hw.norm.const_mul _
  · exact Eventually.of_forall fun b => by
      have harg : Continuous (fun p : ℝ × R2 =>
          p.2 - (b + η p.1 b) + torusCenter) := by fun_prop
      simpa only [Pi.smul_def, Function.comp_def] using
        ((hKC1.continuous_fderiv one_ne_zero).comp harg).const_smul (w b)

theorem isC1SpatialVelocity_regularizedLabelVelocity {K : R2 → R2} {w : R2 → ℝ}
    {L M : ℝ≥0} (hKC1 : ContDiff ℝ 1 K) (hKL : LipschitzWith L K)
    (hM : ∀ x, ‖K x‖ ≤ M) (hw : Integrable w μT)
    {η : ℝ → ParticleDisplacement} (hη : Continuous η) :
    IsC1SpatialVelocity (fun t x => regularizedLabelVelocity K w (η t) x) where
  differentiable t x := (hasFDerivAt_regularizedLabelVelocity hKC1 hKL hM hw (η t) x).differentiableAt
  continuous_fderiv := by
    simp_rw [fderiv_regularizedLabelVelocity hKC1 hKL hM hw]
    exact continuous_regularizedLabelDerivative hKC1 hKL hw hη

theorem pd_regularizedLabelVelocity {K : R2 → R2} {w : R2 → ℝ}
    {L M : ℝ≥0} (hKC1 : ContDiff ℝ 1 K) (hKL : LipschitzWith L K)
    (hM : ∀ x, ‖K x‖ ≤ M) (hw : Integrable w μT)
    (η : ParticleDisplacement) (x : R2) (i j : Fin 2) :
    pd i (regularizedLabelVelocity K w η) x j =
      ∫ b, w b * pd i K (x - (b + η b) + torusCenter) j ∂μT := by
  have hi := RegularizedVelocityRegularity.integrable_label_derivative hKC1 hKL hw η x
  unfold pd
  rw [fderiv_regularizedLabelVelocity hKC1 hKL hM hw]
  unfold regularizedLabelDerivative
  rw [ContinuousLinearMap.integral_apply hi]
  have he := (EuclideanSpace.proj j : R2 →L[ℝ] ℝ).integral_comp_comm
    (hi.apply_continuousLinearMap (EuclideanSpace.single i 1))
  simpa only [ContinuousLinearMap.smul_apply, PiLp.proj_apply,
    PiLp.smul_apply, smul_eq_mul] using he.symm

/-- Pointwise vanishing divergence of the kernel passes to the actual driver. -/
theorem divergence_regularizedLabelVelocity {K : R2 → R2} {w : R2 → ℝ}
    {L M : ℝ≥0} (hKC1 : ContDiff ℝ 1 K) (hKL : LipschitzWith L K)
    (hM : ∀ x, ‖K x‖ ≤ M) (hw : Integrable w μT)
    (hdiv : ∀ x, pd 0 K x 0 + pd 1 K x 1 = 0)
    (η : ParticleDisplacement) (x : R2) :
    pd 0 (regularizedLabelVelocity K w η) x 0 +
      pd 1 (regularizedLabelVelocity K w η) x 1 = 0 := by
  have hi := RegularizedVelocityRegularity.integrable_label_derivative hKC1 hKL hw η x
  have hint (i j : Fin 2) : Integrable
      (fun b => w b * pd i K (x - (b + η b) + torusCenter) j) μT := by
    simpa only [pd, ContinuousLinearMap.smul_apply, PiLp.proj_apply,
      PiLp.smul_apply, smul_eq_mul] using
      (EuclideanSpace.proj j : R2 →L[ℝ] ℝ).integrable_comp
        (hi.apply_continuousLinearMap (EuclideanSpace.single i 1))
  rw [pd_regularizedLabelVelocity hKC1 hKL hM hw, pd_regularizedLabelVelocity hKC1 hKL hM hw,
    ← integral_add (hint 0 0) (hint 1 1)]
  simp_rw [← mul_add, hdiv, mul_zero]
  simp

end Euler2D

end
