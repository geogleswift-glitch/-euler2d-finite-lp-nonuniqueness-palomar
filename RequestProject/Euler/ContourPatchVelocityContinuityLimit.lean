module

public import RequestProject.Euler.ContourPatchVelocityContinuity

/-! The actual singular velocity is a uniform limit, on the whole
physical plane and on every parameter value, of continuous genuine
regularized Green integrals. -/

@[expose] public section

noncomputable section

open Complex Set Filter Topology MeasureTheory
open scoped NNReal UniformConvergence

namespace Euler2D

theorem tendstoUniformly_contourC1RegularizedPatchVelocity
    {P : Type*} {γ : ℝ≥0} (Z : P → ContourC1Space γ) (Z₀ : ContourC1Space γ)
    {r : ℝ} (hr : 0 < r) (href : ContourC1Space.lift γ Z₀ = refCircle r)
    (hsmall : ∀ p, ‖Z p - Z₀‖ ≤ r / 4) :
    TendstoUniformly
      (fun (n : ℕ) (p : P × ℂ) => contourC1RegularizedPatchVelocity (Z p.1)
        ((1 / ((n : ℝ) + 1)) ^ 2) p.2)
      (fun p : P × ℂ => velocityC (contourC1PatchVorticity (Z p.1) Z₀ hr href (hsmall p.1)) p.2)
      atTop := by
  have hlim : Tendsto (fun n : ℕ => contourPatchVelocityApproximationBound r *
      (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (contourPatchVelocityApproximationBound r))
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [(tendsto_order.mp hlim).2 ε hε] with n hn p
  rw [dist_eq_norm]
  exact (norm_contourC1PatchVelocity_sub_regularized_le (Z p.1) Z₀ hr href (hsmall p.1)
    (by positivity : 0 < 1 / ((n : ℝ) + 1)) p.2).trans_lt hn

theorem continuous_contourC1PatchVelocity
    {P : Type*} [TopologicalSpace P] {γ : ℝ≥0}
    {Z : P → ContourC1Space γ} (hZ : Continuous Z) (Z₀ : ContourC1Space γ)
    {r : ℝ} (hr : 0 < r) (href : ContourC1Space.lift γ Z₀ = refCircle r)
    (hsmall : ∀ p, ‖Z p - Z₀‖ ≤ r / 4) :
    Continuous (fun p : P × ℂ =>
      velocityC (contourC1PatchVorticity (Z p.1) Z₀ hr href (hsmall p.1)) p.2) := by
  apply (tendstoUniformly_contourC1RegularizedPatchVelocity Z Z₀ hr href hsmall).continuous
  exact Frequently.of_forall (fun n => continuous_contourC1RegularizedPatchVelocity hZ
    (pow_ne_zero 2 (by positivity : (1 / ((n : ℝ) + 1)) ≠ 0)))

theorem continuous_finiteContourC1PatchVelocity
    {P : Type*} [TopologicalSpace P] {γ : ℝ≥0} {ι : Type*} [Fintype ι]
    (g : ι → ℝ) {Z : P → ι → ContourC1Space γ}
    (hZ : ∀ i, Continuous (fun p => Z p i)) (Z₀ : ι → ContourC1Space γ)
    (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (r i))
    (hsmall : ∀ p i, ‖Z p i - Z₀ i‖ ≤ r i / 4) :
    Continuous (fun p : P × ℂ => velocityC
      (finiteContourC1PatchVorticity g (Z p.1) Z₀ r hr href (hsmall p.1)) p.2) := by
  have he : (fun p : P × ℂ => velocityC
      (finiteContourC1PatchVorticity g (Z p.1) Z₀ r hr href (hsmall p.1)) p.2) =
      (fun p : P × ℂ => ∑ i, (g i : ℂ) * velocityC
        (contourC1PatchVorticity (Z p.1 i) (Z₀ i) (hr i) (href i) (hsmall p.1 i)) p.2) := by
    funext p
    exact velocityC_finite_sum_smul g _ (fun _ => 1)
      (fun i => integrable_contourC1PatchVorticity _ _ _ _ _)
      (fun i => abs_contourC1PatchVorticity_le_one _ _ _ _ _) p.2
  rw [he]
  exact continuous_finset_sum _ (fun i _ => continuous_const.mul
    (continuous_contourC1PatchVelocity (hZ i) (Z₀ i) (hr i) (href i) (fun p => hsmall p i)))

end Euler2D
