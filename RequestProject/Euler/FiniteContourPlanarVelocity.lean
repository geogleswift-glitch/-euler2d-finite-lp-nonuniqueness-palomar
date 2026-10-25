module

public import RequestProject.Euler.ContourPatchVelocityContinuityLimit
public import RequestProject.Euler.BoundedLogVelocityApproximation
public import RequestProject.Euler.ActualTorusCancellation
public import Mathlib.Topology.Order.ProjIcc

/-! The actual finite planar patch velocity, extended only in time by
clamping. Its genuine positive compact smoothings provide the input to
planar particle-flow existence without any torus periodicity hypothesis. -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ContDiff UniformConvergence

namespace Euler2D

def finiteContourPlanarVelocity {γ : ℝ≥0} {ι : Type*} [Fintype ι]
    {T : ℝ} (hT : 0 ≤ T) (g : ι → ℝ)
    (Z : Icc (0 : ℝ) T → ι → ContourC1Space γ) (Z₀ : ι → ContourC1Space γ)
    (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (r i))
    (hsmall : ∀ t i, ‖Z t i - Z₀ i‖ ≤ r i / 4) (t : ℝ) (x : R2) : R2 :=
  complexPhysicalPlane (velocityC
    (finiteContourC1PatchVorticity g (Z (projIcc 0 T hT t)) Z₀ r hr href
      (hsmall (projIcc 0 T hT t))) (complexPhysicalPlane.symm x))

section Actual

variable {γ : ℝ≥0} {ι : Type*} [Fintype ι] {T : ℝ}
  (hT : 0 ≤ T) (g : ι → ℝ)
  (Z : Icc (0 : ℝ) T → ι → ContourC1Space γ) (Z₀ : ι → ContourC1Space γ)
  (r : ι → ℝ) (hr : ∀ i, 0 < r i)
  (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (r i))
  (hsmall : ∀ t i, ‖Z t i - Z₀ i‖ ≤ r i / 4)

theorem finiteContourPlanarVelocity_apply (t : Icc (0 : ℝ) T) (x : ℂ) :
    finiteContourPlanarVelocity hT g Z Z₀ r hr href hsmall t (complexPhysicalPlane x) =
      complexPhysicalPlane (velocityC
        (finiteContourC1PatchVorticity g (Z t) Z₀ r hr href (hsmall t)) x) := by
  unfold finiteContourPlanarVelocity
  simp only [LinearIsometryEquiv.symm_apply_apply]
  exact congrArg (fun u : Icc (0 : ℝ) T => complexPhysicalPlane
    (velocityC (finiteContourC1PatchVorticity g (Z u) Z₀ r hr href (hsmall u)) x))
    (Set.projIcc_val hT t)

set_option maxHeartbeats 600000 in
theorem continuous_finiteContourPlanarVelocity
    (hZ : ∀ i, Continuous (fun t => Z t i)) :
    Continuous (Function.uncurry (finiteContourPlanarVelocity hT g Z Z₀ r hr href hsmall)) := by
  have hv := continuous_finiteContourC1PatchVelocity g hZ Z₀ r hr href hsmall
  have hp : Continuous (fun p : ℝ × R2 =>
      (Set.projIcc 0 T hT p.1, complexPhysicalPlane.symm p.2)) :=
    ((continuous_projIcc (h := hT)).comp continuous_fst).prodMk
      (complexPhysicalPlane.symm.continuous.comp continuous_snd)
  have hc := complexPhysicalPlane.continuous.comp (hv.comp hp)
  exact hc.congr (fun _ => rfl)

theorem norm_finiteContourPlanarVelocity_le (t : ℝ) (x : R2) :
    ‖finiteContourPlanarVelocity hT g Z Z₀ r hr href hsmall t x‖ ≤
      finiteContourPatchSupBound g + finiteContourPatchMassBound g r := by
  unfold finiteContourPlanarVelocity
  rw [LinearIsometryEquiv.norm_map]
  let s := projIcc 0 T hT t
  have hb := velocity_bound_split
    (integrable_finiteContourC1PatchVorticity g (Z s) Z₀ r hr href (hsmall s))
    (abs_finiteContourC1PatchVorticity_le g (Z s) Z₀ r hr href (hsmall s))
    (complexPhysicalPlane.symm x) (d := 1) (by norm_num)
  have hA := integral_abs_finiteContourC1PatchVorticity_le g (Z s) Z₀ r hr href (hsmall s)
  have hi : 0 ≤ ∫ y, |finiteContourC1PatchVorticity g (Z s) Z₀ r hr href (hsmall s) y| :=
    integral_nonneg (fun y => abs_nonneg _)
  have hπ : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  simp only [mul_one] at hb
  exact hb.trans (add_le_add le_rfl ((div_le_self hi hπ).trans hA))

theorem finiteContourPlanarVelocity_logFlowModulus_le
    (t : ℝ) {x y : R2} (hxy : ‖x - y‖ ≤ 1 / 2) :
    ‖finiteContourPlanarVelocity hT g Z Z₀ r hr href hsmall t x -
      finiteContourPlanarVelocity hT g Z Z₀ r hr href hsmall t y‖ ≤
      (8 * (finiteContourPatchSupBound g + finiteContourPatchMassBound g r)) *
        logFlowModulus ‖x - y‖ := by
  unfold finiteContourPlanarVelocity
  rw [← map_sub, LinearIsometryEquiv.norm_map]
  have he := finiteContourPatchVelocity_logFlowModulus_le g (Z (projIcc 0 T hT t)) Z₀ r hr href
    (hsmall _) (x := complexPhysicalPlane.symm x) (y := complexPhysicalPlane.symm y)
    (by simpa only [← map_sub, LinearIsometryEquiv.norm_map] using hxy)
  simpa only [← map_sub, LinearIsometryEquiv.norm_map] using he

theorem exists_smoothApproximation_finiteContourPlanarVelocity
    (hZ : ∀ i, Continuous (fun t => Z t i)) :
    ∃ M C : ℝ≥0, ∃ K : ℕ → ℝ≥0,
      (∀ n, IsBoundedLipschitzVelocity
        (smoothBoundedLogVelocityApproximation (finiteContourPlanarVelocity hT g Z Z₀ r hr href hsmall) n)
          (K n) M) ∧
      (∀ n t, ContDiff ℝ ∞
        (smoothBoundedLogVelocityApproximation (finiteContourPlanarVelocity hT g Z Z₀ r hr href hsmall) n t)) ∧
      (∀ n t x y, ‖x - y‖ ≤ 1 / 2 →
        ‖smoothBoundedLogVelocityApproximation (finiteContourPlanarVelocity hT g Z Z₀ r hr href hsmall) n t x -
          smoothBoundedLogVelocityApproximation (finiteContourPlanarVelocity hT g Z Z₀ r hr href hsmall) n t y‖ ≤
            C * logFlowModulus ‖x - y‖) ∧
      TendstoUniformly (fun n => Function.uncurry
        (smoothBoundedLogVelocityApproximation (finiteContourPlanarVelocity hT g Z Z₀ r hr href hsmall) n))
        (Function.uncurry (finiteContourPlanarVelocity hT g Z Z₀ r hr href hsmall)) atTop := by
  have hB : 0 ≤ finiteContourPatchSupBound g + finiteContourPatchMassBound g r := by
    unfold finiteContourPatchSupBound finiteContourPatchMassBound contourPatchMassBound
    positivity
  let M : ℝ≥0 := NNReal.mk _ hB
  let C : ℝ≥0 := NNReal.mk (8 * (M : ℝ)) (by positivity)
  obtain ⟨K, hK⟩ := exists_smoothBoundedLogVelocityApproximation
    (M := M) (C := C) (continuous_finiteContourPlanarVelocity hT g Z Z₀ r hr href hsmall hZ)
    (norm_finiteContourPlanarVelocity_le hT g Z Z₀ r hr href hsmall)
    (fun t _ _ hxy => finiteContourPlanarVelocity_logFlowModulus_le hT g Z Z₀ r hr href hsmall t hxy)
  exact ⟨M, C, K, hK⟩

end Actual

end Euler2D
