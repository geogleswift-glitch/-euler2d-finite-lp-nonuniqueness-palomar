module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Normed.Operator.NormedSpace

/-! # Differential calculus reflected by a closed isometric linear embedding

The derivative is proved to take values in the closed range, by taking actual
directional difference quotients.  Thus no derivative-range hypothesis or
continuous projection onto the subspace is required.
-/

@[expose] public section

noncomputable section

open Filter Set
open scoped Topology

namespace Euler2D

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace 𝕜 P]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem hasFDerivAt_linearIsometry_iff (i : F →ₗᵢ[𝕜] E) (f : P → F)
    (D : P →L[𝕜] F) (x : P) :
    HasFDerivAt (fun y => i (f y)) (i.toContinuousLinearMap.comp D) x ↔
      HasFDerivAt f D x := by
  have hn (y : P) :
      ‖i (f y) - i (f x) - (i.toContinuousLinearMap.comp D) (y - x)‖ =
        ‖f y - f x - D (y - x)‖ := by
    change ‖i (f y) - i (f x) - i (D (y - x))‖ = _
    rw [← i.map_sub, ← i.map_sub, i.norm_map]
  simp only [hasFDerivAt_iff_tendsto, hn]

theorem linearIsometry_derivative_mem_range (i : F →ₗᵢ[𝕜] E)
    (hi : IsClosed (Set.range i)) {f : P → F} {D : P →L[𝕜] E} {x : P}
    (h : HasFDerivAt (fun y => i (f y)) D x) (v : P) :
    D v ∈ LinearMap.range i.toLinearMap := by
  have hp : HasDerivAt (fun t : 𝕜 => i (f (x + t • v))) (D v) 0 := by
    simpa [Function.comp_def] using h.comp_hasDerivAt_of_eq 0
      (((hasDerivAt_id (0 : 𝕜)).smul_const v).const_add x) (by simp)
  apply hi.mem_of_tendsto hp.tendsto_slope_zero
  exact Filter.Eventually.of_forall fun t =>
    ⟨t⁻¹ • (f (x + (0 + t) • v) - f (x + 0 • v)), by simp⟩

def linearIsometryLiftDerivative (i : F →ₗᵢ[𝕜] E) (D : P →L[𝕜] E)
    (hD : ∀ v, D v ∈ LinearMap.range i.toLinearMap) : P →L[𝕜] F :=
  i.equivRange.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (D.codRestrict (LinearMap.range i.toLinearMap) hD)

theorem linearIsometryLiftDerivative_comp (i : F →ₗᵢ[𝕜] E) (D : P →L[𝕜] E)
    (hD : ∀ v, D v ∈ LinearMap.range i.toLinearMap) :
    i.toContinuousLinearMap.comp (linearIsometryLiftDerivative i D hD) = D := by
  ext v
  exact congrArg Subtype.val (i.equivRange.apply_symm_apply ⟨D v, hD v⟩)

theorem hasFDerivAt_of_closed_linearIsometry (i : F →ₗᵢ[𝕜] E)
    (hi : IsClosed (Set.range i)) {f : P → F} {D : P →L[𝕜] E} {x : P}
    (h : HasFDerivAt (fun y => i (f y)) D x) :
    HasFDerivAt f
      (linearIsometryLiftDerivative i D (linearIsometry_derivative_mem_range i hi h)) x := by
  apply (hasFDerivAt_linearIsometry_iff i f _ x).mp
  rwa [linearIsometryLiftDerivative_comp]

theorem differentiableAt_linearIsometry_iff (i : F →ₗᵢ[𝕜] E)
    (hi : IsClosed (Set.range i)) (f : P → F) (x : P) :
    DifferentiableAt 𝕜 (fun y => i (f y)) x ↔ DifferentiableAt 𝕜 f x := by
  constructor
  · intro h
    exact (hasFDerivAt_of_closed_linearIsometry i hi h.hasFDerivAt).differentiableAt
  · intro h
    exact i.toContinuousLinearMap.differentiableAt.comp x h

theorem linearIsometry_comp_fderiv (i : F →ₗᵢ[𝕜] E)
    (hi : IsClosed (Set.range i)) (f : P → F) (x : P) :
    i.toContinuousLinearMap.comp (fderiv 𝕜 f x) =
      fderiv 𝕜 (fun y => i (f y)) x := by
  by_cases hf : DifferentiableAt 𝕜 f x
  · exact (i.toContinuousLinearMap.hasFDerivAt.comp x hf.hasFDerivAt).fderiv.symm
  · rw [fderiv_zero_of_not_differentiableAt hf]
    have hfi : ¬ DifferentiableAt 𝕜 (fun y => i (f y)) x :=
      fun h => hf ((differentiableAt_linearIsometry_iff i hi f x).mp h)
    rw [fderiv_zero_of_not_differentiableAt hfi]
    ext v
    simp

end Euler2D

end
