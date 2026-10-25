module

public import RequestProject.Euler.LittleContourSpace

/-! # Actual joint evaluation of contours and their actual derivatives -/

@[expose] public section

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal BoundedContinuousFunction

namespace Euler2D

namespace HolderFunctionSpace

variable {X E : Type*} [MetricSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem continuous_eval_uncurry (γ : ℝ≥0) :
    Continuous (fun p : HolderFunctionSpace X E γ × X => p.1 p.2) := by
  exact (continuous_eval : Continuous (fun p : (X →ᵇ E) × X => p.1 p.2)).comp
    (((toBCF γ).continuous.comp continuous_fst).prodMk continuous_snd)

end HolderFunctionSpace

namespace ContourC1Space

theorem continuous_eval_uncurry (γ : ℝ≥0) :
    Continuous (fun p : ContourC1Space γ × ContourCircle => toBCF γ p.1 p.2) := by
  exact (continuous_eval : Continuous (fun p : (ContourCircle →ᵇ ℂ) × ContourCircle =>
    p.1 p.2)).comp (((toBCF γ).continuous.comp continuous_fst).prodMk continuous_snd)

theorem continuous_derivativeEval_uncurry (γ : ℝ≥0) :
    Continuous (fun p : ContourC1Space γ × ContourCircle => derivative γ p.1 p.2) := by
  exact (HolderFunctionSpace.continuous_eval_uncurry γ).comp
    (((derivative γ).continuous.comp continuous_fst).prodMk continuous_snd)

theorem continuous_lift_uncurry (γ : ℝ≥0) :
    Continuous (fun p : ContourC1Space γ × ℝ => lift γ p.1 p.2) := by
  exact (continuous_eval_uncurry γ).comp
    (continuous_fst.prodMk ((AddCircle.continuous_mk' (2 * Real.pi)).comp continuous_snd))

theorem continuous_deriv_lift_uncurry (γ : ℝ≥0) :
    Continuous (fun p : ContourC1Space γ × ℝ => deriv (lift γ p.1) p.2) := by
  have hc := (continuous_derivativeEval_uncurry γ).comp
    (continuous_fst.prodMk ((AddCircle.continuous_mk' (2 * Real.pi)).comp continuous_snd))
  exact hc.congr (fun p => (deriv_lift p.1 p.2).symm)

end ContourC1Space

namespace LittleContourSpace

theorem continuous_lift_uncurry (γ : ℝ≥0) :
    Continuous (fun p : LittleContourSpace γ × ℝ => lift γ p.1 p.2) := by
  exact (ContourC1Space.continuous_lift_uncurry γ).comp
    (((inclusion γ).continuous.comp continuous_fst).prodMk continuous_snd)

theorem continuous_deriv_lift_uncurry (γ : ℝ≥0) :
    Continuous (fun p : LittleContourSpace γ × ℝ => deriv (lift γ p.1) p.2) := by
  exact (ContourC1Space.continuous_deriv_lift_uncurry γ).comp
    (((inclusion γ).continuous.comp continuous_fst).prodMk continuous_snd)

end LittleContourSpace

end Euler2D

end
