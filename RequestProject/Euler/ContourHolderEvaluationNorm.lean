module

public import RequestProject.Euler.ContourComplexHolderSpace

/-! Evaluation at the parameter is itself Hölder continuous in operator
norm on the actual Hölder function space. -/

@[expose] public section

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal

namespace Euler2D.HolderFunctionSpace

variable {X : Type*} [MetricSpace X] {γ : ℝ≥0}

theorem norm_eval_sub_eval_le (x y : X) :
    ‖(eval γ (E := ℂ) x) - eval γ y‖ ≤ dist x y ^ (γ : ℝ) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.rpow_nonneg dist_nonneg _)
  intro f
  simpa only [ContinuousLinearMap.sub_apply, eval_apply, mul_comm] using norm_sub_le_holder f x y

theorem holderWith_eval : HolderWith 1 γ (fun x : X => eval γ (E := ℂ) x) := by
  intro x y
  rw [edist_nndist, edist_nndist, ← ENNReal.coe_rpow_of_nonneg _ γ.coe_nonneg,
    ← ENNReal.coe_mul, ENNReal.coe_le_coe]
  have hb : dist (eval γ (E := ℂ) x) (eval γ y) ≤
      (1 : ℝ) * dist x y ^ (γ : ℝ) := by
    simpa only [dist_eq_norm, one_mul] using norm_eval_sub_eval_le (γ := γ) x y
  exact_mod_cast hb

theorem continuous_eval_operator (hγ : 0 < (γ : ℝ)) :
    Continuous (fun x : X => eval γ (E := ℂ) x) :=
  (holderWith_eval (X := X) (γ := γ)).continuous (by exact_mod_cast hγ)

end Euler2D.HolderFunctionSpace

end
