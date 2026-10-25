module

public import RequestProject.Euler.ContourHolderAlgebra

/-! # Actual constant Hölder functions and complex value multiplication -/

@[expose] public section

noncomputable section

open Set Filter Topology
open scoped NNReal

namespace Euler2D
namespace HolderFunctionSpace

variable {X : Type*} [MetricSpace X]

def const (γ : ℝ≥0) (a : ℂ) : HolderFunctionSpace X ℂ γ :=
  ofMemHolder (BoundedContinuousFunction.const X a)
    (HolderWith.const : HolderWith 0 γ (Function.const X a)).memHolder

@[simp] theorem const_apply (γ : ℝ≥0) (a : ℂ) (x : X) :
    const (X := X) γ a x = a := rfl

theorem norm_const_le (γ : ℝ≥0) (a : ℂ) : ‖const (X := X) γ a‖ ≤ ‖a‖ := by
  apply norm_le_of_pointwise_holder_bounds (C := ‖a‖₊)
  · intro x
    change ‖a‖ ≤ ‖a‖
    exact le_rfl
  · exact HolderWith.const

/-- Multiplication of the actual complex values, as a real CLM. -/
def valueMulOperator (γ : ℝ≥0) (a : ℂ) :
    HolderFunctionSpace X ℂ γ →L[ℝ] HolderFunctionSpace X ℂ γ :=
  pointwiseMulCLM γ (const γ a)

@[simp] theorem valueMulOperator_apply (γ : ℝ≥0) (a : ℂ)
    (f : HolderFunctionSpace X ℂ γ) (x : X) :
    valueMulOperator γ a f x = a * f x := rfl

theorem norm_valueMulOperator_le (γ : ℝ≥0) (a : ℂ) :
    ‖valueMulOperator (X := X) γ a‖ ≤ 2 * ‖a‖ := by
  apply ContinuousLinearMap.opNorm_le_bound
  · positivity
  · intro f
    change ‖pointwiseMul (const γ a) f‖ ≤ _
    exact (norm_pointwiseMul_le (const γ a) f).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (norm_const_le γ a)
        (by norm_num : (0 : ℝ) ≤ 2)) (norm_nonneg f))

end HolderFunctionSpace
end Euler2D

end
