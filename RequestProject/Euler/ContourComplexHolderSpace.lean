module

public import RequestProject.Euler.ContourHolderScalar

/-!
# The actual complex Banach structure on the unchanged Hölder space

The complex scalar operation is genuine multiplication of the complex
values.  Its sharp bound uses the real Hölder graph norm already present.
The resulting structure is a definition, not a global instance: callers
explicitly activate it with `letI`, leaving existing real instances intact.
-/

@[expose] public section

noncomputable section

open Set Filter Topology
open scoped NNReal

namespace Euler2D.HolderFunctionSpace

variable {X : Type*} [MetricSpace X] {γ : ℝ≥0}

theorem norm_valueMulOperator_apply_le (a : ℂ) (f : HolderFunctionSpace X ℂ γ) :
    ‖valueMulOperator γ a f‖ ≤ ‖a‖ * ‖f‖ := by
  have hb : ‖valueMulOperator γ a f‖ ≤ (‖f‖₊ * ‖a‖₊ : ℝ≥0) := by
    apply norm_le_of_pointwise_holder_bounds
    · intro x
      rw [valueMulOperator_apply, norm_mul, NNReal.coe_mul, coe_nnnorm, coe_nnnorm,
        mul_comm ‖f‖]
      exact mul_le_mul_of_nonneg_left (norm_eval_le f x) (norm_nonneg a)
    · simpa only [Pi.smul_def, smul_eq_mul, valueMulOperator_apply] using
        (HolderWith.smul a (HolderFunctionSpace.holderWith f))
  simpa only [NNReal.coe_mul, coe_nnnorm, mul_comm] using hb

/-- Actual complex scalar multiplication, with the original norm and
underlying real Hölder graph.  This is deliberately not a global instance. -/
def complexScalarNormedSpace (γ : ℝ≥0) : NormedSpace ℂ (HolderFunctionSpace X ℂ γ) where
  smul a f := valueMulOperator γ a f
  one_smul f := by
    apply HolderFunctionSpace.ext
    intro x
    change (1 : ℂ) * f x = f x
    exact one_mul _
  mul_smul a b f := by
    apply HolderFunctionSpace.ext
    intro x
    change (a * b) * f x = a * (b * f x)
    exact mul_assoc _ _ _
  smul_add a f g := by
    apply HolderFunctionSpace.ext
    intro x
    change a * (f x + g x) = a * f x + a * g x
    exact mul_add _ _ _
  smul_zero a := by
    apply HolderFunctionSpace.ext
    intro x
    change a * 0 = 0
    exact mul_zero _
  add_smul a b f := by
    apply HolderFunctionSpace.ext
    intro x
    change (a + b) * f x = a * f x + b * f x
    exact add_mul _ _ _
  zero_smul f := by
    apply HolderFunctionSpace.ext
    intro x
    change (0 : ℂ) * f x = 0
    exact zero_mul _
  norm_smul_le := norm_valueMulOperator_apply_le

attribute [local instance] complexScalarNormedSpace

@[simp] theorem complex_smul_apply (a : ℂ) (f : HolderFunctionSpace X ℂ γ) (x : X) :
    (a • f) x = a * f x := rfl

theorem norm_complex_smul (a : ℂ) (f : HolderFunctionSpace X ℂ γ) :
    ‖a • f‖ = ‖a‖ * ‖f‖ := norm_smul a f

theorem norm_valueMulOperator_apply_eq (a : ℂ) (f : HolderFunctionSpace X ℂ γ) :
    ‖valueMulOperator γ a f‖ = ‖a‖ * ‖f‖ := norm_smul a f

/-- Compatibility with the original, unchanged real scalar action. -/
def complexScalarTower (γ : ℝ≥0) : IsScalarTower ℝ ℂ (HolderFunctionSpace X ℂ γ) where
  smul_assoc r a f := by
    apply HolderFunctionSpace.ext
    intro x
    change (r • a) * f x = r • (a * f x)
    rw [Complex.real_smul, Complex.real_smul, mul_assoc]

attribute [local instance] complexScalarTower

/-- Genuine complex-linear evaluation for the actual complex structure. -/
def complexEval (γ : ℝ≥0) (x : X) : HolderFunctionSpace X ℂ γ →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => f x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 (fun f => by
      change ‖f x‖ ≤ 1 * ‖f‖
      simpa only [one_mul] using norm_eval_le f x)

@[simp] theorem complexEval_apply (γ : ℝ≥0) (x : X) (f : HolderFunctionSpace X ℂ γ) :
    complexEval γ x f = f x := rfl

/-- The already constructed bounded real product is genuinely complex
bilinear for this actual complex scalar multiplication. -/
def complexPointwiseMulLM (γ : ℝ≥0) :
    HolderFunctionSpace X ℂ γ →ₗ[ℂ] HolderFunctionSpace X ℂ γ →ₗ[ℂ]
      HolderFunctionSpace X ℂ γ where
  toFun f :=
    { toFun := pointwiseMul f
      map_add' := by
        intro g h
        apply HolderFunctionSpace.ext
        intro x
        change f x * (g x + h x) = f x * g x + f x * h x
        exact mul_add _ _ _
      map_smul' := by
        intro a g
        apply HolderFunctionSpace.ext
        intro x
        change f x * (a * g x) = a * (f x * g x)
        ring }
  map_add' := by
    intro f g
    apply LinearMap.ext
    intro h
    apply HolderFunctionSpace.ext
    intro x
    change (f x + g x) * h x = f x * h x + g x * h x
    exact add_mul _ _ _
  map_smul' := by
    intro a f
    apply LinearMap.ext
    intro h
    apply HolderFunctionSpace.ext
    intro x
    change (a * f x) * h x = a * (f x * h x)
    exact mul_assoc _ _ _

def complexPointwiseMulCLM (γ : ℝ≥0) :
    HolderFunctionSpace X ℂ γ →L[ℂ] HolderFunctionSpace X ℂ γ →L[ℂ]
      HolderFunctionSpace X ℂ γ :=
  (complexPointwiseMulLM γ).mkContinuous₂ 2 norm_pointwiseMul_le

@[simp] theorem complexPointwiseMulCLM_apply (γ : ℝ≥0)
    (f g : HolderFunctionSpace X ℂ γ) : complexPointwiseMulCLM γ f g = pointwiseMul f g := rfl

end Euler2D.HolderFunctionSpace

end
