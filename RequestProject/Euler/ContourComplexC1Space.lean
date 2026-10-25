module

public import RequestProject.Euler.ContourComplexHolderSpace
public import RequestProject.Euler.ContourC1Space

/-! The genuine C¹ derivative graph is stable under actual complex
multiplication of values.  Its complex Banach structure retains the
original norm and real action and is only activated explicitly. -/

@[expose] public section

noncomputable section

open scoped NNReal BoundedContinuousFunction

attribute [local instance] Euler2D.HolderFunctionSpace.complexScalarNormedSpace
attribute [local instance] Euler2D.HolderFunctionSpace.complexScalarTower

namespace Euler2D.ContourC1Space

local instance (priority := 2000) complexC1_baseNormedAddCommGroup (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) :=
  Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)

variable {γ : ℝ≥0}

/-- Actual complex multiplication preserves the actual real derivative
graph, by multiplying its genuine derivative by the same complex value. -/
def complexScale (a : ℂ) (Z : ContourC1Space γ) : ContourC1Space γ :=
  ⟨a • Z.val, by
    intro θ
    change HasDerivAt (fun t : ℝ => a * Z.val.1 (t : ContourCircle))
      (a * Z.val.2 (θ : ContourCircle)) θ
    exact (Z.property θ).const_mul a⟩

@[simp] theorem lift_complexScale (a : ℂ) (Z : ContourC1Space γ) (θ : ℝ) :
    lift γ (complexScale a Z) θ = a * lift γ Z θ := rfl

theorem norm_complexScale_le (a : ℂ) (Z : ContourC1Space γ) :
    ‖complexScale a Z‖ ≤ ‖a‖ * ‖Z‖ := by
  change ‖a • Z.val‖ ≤ ‖a‖ * ‖Z.val‖
  exact norm_smul_le a Z.val

/-- Genuine complex Banach structure on the unchanged C¹ Hölder norm.
This definition is deliberately not a global instance. -/
def complexScalarNormedSpace (γ : ℝ≥0) : NormedSpace ℂ (ContourC1Space γ) where
  smul := complexScale
  one_smul Z := by
    apply Subtype.ext
    change (1 : ℂ) • Z.val = Z.val
    exact one_smul _ _
  mul_smul a b Z := by
    apply Subtype.ext
    change (a * b) • Z.val = a • (b • Z.val)
    exact mul_smul _ _ _
  smul_add a Z W := by
    apply Subtype.ext
    change a • (Z.val + W.val) = a • Z.val + a • W.val
    exact smul_add _ _ _
  smul_zero a := by
    apply Subtype.ext
    change a • (0 : ContourC1Ambient γ) = 0
    exact smul_zero _
  add_smul a b Z := by
    apply Subtype.ext
    change (a + b) • Z.val = a • Z.val + b • Z.val
    exact add_smul _ _ _
  zero_smul Z := by
    apply Subtype.ext
    change (0 : ℂ) • Z.val = 0
    exact zero_smul _ _
  norm_smul_le := norm_complexScale_le

attribute [local instance] complexScalarNormedSpace

theorem norm_complex_smul (a : ℂ) (Z : ContourC1Space γ) :
    ‖a • Z‖ = ‖a‖ * ‖Z‖ := norm_smul a Z

theorem norm_complexScale_eq (a : ℂ) (Z : ContourC1Space γ) :
    ‖complexScale a Z‖ = ‖a‖ * ‖Z‖ := norm_smul a Z

def complexScalarTower (γ : ℝ≥0) : IsScalarTower ℝ ℂ (ContourC1Space γ) where
  smul_assoc r a Z := by
    apply Subtype.ext
    change (r • a) • Z.val = r • (a • Z.val)
    exact smul_assoc _ _ _

attribute [local instance] complexScalarTower

/-- The genuine derivative is complex-linear for the actual scalar action. -/
def complexDerivative (γ : ℝ≥0) : ContourC1Space γ →L[ℂ] ContourHolderSpace γ :=
  LinearMap.mkContinuous
    { toFun := derivative γ
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 (fun Z => by
      change ‖derivative γ Z‖ ≤ 1 * ‖Z‖
      simpa only [one_mul] using norm_derivative_le Z)

@[simp] theorem complexDerivative_apply (γ : ℝ≥0) (Z : ContourC1Space γ) :
    complexDerivative γ Z = derivative γ Z := rfl

def complexToBCF (γ : ℝ≥0) : ContourC1Space γ →L[ℂ] (ContourCircle →ᵇ ℂ) :=
  LinearMap.mkContinuous
    { toFun := toBCF γ
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 (fun Z => by
      change ‖toBCF γ Z‖ ≤ 1 * ‖Z‖
      simpa only [one_mul] using norm_toBCF_le Z)

@[simp] theorem complexToBCF_apply (γ : ℝ≥0) (Z : ContourC1Space γ) :
    complexToBCF γ Z = toBCF γ Z := rfl

def complexEval (γ : ℝ≥0) (x : ContourCircle) : ContourC1Space γ →L[ℂ] ℂ :=
  (BoundedContinuousFunction.evalCLM ℂ x).comp (complexToBCF γ)

@[simp] theorem complexEval_apply (γ : ℝ≥0) (x : ContourCircle) (Z : ContourC1Space γ) :
    complexEval γ x Z = toBCF γ Z x := rfl

end Euler2D.ContourC1Space

end
