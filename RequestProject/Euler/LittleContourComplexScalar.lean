module

public import RequestProject.Euler.ContourComplexC1Space
public import RequestProject.Euler.LittleContourSpace

/-! Actual complex multiplication preserves the genuine smooth closure.
The norm and the real action are exactly the original little norm and
real action. Complex instances are explicitly activated by users. -/

@[expose] public section

set_option maxHeartbeats 2200000

noncomputable section

open Set Topology
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) valueScalarC1_group (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) := Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)
local instance (priority := 2000) valueScalarC1_space (γ : ℝ≥0) :
    NormedSpace ℝ (ContourC1Space γ) := Submodule.normedSpace (contourC1GraphSubmodule γ)
local instance (priority := 2000) valueScalarLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) valueScalarLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

attribute [local instance] ContourC1Space.complexScalarNormedSpace ContourC1Space.complexScalarTower

def contourComplexValueMulC1CLM (γ : ℝ≥0) (a : ℂ) : ContourC1Space γ →L[ℝ] ContourC1Space γ :=
  LinearMap.mkContinuous
    { toFun := ContourC1Space.complexScale a
      map_add' := fun Z W => by exact smul_add a Z W
      map_smul' := fun c Z => by exact smul_comm a c Z }
    ‖a‖ (fun Z => ContourC1Space.norm_complexScale_le a Z)

theorem complexScale_preserves_little {γ : ℝ≥0} (a : ℂ) {Z : ContourC1Space γ}
    (hZ : Z ∈ LittleContourSpace γ) : ContourC1Space.complexScale a Z ∈ LittleContourSpace γ := by
  have hclosed : IsClosed {W : ContourC1Space γ |
      ContourC1Space.complexScale a W ∈ LittleContourSpace γ} :=
    (isClosed_littleContourSpace γ).preimage (contourComplexValueMulC1CLM γ a).continuous
  have hsub : (smoothContourSubmodule γ : Set (ContourC1Space γ)) ⊆
      {W : ContourC1Space γ | ContourC1Space.complexScale a W ∈ LittleContourSpace γ} := by
    intro W hW
    apply (smoothContourSubmodule γ).le_topologicalClosure
    change ContDiff ℝ ∞ (ContourC1Space.lift γ (ContourC1Space.complexScale a W))
    change ContDiff ℝ ∞ (fun θ => a * ContourC1Space.lift γ W θ)
    exact contDiff_const.mul hW
  exact closure_minimal hsub hclosed hZ

namespace LittleContourSpace

def complexScale {γ : ℝ≥0} (a : ℂ) (Z : LittleContourSpace γ) : LittleContourSpace γ :=
  ⟨ContourC1Space.complexScale a Z.val, complexScale_preserves_little a Z.property⟩

@[simp] theorem lift_complexScale {γ : ℝ≥0} (a : ℂ) (Z : LittleContourSpace γ) (θ : ℝ) :
    lift γ (complexScale a Z) θ = a * lift γ Z θ := rfl

theorem norm_complexScale_eq {γ : ℝ≥0} (a : ℂ) (Z : LittleContourSpace γ) :
    ‖complexScale a Z‖ = ‖a‖ * ‖Z‖ := ContourC1Space.norm_complexScale_eq a Z.val

def complexScalarNormedSpace (γ : ℝ≥0) : NormedSpace ℂ (LittleContourSpace γ) where
  smul := complexScale
  one_smul Z := by apply Subtype.ext; change (1 : ℂ) • Z.val = Z.val; exact one_smul _ _
  mul_smul a b Z := by apply Subtype.ext; change (a * b) • Z.val = a • (b • Z.val); exact mul_smul _ _ _
  smul_add a Z W := by apply Subtype.ext; change a • (Z.val + W.val) = a • Z.val + a • W.val; exact smul_add _ _ _
  smul_zero a := by apply Subtype.ext; change a • (0 : ContourC1Space γ) = 0; exact smul_zero _
  add_smul a b Z := by apply Subtype.ext; change (a + b) • Z.val = a • Z.val + b • Z.val; exact add_smul _ _ _
  zero_smul Z := by apply Subtype.ext; change (0 : ℂ) • Z.val = 0; exact zero_smul _ _
  norm_smul_le a Z := (norm_complexScale_eq a Z).le

attribute [local instance] complexScalarNormedSpace

def complexScalarTower (γ : ℝ≥0) : IsScalarTower ℝ ℂ (LittleContourSpace γ) where
  smul_assoc c a Z := by
    apply Subtype.ext
    change (c • a) • Z.val = c • (a • Z.val)
    exact smul_assoc _ _ _

def complexValueMulCLM (γ : ℝ≥0) (a : ℂ) : LittleContourSpace γ →L[ℝ] LittleContourSpace γ :=
  ((contourComplexValueMulC1CLM γ a).comp (inclusion γ)).codRestrict
    (LittleContourSpace γ) (fun Z => complexScale_preserves_little a Z.property)

@[simp] theorem complexValueMulCLM_apply {γ : ℝ≥0} (a : ℂ) (Z : LittleContourSpace γ) :
    complexValueMulCLM γ a Z = complexScale a Z := rfl

end LittleContourSpace

end Euler2D

end
