module

public import RequestProject.Euler.ContourRotationLittle

/-! Independent changes of parameter origin act by actual linear
isometries on the unchanged C¹ Hölder and little contour spaces. -/

@[expose] public section

noncomputable section

open Set Filter Topology
open scoped NNReal ContDiff BoundedContinuousFunction

namespace Euler2D

local instance (priority := 2000) parameterShiftC1_group (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) := Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)
local instance (priority := 2000) parameterShiftC1_space (γ : ℝ≥0) :
    NormedSpace ℝ (ContourC1Space γ) := Submodule.normedSpace (contourC1GraphSubmodule γ)
local instance (priority := 2000) parameterShiftLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) parameterShiftLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

variable {γ : ℝ≥0}

def contourParameterShiftBCF (b : ℝ) (f : ContourCircle →ᵇ ℂ) : ContourCircle →ᵇ ℂ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun x => f (x + (b : ContourCircle)),
      f.continuous.comp (continuous_id.add continuous_const)⟩

theorem norm_contourParameterShiftBCF_le (b : ℝ) (f : ContourCircle →ᵇ ℂ) :
    ‖contourParameterShiftBCF b f‖ ≤ ‖f‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr
  intro x
  exact f.norm_coe_le_norm _

def contourParameterShiftC1 (b : ℝ) (Z : ContourC1Space γ) : ContourC1Space γ :=
  ContourC1Space.ofHasDerivAt (contourParameterShiftBCF b (ContourC1Space.toBCF γ Z))
    (contourHolderShift (ContourC1Space.derivative γ Z) b) (by
      intro θ
      have hd := (ContourC1Space.hasDerivAt_lift Z (θ + b)).scomp θ
        ((hasDerivAt_id θ).add_const b)
      simpa only [one_smul, ContourC1Space.lift, contourParameterShiftBCF,
        BoundedContinuousFunction.mkOfCompact_apply, contourHolderShift_apply,
        AddCircle.coe_add] using hd)

@[simp] theorem lift_contourParameterShiftC1 (b : ℝ) (Z : ContourC1Space γ) (θ : ℝ) :
    ContourC1Space.lift γ (contourParameterShiftC1 b Z) θ =
      ContourC1Space.lift γ Z (θ + b) := by
  change ContourC1Space.toBCF γ Z ((θ : ContourCircle) + (b : ContourCircle)) = _
  rw [← AddCircle.coe_add]
  rfl

theorem norm_contourParameterShiftC1_le (b : ℝ) (Z : ContourC1Space γ) :
    ‖contourParameterShiftC1 b Z‖ ≤ ‖Z‖ :=
  max_le_max (norm_contourParameterShiftBCF_le _ _) (norm_contourHolderShift_le _ _)

def contourParameterShiftC1CLM (γ : ℝ≥0) (b : ℝ) : ContourC1Space γ →L[ℝ] ContourC1Space γ :=
  LinearMap.mkContinuous
    { toFun := contourParameterShiftC1 b
      map_add' := by
        intro Z W
        apply ContourC1Space.ext
        intro x
        rfl
      map_smul' := by
        intro a Z
        apply ContourC1Space.ext
        intro x
        rfl }
    1 (fun Z => by simpa only [one_mul] using norm_contourParameterShiftC1_le b Z)

@[simp] theorem contourParameterShiftC1_zero (Z : ContourC1Space γ) :
    contourParameterShiftC1 0 Z = Z := by
  apply ContourC1Space.ext
  intro x
  change ContourC1Space.toBCF γ Z (x + ((0 : ℝ) : ContourCircle)) = _
  simp only [AddCircle.coe_zero, add_zero]

theorem contourParameterShiftC1_add (b c : ℝ) (Z : ContourC1Space γ) :
    contourParameterShiftC1 b (contourParameterShiftC1 c Z) =
      contourParameterShiftC1 (b + c) Z := by
  apply ContourC1Space.ext
  intro x
  change ContourC1Space.toBCF γ Z ((x + (b : ContourCircle)) + (c : ContourCircle)) =
    ContourC1Space.toBCF γ Z (x + ((b + c : ℝ) : ContourCircle))
  rw [AddCircle.coe_add, add_assoc]

theorem norm_contourParameterShiftC1 (b : ℝ) (Z : ContourC1Space γ) :
    ‖contourParameterShiftC1 b Z‖ = ‖Z‖ := by
  apply le_antisymm (norm_contourParameterShiftC1_le b Z)
  have h := norm_contourParameterShiftC1_le (-b) (contourParameterShiftC1 b Z)
  simpa only [contourParameterShiftC1_add, neg_add_cancel, contourParameterShiftC1_zero] using h

theorem contourParameterShiftC1_preserves_smooth (b : ℝ) {Z : ContourC1Space γ}
    (hZ : Z ∈ smoothContourSubmodule γ) :
    contourParameterShiftC1 b Z ∈ smoothContourSubmodule γ := by
  change ContDiff ℝ ∞ (ContourC1Space.lift γ Z) at hZ
  change ContDiff ℝ ∞ (ContourC1Space.lift γ (contourParameterShiftC1 b Z))
  have he : ContourC1Space.lift γ (contourParameterShiftC1 b Z) =
      fun θ => ContourC1Space.lift γ Z (θ + b) := funext (lift_contourParameterShiftC1 b Z)
  rw [he]
  exact hZ.comp (contDiff_id.add contDiff_const)

theorem contourParameterShiftC1_preserves_little (b : ℝ) {Z : ContourC1Space γ}
    (hZ : Z ∈ LittleContourSpace γ) : contourParameterShiftC1 b Z ∈ LittleContourSpace γ := by
  have hclosed : IsClosed {W : ContourC1Space γ | contourParameterShiftC1 b W ∈ LittleContourSpace γ} :=
    (isClosed_littleContourSpace γ).preimage (contourParameterShiftC1CLM γ b).continuous
  have hsub : (smoothContourSubmodule γ : Set (ContourC1Space γ)) ⊆
      {W : ContourC1Space γ | contourParameterShiftC1 b W ∈ LittleContourSpace γ} := by
    intro W hW
    exact (smoothContourSubmodule γ).le_topologicalClosure
      (contourParameterShiftC1_preserves_smooth b hW)
  exact closure_minimal hsub hclosed hZ

def contourParameterShiftLittleCLM (γ : ℝ≥0) (b : ℝ) :
    LittleContourSpace γ →L[ℝ] LittleContourSpace γ :=
  ((contourParameterShiftC1CLM γ b).comp (LittleContourSpace.inclusion γ)).codRestrict
    (LittleContourSpace γ) (fun Z => contourParameterShiftC1_preserves_little b Z.property)

@[simp] theorem lift_contourParameterShiftLittleCLM (b : ℝ) (Z : LittleContourSpace γ) (θ : ℝ) :
    LittleContourSpace.lift γ (contourParameterShiftLittleCLM γ b Z) θ =
      LittleContourSpace.lift γ Z (θ + b) := lift_contourParameterShiftC1 b Z.val θ

theorem norm_contourParameterShiftLittleCLM (b : ℝ) (Z : LittleContourSpace γ) :
    ‖contourParameterShiftLittleCLM γ b Z‖ = ‖Z‖ := norm_contourParameterShiftC1 b Z.val

@[simp] theorem contourParameterShiftLittleCLM_zero (Z : LittleContourSpace γ) :
    contourParameterShiftLittleCLM γ 0 Z = Z := by
  apply Subtype.ext
  exact contourParameterShiftC1_zero Z.val

theorem contourParameterShiftLittleCLM_add (b c : ℝ) (Z : LittleContourSpace γ) :
    contourParameterShiftLittleCLM γ b (contourParameterShiftLittleCLM γ c Z) =
      contourParameterShiftLittleCLM γ (b + c) Z := by
  apply Subtype.ext
  exact contourParameterShiftC1_add b c Z.val

def contourParameterShiftLittleIsometry (γ : ℝ≥0) (b : ℝ) :
    LittleContourSpace γ ≃ₗᵢ[ℝ] LittleContourSpace γ where
  toLinearEquiv :=
    { toLinearMap := (contourParameterShiftLittleCLM γ b).toLinearMap
      invFun := contourParameterShiftLittleCLM γ (-b)
      left_inv := fun Z => by
        change contourParameterShiftLittleCLM γ (-b) (contourParameterShiftLittleCLM γ b Z) = Z
        rw [contourParameterShiftLittleCLM_add, neg_add_cancel, contourParameterShiftLittleCLM_zero]
      right_inv := fun Z => by
        change contourParameterShiftLittleCLM γ b (contourParameterShiftLittleCLM γ (-b) Z) = Z
        rw [contourParameterShiftLittleCLM_add, add_neg_cancel, contourParameterShiftLittleCLM_zero] }
  norm_map' := norm_contourParameterShiftLittleCLM b

def contourParameterShiftFamilyCLM {ι : Type*} [Fintype ι] (γ : ℝ≥0) (b : ι → ℝ) :
    (ι → LittleContourSpace γ) →L[ℝ] (ι → LittleContourSpace γ) :=
  ContinuousLinearMap.pi (fun i => (contourParameterShiftLittleCLM γ (b i)).comp
    (ContinuousLinearMap.proj i))

@[simp] theorem contourParameterShiftFamilyCLM_apply {ι : Type*} [Fintype ι]
    (b : ι → ℝ) (Z : ι → LittleContourSpace γ) (i : ι) :
    contourParameterShiftFamilyCLM γ b Z i = contourParameterShiftLittleCLM γ (b i) (Z i) := rfl

theorem contourParameterShiftFamilyCLM_add {ι : Type*} [Fintype ι]
    (b c : ι → ℝ) (Z : ι → LittleContourSpace γ) :
    contourParameterShiftFamilyCLM γ b (contourParameterShiftFamilyCLM γ c Z) =
      contourParameterShiftFamilyCLM γ (b + c) Z := by
  funext i
  exact contourParameterShiftLittleCLM_add (b i) (c i) (Z i)

@[simp] theorem contourParameterShiftFamilyCLM_zero {ι : Type*} [Fintype ι]
    (Z : ι → LittleContourSpace γ) : contourParameterShiftFamilyCLM γ 0 Z = Z := by
  funext i
  exact contourParameterShiftLittleCLM_zero (Z i)

theorem norm_contourParameterShiftFamilyCLM {ι : Type*} [Fintype ι]
    (b : ι → ℝ) (Z : ι → LittleContourSpace γ) :
    ‖contourParameterShiftFamilyCLM γ b Z‖ = ‖Z‖ := by
  have hle (c : ι → ℝ) (W : ι → LittleContourSpace γ) :
      ‖contourParameterShiftFamilyCLM γ c W‖ ≤ ‖W‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg W)).mpr
    intro i
    rw [contourParameterShiftFamilyCLM_apply, norm_contourParameterShiftLittleCLM]
    exact norm_le_pi_norm W i
  apply le_antisymm (hle b Z)
  have h := hle (-b) (contourParameterShiftFamilyCLM γ b Z)
  simpa only [contourParameterShiftFamilyCLM_add, neg_add_cancel,
    contourParameterShiftFamilyCLM_zero] using h

def contourParameterShiftFamilyIsometry {ι : Type*} [Fintype ι] (γ : ℝ≥0) (b : ι → ℝ) :
    (ι → LittleContourSpace γ) ≃ₗᵢ[ℝ] (ι → LittleContourSpace γ) where
  toLinearEquiv :=
    { toLinearMap := (contourParameterShiftFamilyCLM γ b).toLinearMap
      invFun := contourParameterShiftFamilyCLM γ (-b)
      left_inv := fun Z => by
        change contourParameterShiftFamilyCLM γ (-b) (contourParameterShiftFamilyCLM γ b Z) = Z
        rw [contourParameterShiftFamilyCLM_add, neg_add_cancel, contourParameterShiftFamilyCLM_zero]
      right_inv := fun Z => by
        change contourParameterShiftFamilyCLM γ b (contourParameterShiftFamilyCLM γ (-b) Z) = Z
        rw [contourParameterShiftFamilyCLM_add, add_neg_cancel, contourParameterShiftFamilyCLM_zero] }
  norm_map' := norm_contourParameterShiftFamilyCLM b

end Euler2D

end
