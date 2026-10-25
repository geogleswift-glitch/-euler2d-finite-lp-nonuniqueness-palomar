module

public import RequestProject.Euler.ContourRotationC1
public import RequestProject.Euler.LittleContourSpace

/-! The actual rotation preserves the genuine little closure. The
fourfold constraint is a closed linear subspace of that Banach space. -/

@[expose] public section

noncomputable section

open Set Filter Topology
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) littleRotationC1_group (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) := Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)
local instance (priority := 2000) littleRotationC1_space (γ : ℝ≥0) :
    NormedSpace ℝ (ContourC1Space γ) := Submodule.normedSpace (contourC1GraphSubmodule γ)
local instance (priority := 2000) littleRotation_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) littleRotation_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

theorem contourRotationC1_preserves_smooth {γ : ℝ≥0} (b : ℝ) {Z : ContourC1Space γ}
    (hZ : Z ∈ smoothContourSubmodule γ) : contourRotationC1 b Z ∈ smoothContourSubmodule γ := by
  change ContDiff ℝ ∞ (ContourC1Space.lift γ Z) at hZ
  change ContDiff ℝ ∞ (ContourC1Space.lift γ (contourRotationC1 b Z))
  rw [contourRotationC1_lift]
  unfold rotShift
  have ha : ContDiff ℝ ∞ (fun t : ℝ => t - b) := contDiff_id.sub contDiff_const
  exact contDiff_const.mul (hZ.comp ha)

theorem contourRotationC1_preserves_little {γ : ℝ≥0} (b : ℝ) {Z : ContourC1Space γ}
    (hZ : Z ∈ LittleContourSpace γ) : contourRotationC1 b Z ∈ LittleContourSpace γ := by
  have hclosed : IsClosed {W : ContourC1Space γ | contourRotationC1 b W ∈ LittleContourSpace γ} :=
    (isClosed_littleContourSpace γ).preimage (contourRotationC1CLM γ b).continuous
  have hsub : (smoothContourSubmodule γ : Set (ContourC1Space γ)) ⊆
      {W : ContourC1Space γ | contourRotationC1 b W ∈ LittleContourSpace γ} := by
    intro W hW
    exact (smoothContourSubmodule γ).le_topologicalClosure (contourRotationC1_preserves_smooth b hW)
  exact closure_minimal hsub hclosed hZ

def contourRotationLittleCLM (γ : ℝ≥0) (b : ℝ) : LittleContourSpace γ →L[ℝ] LittleContourSpace γ :=
  ((contourRotationC1CLM γ b).comp (LittleContourSpace.inclusion γ)).codRestrict
    (LittleContourSpace γ) (fun Z => contourRotationC1_preserves_little b Z.property)

theorem lift_contourRotationLittleCLM {γ : ℝ≥0} (b : ℝ) (Z : LittleContourSpace γ) :
    LittleContourSpace.lift γ (contourRotationLittleCLM γ b Z) =
      rotShift b (LittleContourSpace.lift γ Z) := contourRotationC1_lift b Z.val

theorem norm_contourRotationLittleCLM {γ : ℝ≥0} (b : ℝ) (Z : LittleContourSpace γ) :
    ‖contourRotationLittleCLM γ b Z‖ = ‖Z‖ := norm_contourRotationC1 b Z.val

theorem contourRotationLittleCLM_add {γ : ℝ≥0} (b c : ℝ) (Z : LittleContourSpace γ) :
    contourRotationLittleCLM γ b (contourRotationLittleCLM γ c Z) =
      contourRotationLittleCLM γ (b + c) Z := by
  apply Subtype.ext
  exact contourRotationC1_add b c Z.val

theorem contourRotationLittleCLM_zero {γ : ℝ≥0} (Z : LittleContourSpace γ) :
    contourRotationLittleCLM γ 0 Z = Z := by
  apply Subtype.ext
  exact contourRotationC1_zero Z.val

def contourRotationLittleIsometry (γ : ℝ≥0) (b : ℝ) :
    LittleContourSpace γ ≃ₗᵢ[ℝ] LittleContourSpace γ where
  toLinearEquiv :=
    { toLinearMap := (contourRotationLittleCLM γ b).toLinearMap
      invFun := contourRotationLittleCLM γ (-b)
      left_inv := fun Z => by
        change contourRotationLittleCLM γ (-b) (contourRotationLittleCLM γ b Z) = Z
        rw [contourRotationLittleCLM_add, neg_add_cancel, contourRotationLittleCLM_zero]
      right_inv := fun Z => by
        change contourRotationLittleCLM γ b (contourRotationLittleCLM γ (-b) Z) = Z
        rw [contourRotationLittleCLM_add, add_neg_cancel, contourRotationLittleCLM_zero] }
  norm_map' := norm_contourRotationLittleCLM b

def fourfoldLittleContourSubmodule (γ : ℝ≥0) : Submodule ℝ (LittleContourSpace γ) :=
  (contourRotationLittleCLM γ (Real.pi / 2) - ContinuousLinearMap.id ℝ (LittleContourSpace γ)).ker

theorem isClosed_fourfoldLittleContourSubmodule (γ : ℝ≥0) :
    IsClosed (fourfoldLittleContourSubmodule γ : Set (LittleContourSpace γ)) :=
  (contourRotationLittleCLM γ (Real.pi / 2) - ContinuousLinearMap.id ℝ (LittleContourSpace γ)).isClosed_ker

theorem mem_fourfoldLittleContourSubmodule {γ : ℝ≥0} (Z : LittleContourSpace γ) :
    Z ∈ fourfoldLittleContourSubmodule γ ↔
      ∀ θ, LittleContourSpace.lift γ Z (θ + Real.pi / 2) = Complex.I * LittleContourSpace.lift γ Z θ := by
  change (contourRotationLittleCLM γ (Real.pi / 2) Z - Z = 0) ↔ _
  rw [sub_eq_zero]
  have he : Complex.exp (((Real.pi / 2 : ℝ) : ℂ) * Complex.I) = Complex.I := by
    push_cast
    exact Complex.exp_pi_div_two_mul_I
  constructor
  · intro h θ
    have hv := congrArg (fun W : LittleContourSpace γ => LittleContourSpace.lift γ W (θ + Real.pi / 2)) h
    rw [lift_contourRotationLittleCLM] at hv
    simp only [rotShift, add_sub_cancel_right, he] at hv
    exact hv.symm
  · intro h
    apply Subtype.ext
    apply ContourC1Space.ext
    intro x
    obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective x
    change LittleContourSpace.lift γ (contourRotationLittleCLM γ (Real.pi / 2) Z) θ =
      LittleContourSpace.lift γ Z θ
    rw [lift_contourRotationLittleCLM]
    change Complex.exp (((Real.pi / 2 : ℝ) : ℂ) * Complex.I) *
      LittleContourSpace.lift γ Z (θ - Real.pi / 2) = LittleContourSpace.lift γ Z θ
    rw [he]
    simpa only [sub_add_cancel] using (h (θ - Real.pi / 2)).symm

end Euler2D

end
