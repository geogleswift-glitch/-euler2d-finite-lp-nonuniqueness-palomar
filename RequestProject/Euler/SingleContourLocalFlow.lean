module

public import RequestProject.Euler.ContourLittleSelfLogLipschitz
public import RequestProject.Euler.LocalBanachContourODE

/-! A genuine local material solution for the original self-interaction
of one interface in the actual little Hölder Banach space. -/

@[expose] public section

noncomputable section

open Set Filter Topology
open scoped NNReal

namespace Euler2D

local instance (priority := 2000) singleFlowLittle_normedAddCommGroup (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) :=
  Submodule.normedAddCommGroup (LittleContourSpace γ)

local instance (priority := 2000) singleFlowLittle_normedSpace (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) :=
  Submodule.normedSpace (LittleContourSpace γ)

local instance (priority := 2000) singleFlowC1_normedAddCommGroup (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) :=
  Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)

def singleContourMaterialField {γ : ℝ≥0}
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1) (Z₀ : ContourC1Space γ)
    {r : ℝ} (hr : 0 < r) (href : ContourC1Space.lift γ Z₀ = refCircle r)
    (g : ℝ) (Z : NearCircleLittleContour Z₀ r) : LittleContourSpace γ :=
  (-g / (2 * Real.pi) : ℝ) • nearCircleSelfLogLittle hγ hγ1 Z₀ hr href Z

theorem locallyLipschitz_singleContourMaterialField {γ : ℝ≥0}
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1) (Z₀ : ContourC1Space γ)
    {r : ℝ} (hr : 0 < r) (href : ContourC1Space.lift γ Z₀ = refCircle r) (g : ℝ) :
    LocallyLipschitz (singleContourMaterialField hγ hγ1 Z₀ hr href g) := by
  have hs : LocallyLipschitz (fun W : LittleContourSpace γ => (-g / (2 * Real.pi) : ℝ) • W) :=
    (lipschitzWith_smul (-g / (2 * Real.pi) : ℝ)).locallyLipschitz
  exact hs.comp (locallyLipschitz_nearCircleSelfLogLittle hγ hγ1 Z₀ hr href)

@[simp] theorem lift_singleContourMaterialField {γ : ℝ≥0}
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1) (Z₀ : ContourC1Space γ)
    {r : ℝ} (hr : 0 < r) (href : ContourC1Space.lift γ Z₀ = refCircle r)
    (g : ℝ) (Z : NearCircleLittleContour Z₀ r) :
    LittleContourSpace.lift γ (singleContourMaterialField hγ hγ1 Z₀ hr href g Z) =
      fun θ => (-g / (2 * Real.pi) : ℝ) • ContourC1Space.selfLogIntegral Z.val.val θ := rfl

theorem exists_singleContour_local_material_solution {γ : ℝ≥0}
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1) (Z₀ : ContourC1Space γ)
    {r : ℝ} (hr : 0 < r) (href : ContourC1Space.lift γ Z₀ = refCircle r)
    (g : ℝ) (Z : NearCircleLittleContour Z₀ r) :
    ∃ T > 0, ∃ α : ℝ → LittleContourSpace γ, α 0 = Z.val ∧
      ∀ t ∈ Ioo (-T) T, ∃ ht : ‖(α t).val - Z₀‖ < 2 * r / Real.pi,
        HasDerivAt α (singleContourMaterialField hγ hγ1 Z₀ hr href g ⟨α t, ht⟩) t := by
  have ho : IsOpen {W : LittleContourSpace γ | ‖W.val - Z₀‖ < 2 * r / Real.pi} :=
    isOpen_lt (((LittleContourSpace.inclusion γ).continuous.sub continuous_const).norm) continuous_const
  exact exists_local_curve_on_open_subtype ho
    (singleContourMaterialField hγ hγ1 Z₀ hr href g)
    (locallyLipschitz_singleContourMaterialField hγ hγ1 Z₀ hr href g) Z

/-- The actual temporal derivative of every point is the original log
integral, obtained by applying the actual evaluation CLM to the Banach ODE. -/
theorem exists_singleContour_local_pointwise_solution {γ : ℝ≥0}
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1) (Z₀ : ContourC1Space γ)
    {r : ℝ} (hr : 0 < r) (href : ContourC1Space.lift γ Z₀ = refCircle r)
    (g : ℝ) (Z : NearCircleLittleContour Z₀ r) :
    ∃ T > 0, ∃ α : ℝ → LittleContourSpace γ, α 0 = Z.val ∧
      ∀ t ∈ Ioo (-T) T, ‖(α t).val - Z₀‖ < 2 * r / Real.pi ∧
        ∀ θ : ℝ, HasDerivAt (fun s => LittleContourSpace.lift γ (α s) θ)
          ((-g / (2 * Real.pi) : ℝ) • ContourC1Space.selfLogIntegral (α t).val θ) t := by
  obtain ⟨T, hT, α, hα0, hd⟩ :=
    exists_singleContour_local_material_solution hγ hγ1 Z₀ hr href g Z
  refine ⟨T, hT, α, hα0, ?_⟩
  intro t ht
  obtain ⟨htZ, hdt⟩ := hd t ht
  refine ⟨htZ, fun θ => ?_⟩
  exact (LittleContourSpace.eval γ (θ : ContourCircle)).hasFDerivAt.comp_hasDerivAt t hdt

end Euler2D

end
