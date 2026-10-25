module

public import RequestProject.Euler.FiniteContourQuarterFlow
public import RequestProject.Euler.ContourMaterialArea

/-! Actual local solutions of the finite material contour equation
preserve the original area functional of every interface. -/

@[expose] public section

noncomputable section

open Set Filter Topology
open scoped NNReal

namespace Euler2D

local instance (priority := 2000) finiteAreaLittle_normedAddCommGroup (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) :=
  Submodule.normedAddCommGroup (LittleContourSpace γ)

local instance (priority := 2000) finiteAreaLittle_normedSpace (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

local instance (priority := 2000) finiteAreaC1_normedAddCommGroup (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) :=
  Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)

local instance (priority := 2000) finiteAreaC1_normedSpace (γ : ℝ≥0) :
    NormedSpace ℝ (ContourC1Space γ) :=
  Submodule.normedSpace (contourC1GraphSubmodule γ)

theorem contourArea_eq_initial_of_finiteContour_solution {γ : ℝ≥0} {ι : Type*} [Fintype ι]
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1)
    (Z₀ : ι → ContourC1Space γ) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (r i)) (g : ι → ℝ)
    (α : ℝ → ι → LittleContourSpace γ) {a b : ℝ}
    (hq : ∀ t ∈ Icc a b, ∀ i, ‖(α t i).val - Z₀ i‖ ≤ r i / 4)
    (hd : ∀ t ∈ Icc a b, ∃ ht : IsAdmissibleLittleContourFamily Z₀ r (α t),
      HasDerivAt α (finiteContourMaterialField hγ hγ1 Z₀ r hr href g ⟨α t, ht⟩) t)
    {t : ℝ} (ht : t ∈ Icc a b) (i : ι) :
    contourArea γ (α t i).val = contourArea γ (α a i).val := by
  let U := {W : ι → LittleContourSpace γ | IsAdmissibleLittleContourFamily Z₀ r W}
  let G := openSubtypeFieldExtension U (finiteContourMaterialField hγ hγ1 Z₀ r hr href g)
  let V : ℝ → ι → ContourC1Space γ := fun s j => (G (α s) j).val
  have hZ (s : ℝ) (hs : s ∈ Icc a b) (j : ι) :
      HasDerivAt (fun q => (α q j).val) (V s j) s := by
    obtain ⟨hmem, hds⟩ := hd s hs
    have he := ((LittleContourSpace.inclusion γ).comp
      (ContinuousLinearMap.proj j)).hasFDerivAt.comp_hasDerivAt s hds
    have hG : G (α s) = finiteContourMaterialField hγ hγ1 Z₀ r hr href g ⟨α s, hmem⟩ :=
      openSubtypeFieldExtension_of_mem _ ⟨α s, hmem⟩
    simpa only [V, hG, Function.comp_def, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply, LittleContourSpace.inclusion_apply] using he
  have hV (s : ℝ) (hs : s ∈ Icc a b) (j : ι) (θ : ℝ) :
      ContourC1Space.lift γ (V s j) θ =
        contourC1BoundaryField g (fun k => (α s k).val) j θ := by
    obtain ⟨hmem, _⟩ := hd s hs
    have hG : G (α s) = finiteContourMaterialField hγ hγ1 Z₀ r hr href g ⟨α s, hmem⟩ :=
      openSubtypeFieldExtension_of_mem _ ⟨α s, hmem⟩
    change LittleContourSpace.lift γ (G (α s) j) θ = _
    rw [hG, lift_finiteContourMaterialField]
    rfl
  exact contourArea_eq_initial_of_material_boundary_field g (fun s j => (α s j).val)
    Z₀ r hr href V hq hZ hV ht i

theorem exists_finiteContour_local_area_preserving_solution {γ : ℝ≥0} {ι : Type*} [Fintype ι]
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1)
    (Z₀ : ι → ContourC1Space γ) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (r i)) (g : ι → ℝ)
    (Z : AdmissibleLittleContourFamily Z₀ r) (hq : ∀ i, ‖(Z.val i).val - Z₀ i‖ < r i / 4) :
    ∃ T > 0, ∃ α : ℝ → ι → LittleContourSpace γ, α 0 = Z.val ∧
      (∀ t ∈ Icc 0 T, (∀ i, ‖(α t i).val - Z₀ i‖ < r i / 4) ∧
        ∃ ht : IsAdmissibleLittleContourFamily Z₀ r (α t),
          HasDerivAt α (finiteContourMaterialField hγ hγ1 Z₀ r hr href g ⟨α t, ht⟩) t) ∧
      ∀ t ∈ Icc 0 T, ∀ i, contourArea γ (α t i).val = contourArea γ (Z.val i).val := by
  obtain ⟨T, hT, α, hα0, hd⟩ :=
    exists_finiteContour_quarter_local_material_solution hγ hγ1 Z₀ r hr href g Z hq
  have hsub : Icc 0 (T / 2) ⊆ Ioo (-T) T := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  refine ⟨T / 2, half_pos hT, α, hα0, fun t ht => hd t (hsub ht), ?_⟩
  intro t ht i
  rw [← hα0]
  exact contourArea_eq_initial_of_finiteContour_solution hγ hγ1 Z₀ r hr href g α
    (fun s hs j => (hd s (hsub hs)).1 j |>.le)
    (fun s hs => (hd s (hsub hs)).2) ht i

end Euler2D

end
