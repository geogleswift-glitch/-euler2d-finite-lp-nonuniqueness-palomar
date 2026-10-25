module

public import RequestProject.Euler.FiniteContourField
public import RequestProject.Euler.LocalBanachContourODE
public import RequestProject.Euler.LocalBanachContourUniqueness

/-! Genuine local material solutions of the original finite-interface
contour equation in the actual little Hölder Banach space. -/

@[expose] public section

noncomputable section

open Set Filter Topology
open scoped NNReal

namespace Euler2D

local instance (priority := 2000) finiteFlowLittle_normedAddCommGroup (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) :=
  Submodule.normedAddCommGroup (LittleContourSpace γ)

local instance (priority := 2000) finiteFlowLittle_normedSpace (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

local instance (priority := 2000) finiteFlowC1_normedAddCommGroup (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) :=
  Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)

theorem exists_finiteContour_local_material_solution {γ : ℝ≥0} {ι : Type*} [Fintype ι]
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1)
    (Z₀ : ι → ContourC1Space γ) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (r i)) (g : ι → ℝ)
    (Z : AdmissibleLittleContourFamily Z₀ r) :
    ∃ T > 0, ∃ α : ℝ → ι → LittleContourSpace γ, α 0 = Z.val ∧
      ∀ t ∈ Ioo (-T) T, ∃ ht : IsAdmissibleLittleContourFamily Z₀ r (α t),
        HasDerivAt α (finiteContourMaterialField hγ hγ1 Z₀ r hr href g ⟨α t, ht⟩) t :=
  exists_local_curve_on_open_subtype (isOpen_admissibleLittleContourFamilies Z₀ r)
    (finiteContourMaterialField hγ hγ1 Z₀ r hr href g)
    (locallyLipschitz_finiteContourMaterialField hγ hγ1 Z₀ r hr href g) Z

/-- Every point of every interface satisfies the literal original
finite boundary-integral vector field. -/
theorem exists_finiteContour_local_pointwise_solution {γ : ℝ≥0} {ι : Type*} [Fintype ι]
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1)
    (Z₀ : ι → ContourC1Space γ) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (r i)) (g : ι → ℝ)
    (Z : AdmissibleLittleContourFamily Z₀ r) :
    ∃ T > 0, ∃ α : ℝ → ι → LittleContourSpace γ, α 0 = Z.val ∧
      ∀ t ∈ Ioo (-T) T, IsAdmissibleLittleContourFamily Z₀ r (α t) ∧
        ∀ (i : ι) (θ : ℝ), HasDerivAt (fun s => LittleContourSpace.lift γ (α s i) θ)
          (contourBoundaryField g (fun j => LittleContourSpace.lift γ (α t j)) i θ) t := by
  obtain ⟨T, hT, α, hα0, hd⟩ := exists_finiteContour_local_material_solution hγ hγ1 Z₀ r hr href g Z
  refine ⟨T, hT, α, hα0, ?_⟩
  intro t ht
  obtain ⟨htZ, hdt⟩ := hd t ht
  refine ⟨htZ, fun i θ => ?_⟩
  have he := ((LittleContourSpace.eval γ (θ : ContourCircle)).comp
    (ContinuousLinearMap.proj i)).hasFDerivAt.comp_hasDerivAt t hdt
  change HasDerivAt (fun s => LittleContourSpace.lift γ (α s i) θ)
    (LittleContourSpace.lift γ
      (finiteContourMaterialField hγ hγ1 Z₀ r hr href g ⟨α t, htZ⟩ i) θ) t at he
  rw [lift_finiteContourMaterialField] at he
  exact he

theorem locally_unique_finiteContour_material_solution {γ : ℝ≥0} {ι : Type*} [Fintype ι]
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1)
    (Z₀ : ι → ContourC1Space γ) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (r i)) (g : ι → ℝ)
    (Z : AdmissibleLittleContourFamily Z₀ r) {α β : ℝ → ι → LittleContourSpace γ} {t₀ : ℝ}
    (hα0 : α t₀ = Z.val) (hβ0 : β t₀ = Z.val)
    (hα : ∀ᶠ t in 𝓝 t₀, ∃ ht : IsAdmissibleLittleContourFamily Z₀ r (α t),
      HasDerivAt α (finiteContourMaterialField hγ hγ1 Z₀ r hr href g ⟨α t, ht⟩) t)
    (hβ : ∀ᶠ t in 𝓝 t₀, ∃ ht : IsAdmissibleLittleContourFamily Z₀ r (β t),
      HasDerivAt β (finiteContourMaterialField hγ hγ1 Z₀ r hr href g ⟨β t, ht⟩) t) :
    α =ᶠ[𝓝 t₀] β :=
  locally_unique_curve_on_open_subtype (isOpen_admissibleLittleContourFamilies Z₀ r)
    (finiteContourMaterialField hγ hγ1 Z₀ r hr href g)
    (locallyLipschitz_finiteContourMaterialField hγ hγ1 Z₀ r hr href g) Z hα0 hβ0 hα hβ

end Euler2D

end
