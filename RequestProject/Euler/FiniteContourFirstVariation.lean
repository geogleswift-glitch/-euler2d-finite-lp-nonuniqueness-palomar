module

public import RequestProject.Euler.ContourSelfFirstVariation
public import RequestProject.Euler.ContourCrossFirstVariation
public import RequestProject.Euler.FiniteContourSmoothField

/-! The actual Banach field derivative is the sum of the actual
singular self and separated cross first variations, after applying
the genuine inclusion and evaluation maps. -/

@[expose] public section

noncomputable section

open Set Filter Topology
open scoped NNReal ContDiff BigOperators

namespace Euler2D

local instance (priority := 2000) finiteVariationC1_group (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) := Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)
local instance (priority := 2000) finiteVariationC1_space (γ : ℝ≥0) :
    NormedSpace ℝ (ContourC1Space γ) := Submodule.normedSpace (contourC1GraphSubmodule γ)
local instance (priority := 2000) finiteVariationLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) finiteVariationLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

variable {γ : ℝ≥0} {ι : Type} [Fintype ι]

def contourC1InteractionAt (i j : ι) (θ : ℝ) (Z : ι → ContourC1Space γ) : ℂ := by
  classical
  exact if i = j then ContourC1Space.selfLogIntegral (Z i) θ
    else contourC1CrossLogIntegral (Z i) (Z j) θ

theorem contourC1InteractionAt_eq_boundaryIntegral (i j : ι) (θ : ℝ) (Z : ι → ContourC1Space γ) :
    contourC1InteractionAt i j θ Z =
      contourLogBoundaryIntegral (ContourC1Space.lift γ (Z j))
        (deriv (ContourC1Space.lift γ (Z j))) (ContourC1Space.lift γ (Z i) θ) := by
  classical
  by_cases hij : i = j
  · subst j
    rw [contourC1InteractionAt, if_pos rfl]
    exact ContourC1Space.selfLogIntegral_eq_boundaryIntegral (Z i) θ
  · rw [contourC1InteractionAt, if_neg hij]
    exact contourC1CrossLogIntegral_eq_boundaryIntegral (Z i) (Z j) θ

def contourC1InteractionDerivative (i j : ι) (θ : ℝ) (Z : ι → ContourC1Space γ) :
    (ι → ContourC1Space γ) →L[ℝ] ℂ := by
  classical
  exact if i = j then
    (fderiv ℝ (fun W : ContourC1Space γ => ContourC1Space.selfLogIntegral W θ) (Z i)).comp
      (ContinuousLinearMap.proj i)
  else
    (fderiv ℝ (fun p : ContourC1Space γ × ContourC1Space γ => contourC1CrossLogIntegral p.1 p.2 θ)
      (Z i, Z j)).comp ((ContinuousLinearMap.proj i).prod (ContinuousLinearMap.proj j))

theorem hasFDerivAt_contourC1InteractionAt
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) ≤ 1) (i j : ι) (θ : ℝ)
    (Z : ι → ContourC1Space γ) (hchord : ∀ k, ContourC1Space.HasPositiveChordArc (Z k))
    (hsep : ∀ k l, k ≠ l → ∃ σ > 0, ContourCrossSeparated (Z k) (Z l) σ) :
    HasFDerivAt (contourC1InteractionAt (γ := γ) i j θ) (contourC1InteractionDerivative i j θ Z) Z := by
  classical
  by_cases hij : i = j
  · have hd := ((contDiffAt_selfLogIntegral_fixed hγ θ (Z i) (hchord i)).differentiableAt
      (by simp)).hasFDerivAt.comp Z
        (ContinuousLinearMap.proj i : (ι → ContourC1Space γ) →L[ℝ] ContourC1Space γ).hasFDerivAt
    have he : contourC1InteractionAt (γ := γ) i j θ =
        fun W : ι → ContourC1Space γ => ContourC1Space.selfLogIntegral (W i) θ := by
      funext W
      exact if_pos hij
    rw [he, contourC1InteractionDerivative, if_pos hij]
    exact hd
  · have hp : (Z i, Z j) ∈ {p : ContourC1Space γ × ContourC1Space γ |
        ∃ σ > 0, ContourCrossSeparated p.1 p.2 σ} := hsep i j hij
    have hd := (((contDiffOn_contourC1CrossLogIntegral_fixed hγ hγ1 θ (Z i, Z j) hp).contDiffAt
      ((isOpen_positiveSeparatedContourPairs γ).mem_nhds hp)).differentiableAt
        (by simp)).hasFDerivAt.comp Z
          (((ContinuousLinearMap.proj i : (ι → ContourC1Space γ) →L[ℝ] ContourC1Space γ).prod
            (ContinuousLinearMap.proj j)) :
              (ι → ContourC1Space γ) →L[ℝ] ContourC1Space γ × ContourC1Space γ).hasFDerivAt
    have he : contourC1InteractionAt (γ := γ) i j θ =
        fun W : ι → ContourC1Space γ => contourC1CrossLogIntegral (W i) (W j) θ := by
      funext W
      exact if_neg hij
    rw [he, contourC1InteractionDerivative, if_neg hij]
    exact hd

def contourC1BoundaryDerivative (g : ι → ℝ) (Z : ι → ContourC1Space γ) (i : ι) (θ : ℝ) :
    (ι → ContourC1Space γ) →L[ℝ] ℂ :=
  (-1 / (2 * Real.pi) : ℝ) • ∑ j, g j • contourC1InteractionDerivative i j θ Z

theorem hasFDerivAt_contourC1BoundaryField
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) ≤ 1) (g : ι → ℝ)
    (Z : ι → ContourC1Space γ) (hchord : ∀ k, ContourC1Space.HasPositiveChordArc (Z k))
    (hsep : ∀ k l, k ≠ l → ∃ σ > 0, ContourCrossSeparated (Z k) (Z l) σ)
    (i : ι) (θ : ℝ) :
    HasFDerivAt (fun W : ι → ContourC1Space γ => contourC1BoundaryField g W i θ)
      (contourC1BoundaryDerivative g Z i θ) Z := by
  have hd := (HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
    (hasFDerivAt_contourC1InteractionAt hγ hγ1 i j θ Z hchord hsep).const_smul (g j))).const_smul
      (-1 / (2 * Real.pi) : ℝ)
  have he : (fun W : ι → ContourC1Space γ => contourC1BoundaryField g W i θ) =
      (fun W => (-1 / (2 * Real.pi) : ℝ) • ∑ j, g j • contourC1InteractionAt i j θ W) := by
    funext W
    unfold contourC1BoundaryField contourBoundaryField
    simp only [Complex.real_smul, contourC1InteractionAt_eq_boundaryIntegral]
    push_cast
    rfl
  rw [he]
  exact hd

def littleContourFamilyInclusion (γ : ℝ≥0) :
    (ι → LittleContourSpace γ) →L[ℝ] (ι → ContourC1Space γ) :=
  ContinuousLinearMap.pi (fun i => (LittleContourSpace.inclusion γ).comp (ContinuousLinearMap.proj i))

set_option maxHeartbeats 800000 in
theorem lift_fderiv_finiteContourMaterialFieldTotal
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1)
    (Z₀ : ι → ContourC1Space γ) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (r i)) (g : ι → ℝ)
    (Z : AdmissibleLittleContourFamily Z₀ r) (H : ι → LittleContourSpace γ) (i : ι) (θ : ℝ) :
    LittleContourSpace.lift γ
        (fderiv ℝ (finiteContourMaterialFieldTotal hγ hγ1 Z₀ r hr href g) Z.val H i) θ =
      contourC1BoundaryDerivative g (fun j => (Z.val j).val) i θ (fun j => (H j).val) := by
  let L : (ι → LittleContourSpace γ) →L[ℝ] ℂ :=
    (LittleContourSpace.eval γ (θ : ContourCircle)).comp (ContinuousLinearMap.proj i)
  have hF := ((contDiffAt_finiteContourMaterialFieldTotal hγ hγ1 Z₀ r hr href g Z 1).differentiableAt
    (by simp)).hasFDerivAt
  have hleft := L.hasFDerivAt.comp Z.val hF
  have hchord (j : ι) : ContourC1Space.HasPositiveChordArc (Z.val j).val :=
    (nearCirclePositiveContour (Z₀ j) (hr j) (href j) (finiteFamilyNearCircleComponent Z₀ r j Z)).property
  have hright := (hasFDerivAt_contourC1BoundaryField hγ hγ1.le g
    (fun j => (Z.val j).val) hchord Z.property.2 i θ).comp Z.val
      (littleContourFamilyInclusion (ι := ι) γ).hasFDerivAt
  have he : (fun W : ι → LittleContourSpace γ => contourC1BoundaryField g
        (littleContourFamilyInclusion (ι := ι) γ W) i θ) =ᶠ[𝓝 Z.val]
      (fun W => L (finiteContourMaterialFieldTotal hγ hγ1 Z₀ r hr href g W)) := by
    filter_upwards [(isOpen_admissibleLittleContourFamilies Z₀ r).mem_nhds Z.property] with W hW
    change contourBoundaryField g (fun j => LittleContourSpace.lift γ (W j)) i θ =
      LittleContourSpace.lift γ (finiteContourMaterialFieldTotal hγ hγ1 Z₀ r hr href g W i) θ
    rw [finiteContourMaterialFieldTotal_of_mem hγ hγ1 Z₀ r hr href g ⟨W, hW⟩,
      lift_finiteContourMaterialField]
  have hEq := hleft.unique (hright.congr_of_eventuallyEq he.symm)
  exact congrArg (fun A : (ι → LittleContourSpace γ) →L[ℝ] ℂ => A H) hEq

end Euler2D

end
