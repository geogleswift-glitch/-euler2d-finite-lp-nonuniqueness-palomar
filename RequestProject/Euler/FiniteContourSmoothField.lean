module

public import RequestProject.Euler.FiniteContourField
public import RequestProject.Euler.ContourSelfLogSmooth
public import RequestProject.Euler.ContourCrossLogSmoothness

/-! All finite orders of genuine Banach smoothness for the original
finite-interface field on the actual open separated contour domain. -/

@[expose] public section

noncomputable section

open Set
open scoped NNReal BigOperators ContDiff

namespace Euler2D

local instance (priority := 2000) finiteSmoothLittle_normedAddCommGroup (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) :=
  Submodule.normedAddCommGroup (LittleContourSpace γ)

local instance (priority := 2000) finiteSmoothLittle_normedSpace (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

local instance (priority := 2000) finiteSmoothC1_normedAddCommGroup (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) :=
  Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)

local instance (priority := 2000) finiteSmoothC1_normedSpace (γ : ℝ≥0) :
    NormedSpace ℝ (ContourC1Space γ) :=
  Submodule.normedSpace (contourC1GraphSubmodule γ)

def finiteContourInteractionTotal {γ : ℝ≥0} {ι : Type*}
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1)
    (Z₀ : ι → ContourC1Space γ) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (r i))
    (i j : ι) (Z : ι → LittleContourSpace γ) : LittleContourSpace γ := by
  classical
  exact if i = j then nearCircleSelfLogLittleTotal hγ hγ1 (Z₀ i) (hr i) (href i) (Z i)
    else contourCrossLogLittleShape hγ1.le (Z i, Z j)

theorem finiteContourInteractionTotal_of_mem {γ : ℝ≥0} {ι : Type*}
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1)
    (Z₀ : ι → ContourC1Space γ) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (r i))
    (i j : ι) (Z : AdmissibleLittleContourFamily Z₀ r) :
    finiteContourInteractionTotal hγ hγ1 Z₀ r hr href i j Z.val =
      finiteContourInteraction hγ hγ1 Z₀ r hr href i j Z := by
  classical
  by_cases hij : i = j
  · simp only [finiteContourInteractionTotal, if_pos hij, finiteContourInteraction, dif_pos hij]
    exact nearCircleSelfLogLittleTotal_of_mem hγ hγ1 (Z₀ i) (hr i) (href i)
      (Z.val i) (Z.property.1 i)
  · simp only [finiteContourInteractionTotal, if_neg hij, finiteContourInteraction, dif_neg hij]
    exact contourCrossLogLittleShape_eq hγ1.le (finiteFamilySeparatedPair Z₀ r i j hij Z)

theorem contDiffOn_finiteContourInteractionTotal {γ : ℝ≥0} {ι : Type} [Fintype ι]
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1)
    (Z₀ : ι → ContourC1Space γ) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (r i)) (i j : ι) (n : ℕ∞) :
    ContDiffOn ℝ n (finiteContourInteractionTotal hγ hγ1 Z₀ r hr href i j)
      {Z : ι → LittleContourSpace γ | IsAdmissibleLittleContourFamily Z₀ r Z} := by
  classical
  by_cases hij : i = j
  · have he : finiteContourInteractionTotal hγ hγ1 Z₀ r hr href i j =
        fun Z => nearCircleSelfLogLittleTotal hγ hγ1 (Z₀ i) (hr i) (href i) (Z i) :=
      funext (fun _ => by simp only [finiteContourInteractionTotal, if_pos hij])
    rw [he]
    exact (contDiffOn_nearCircleSelfLogLittleTotal hγ hγ1 (Z₀ i) (hr i) (href i) n).comp
      (ContinuousLinearMap.proj i : (ι → LittleContourSpace γ) →L[ℝ] LittleContourSpace γ).contDiff.contDiffOn
        (fun Z hZ => hZ.1 i)
  · have he : finiteContourInteractionTotal hγ hγ1 Z₀ r hr href i j =
        fun Z => contourCrossLogLittleShape hγ1.le (Z i, Z j) :=
      funext (fun _ => by simp only [finiteContourInteractionTotal, if_neg hij])
    rw [he]
    have hp : ContDiff ℝ n (fun Z : ι → LittleContourSpace γ => (Z i, Z j)) :=
      (ContinuousLinearMap.proj i : (ι → LittleContourSpace γ) →L[ℝ] LittleContourSpace γ).contDiff.prodMk
        (ContinuousLinearMap.proj j : (ι → LittleContourSpace γ) →L[ℝ] LittleContourSpace γ).contDiff
    exact ((contDiffOn_contourCrossLogLittleShape hγ hγ1.le).of_le
      (WithTop.coe_le_coe.mpr le_top)).comp hp.contDiffOn (fun Z hZ => hZ.2 i j hij)

def finiteContourMaterialFieldTotal {γ : ℝ≥0} {ι : Type*} [Fintype ι]
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1)
    (Z₀ : ι → ContourC1Space γ) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (r i)) (g : ι → ℝ)
    (Z : ι → LittleContourSpace γ) (i : ι) : LittleContourSpace γ :=
  (-1 / (2 * Real.pi) : ℝ) • ∑ j, g j • finiteContourInteractionTotal hγ hγ1 Z₀ r hr href i j Z

theorem finiteContourMaterialFieldTotal_of_mem {γ : ℝ≥0} {ι : Type*} [Fintype ι]
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1)
    (Z₀ : ι → ContourC1Space γ) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (r i)) (g : ι → ℝ)
    (Z : AdmissibleLittleContourFamily Z₀ r) :
    finiteContourMaterialFieldTotal hγ hγ1 Z₀ r hr href g Z.val =
      finiteContourMaterialField hγ hγ1 Z₀ r hr href g Z := by
  funext i
  unfold finiteContourMaterialFieldTotal finiteContourMaterialField
  simp_rw [finiteContourInteractionTotal_of_mem]

theorem contDiffOn_finiteContourMaterialFieldTotal {γ : ℝ≥0} {ι : Type} [Fintype ι]
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1)
    (Z₀ : ι → ContourC1Space γ) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (r i)) (g : ι → ℝ) (n : ℕ∞) :
    ContDiffOn ℝ n (finiteContourMaterialFieldTotal hγ hγ1 Z₀ r hr href g)
      {Z : ι → LittleContourSpace γ | IsAdmissibleLittleContourFamily Z₀ r Z} := by
  apply contDiffOn_pi.mpr
  intro i
  exact ((contDiffOn_const (c := (-1 / (2 * Real.pi) : ℝ))).smul
    (ContDiffOn.sum (fun j _ => (contDiffOn_const (c := g j)).smul
      (contDiffOn_finiteContourInteractionTotal hγ hγ1 Z₀ r hr href i j n))))

theorem contDiffAt_finiteContourMaterialFieldTotal {γ : ℝ≥0} {ι : Type} [Fintype ι]
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1)
    (Z₀ : ι → ContourC1Space γ) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (r i)) (g : ι → ℝ)
    (Z : AdmissibleLittleContourFamily Z₀ r) (n : ℕ∞) :
    ContDiffAt ℝ n (finiteContourMaterialFieldTotal hγ hγ1 Z₀ r hr href g) Z.val :=
  (contDiffOn_finiteContourMaterialFieldTotal hγ hγ1 Z₀ r hr href g n Z.val Z.property).contDiffAt
    ((isOpen_admissibleLittleContourFamilies Z₀ r).mem_nhds Z.property)

end Euler2D

end
