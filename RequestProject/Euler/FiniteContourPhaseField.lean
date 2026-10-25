module

public import RequestProject.Euler.ContourParameterShift
public import RequestProject.Euler.FiniteContourSmoothField
public import RequestProject.Euler.CircularContourDynamics

/-! The original finite contour field on the union of all parameter
phase charts. Chart overlaps agree as actual Banach-valued maps because
their lifts are the same original boundary integrals. -/

@[expose] public section

noncomputable section

open Set Filter Topology
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) phaseFieldC1_group (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) := Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)
local instance (priority := 2000) phaseFieldC1_space (γ : ℝ≥0) :
    NormedSpace ℝ (ContourC1Space γ) := Submodule.normedSpace (contourC1GraphSubmodule γ)
local instance (priority := 2000) phaseFieldLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) phaseFieldLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

variable {γ : ℝ≥0} {ι : Type} [Fintype ι]

def IsPhaseAdmissibleLittleContourFamily (Z₀ : ι → ContourC1Space γ) (r : ι → ℝ)
    (Z : ι → LittleContourSpace γ) : Prop :=
  ∃ b : ι → ℝ, IsAdmissibleLittleContourFamily Z₀ r (contourParameterShiftFamilyCLM γ (-b) Z)

theorem isOpen_contourPhaseChart (Z₀ : ι → ContourC1Space γ) (r : ι → ℝ) (b : ι → ℝ) :
    IsOpen {Z : ι → LittleContourSpace γ |
      IsAdmissibleLittleContourFamily Z₀ r (contourParameterShiftFamilyCLM γ (-b) Z)} :=
  (isOpen_admissibleLittleContourFamilies Z₀ r).preimage
    (contourParameterShiftFamilyCLM γ (-b)).continuous

theorem isOpen_phaseAdmissibleLittleContourFamilies
    (Z₀ : ι → ContourC1Space γ) (r : ι → ℝ) :
    IsOpen {Z : ι → LittleContourSpace γ | IsPhaseAdmissibleLittleContourFamily Z₀ r Z} := by
  have he : {Z : ι → LittleContourSpace γ | IsPhaseAdmissibleLittleContourFamily Z₀ r Z} =
      ⋃ b : ι → ℝ, {Z | IsAdmissibleLittleContourFamily Z₀ r
        (contourParameterShiftFamilyCLM γ (-b) Z)} := by
    ext Z
    simp only [IsPhaseAdmissibleLittleContourFamily, mem_setOf_eq, mem_iUnion]
  rw [he]
  exact isOpen_iUnion (isOpen_contourPhaseChart Z₀ r)

def finiteContourPhaseFieldChart
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1)
    (Z₀ : ι → ContourC1Space γ) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (r i)) (g : ι → ℝ)
    (b : ι → ℝ) (Z : ι → LittleContourSpace γ) : ι → LittleContourSpace γ :=
  contourParameterShiftFamilyCLM γ b
    (finiteContourMaterialFieldTotal hγ hγ1 Z₀ r hr href g
      (contourParameterShiftFamilyCLM γ (-b) Z))

theorem lift_finiteContourPhaseFieldChart
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1)
    (Z₀ : ι → ContourC1Space γ) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (r i)) (g : ι → ℝ)
    (b : ι → ℝ) (Z : ι → LittleContourSpace γ)
    (hZ : IsAdmissibleLittleContourFamily Z₀ r (contourParameterShiftFamilyCLM γ (-b) Z))
    (i : ι) (θ : ℝ) :
    LittleContourSpace.lift γ (finiteContourPhaseFieldChart hγ hγ1 Z₀ r hr href g b Z i) θ =
      contourBoundaryField g (fun j => LittleContourSpace.lift γ (Z j)) i θ := by
  let W := contourParameterShiftFamilyCLM γ (-b) Z
  have hz (j : ι) : Differentiable ℝ (LittleContourSpace.lift γ (W j)) :=
    fun x => (LittleContourSpace.hasDerivAt_lift (W j) x).differentiableAt
  have hp (j : ι) := LittleContourSpace.periodic_lift (W j)
  have hpd (j : ι) := periodic_deriv_contour (hp j) (hz j)
  have he : (fun j φ => LittleContourSpace.lift γ (W j) (φ + b j)) =
      (fun j => LittleContourSpace.lift γ (Z j)) := by
    funext j φ
    simp only [W, contourParameterShiftFamilyCLM_apply, lift_contourParameterShiftLittleCLM,
      Pi.neg_apply, add_neg_cancel_right]
  change LittleContourSpace.lift γ
    (contourParameterShiftLittleCLM γ (b i)
      (finiteContourMaterialFieldTotal hγ hγ1 Z₀ r hr href g W i)) θ = _
  rw [lift_contourParameterShiftLittleCLM,
    finiteContourMaterialFieldTotal_of_mem hγ hγ1 Z₀ r hr href g ⟨W, hZ⟩,
    lift_finiteContourMaterialField]
  have h := contourBoundaryField_reparametrize g
    (fun j => LittleContourSpace.lift γ (W j)) b hz hp hpd i θ
  rw [he] at h
  exact h.symm

theorem finiteContourPhaseFieldChart_eq_on_overlap
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1)
    (Z₀ : ι → ContourC1Space γ) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (r i)) (g : ι → ℝ)
    (b c : ι → ℝ) (Z : ι → LittleContourSpace γ)
    (hb : IsAdmissibleLittleContourFamily Z₀ r (contourParameterShiftFamilyCLM γ (-b) Z))
    (hc : IsAdmissibleLittleContourFamily Z₀ r (contourParameterShiftFamilyCLM γ (-c) Z)) :
    finiteContourPhaseFieldChart hγ hγ1 Z₀ r hr href g b Z =
      finiteContourPhaseFieldChart hγ hγ1 Z₀ r hr href g c Z := by
  funext i
  apply Subtype.ext
  apply ContourC1Space.ext
  intro x
  obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective x
  change LittleContourSpace.lift γ (finiteContourPhaseFieldChart hγ hγ1 Z₀ r hr href g b Z i) θ =
    LittleContourSpace.lift γ (finiteContourPhaseFieldChart hγ hγ1 Z₀ r hr href g c Z i) θ
  rw [lift_finiteContourPhaseFieldChart hγ hγ1 Z₀ r hr href g b Z hb,
    lift_finiteContourPhaseFieldChart hγ hγ1 Z₀ r hr href g c Z hc]

def finiteContourPhaseFieldTotal
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1)
    (Z₀ : ι → ContourC1Space γ) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (r i)) (g : ι → ℝ)
    (Z : ι → LittleContourSpace γ) : ι → LittleContourSpace γ := by
  classical
  exact if hZ : IsPhaseAdmissibleLittleContourFamily Z₀ r Z then
    finiteContourPhaseFieldChart hγ hγ1 Z₀ r hr href g hZ.choose Z else 0

theorem finiteContourPhaseFieldTotal_eq_chart
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1)
    (Z₀ : ι → ContourC1Space γ) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (r i)) (g : ι → ℝ)
    (b : ι → ℝ) (Z : ι → LittleContourSpace γ)
    (hZ : IsAdmissibleLittleContourFamily Z₀ r (contourParameterShiftFamilyCLM γ (-b) Z)) :
    finiteContourPhaseFieldTotal hγ hγ1 Z₀ r hr href g Z =
      finiteContourPhaseFieldChart hγ hγ1 Z₀ r hr href g b Z := by
  have hp : IsPhaseAdmissibleLittleContourFamily Z₀ r Z := ⟨b, hZ⟩
  rw [finiteContourPhaseFieldTotal, dif_pos hp]
  exact finiteContourPhaseFieldChart_eq_on_overlap hγ hγ1 Z₀ r hr href g
    hp.choose b Z hp.choose_spec hZ

theorem lift_finiteContourPhaseFieldTotal
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1)
    (Z₀ : ι → ContourC1Space γ) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (r i)) (g : ι → ℝ)
    (Z : ι → LittleContourSpace γ) (hZ : IsPhaseAdmissibleLittleContourFamily Z₀ r Z)
    (i : ι) (θ : ℝ) :
    LittleContourSpace.lift γ (finiteContourPhaseFieldTotal hγ hγ1 Z₀ r hr href g Z i) θ =
      contourBoundaryField g (fun j => LittleContourSpace.lift γ (Z j)) i θ := by
  obtain ⟨b, hb⟩ := hZ
  rw [finiteContourPhaseFieldTotal_eq_chart hγ hγ1 Z₀ r hr href g b Z hb]
  exact lift_finiteContourPhaseFieldChart hγ hγ1 Z₀ r hr href g b Z hb i θ

theorem contDiffAt_finiteContourPhaseFieldTotal
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1)
    (Z₀ : ι → ContourC1Space γ) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (r i)) (g : ι → ℝ)
    (Z : ι → LittleContourSpace γ) (hZ : IsPhaseAdmissibleLittleContourFamily Z₀ r Z) (n : ℕ∞) :
    ContDiffAt ℝ n (finiteContourPhaseFieldTotal hγ hγ1 Z₀ r hr href g) Z := by
  obtain ⟨b, hb⟩ := hZ
  have hf := (contDiffAt_finiteContourMaterialFieldTotal hγ hγ1 Z₀ r hr href g
    ⟨contourParameterShiftFamilyCLM γ (-b) Z, hb⟩ n).comp Z
      (contourParameterShiftFamilyCLM γ (-b)).contDiff.contDiffAt
  have hc : ContDiffAt ℝ n (finiteContourPhaseFieldChart hγ hγ1 Z₀ r hr href g b) Z :=
    (contourParameterShiftFamilyCLM γ b).contDiff.contDiffAt.comp Z hf
  apply hc.congr_of_eventuallyEq
  filter_upwards [(isOpen_contourPhaseChart Z₀ r b).mem_nhds hb] with W hW
  exact finiteContourPhaseFieldTotal_eq_chart hγ hγ1 Z₀ r hr href g b W hW

theorem contDiffOn_finiteContourPhaseFieldTotal
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1)
    (Z₀ : ι → ContourC1Space γ) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (r i)) (g : ι → ℝ) (n : ℕ∞) :
    ContDiffOn ℝ n (finiteContourPhaseFieldTotal hγ hγ1 Z₀ r hr href g)
      {Z | IsPhaseAdmissibleLittleContourFamily Z₀ r Z} :=
  fun Z hZ => (contDiffAt_finiteContourPhaseFieldTotal hγ hγ1 Z₀ r hr href g Z hZ n).contDiffWithinAt

end Euler2D

end
