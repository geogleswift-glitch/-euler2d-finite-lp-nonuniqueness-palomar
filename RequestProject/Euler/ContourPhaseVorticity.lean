module

public import RequestProject.Euler.ContourPhaseEnclosedDomain
public import RequestProject.Euler.ContourPatchVelocityBounds

/-! The actual indicator density of the intrinsic enclosed domains.
It agrees on every phase-chart overlap and its true Biot--Savart
velocity is the original contour boundary field. -/

@[expose] public section

set_option maxHeartbeats 2500000

noncomputable section

open Complex Set Filter Topology MeasureTheory
open scoped NNReal

namespace Euler2D

local instance (priority := 2000) phaseVorticityC1_group (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) := Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)
local instance (priority := 2000) phaseVorticityC1_space (γ : ℝ≥0) :
    NormedSpace ℝ (ContourC1Space γ) := Submodule.normedSpace (contourC1GraphSubmodule γ)

def phaseContourPatchVorticity {γ : ℝ≥0} (Z : ContourC1Space γ) : ℂ → ℝ :=
  (contourRadialFill (ContourC1Space.lift γ Z)).indicator (fun _ => 1)

def phaseFiniteContourPatchVorticity {γ : ℝ≥0} {ι : Type*} [Fintype ι]
    (g : ι → ℝ) (Z : ι → ContourC1Space γ) : ℂ → ℝ :=
  fun x => ∑ j, g j * phaseContourPatchVorticity (Z j) x

theorem phaseContourPatchVorticity_parameterShift {γ : ℝ≥0} (b : ℝ) (Z : ContourC1Space γ) :
    phaseContourPatchVorticity (contourParameterShiftC1 b Z) = phaseContourPatchVorticity Z := by
  unfold phaseContourPatchVorticity
  rw [contourRadialFill_parameterShiftC1]

theorem phaseFiniteContourPatchVorticity_parameterShift {γ : ℝ≥0} {ι : Type*} [Fintype ι]
    (g : ι → ℝ) (b : ι → ℝ) (Z : ι → ContourC1Space γ) :
    phaseFiniteContourPatchVorticity g (fun i => contourParameterShiftC1 (b i) (Z i)) =
      phaseFiniteContourPatchVorticity g Z := by
  unfold phaseFiniteContourPatchVorticity
  simp only [phaseContourPatchVorticity_parameterShift]

section Chart

variable {γ : ℝ≥0} {ι : Type*} [Fintype ι]
  (g : ι → ℝ) (Z Z₀ : ι → ContourC1Space γ) (r : ι → ℝ)
  (hr : ∀ i, 0 < r i) (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (r i))
  (b : ι → ℝ) (hsmall : ∀ i, ‖contourParameterShiftC1 (b i) (Z i) - Z₀ i‖ ≤ r i / 4)

include hr href hsmall

theorem phaseFiniteContourPatchVorticity_eq_chart :
    phaseFiniteContourPatchVorticity g Z = finiteContourC1PatchVorticity g
      (fun i => contourParameterShiftC1 (b i) (Z i)) Z₀ r hr href hsmall := by
  funext x
  unfold phaseFiniteContourPatchVorticity finiteContourC1PatchVorticity
  apply Finset.sum_congr rfl
  intro i _
  rw [phaseContourPatchVorticity, contourC1PatchVorticity,
    contourRadialFill_eq_enclosedDomain_of_shift (Z i) (Z₀ i) (hr i) (href i) (b i) (hsmall i)]

theorem integrable_phaseFiniteContourPatchVorticity : Integrable (phaseFiniteContourPatchVorticity g Z) := by
  rw [phaseFiniteContourPatchVorticity_eq_chart g Z Z₀ r hr href b hsmall]
  exact integrable_finiteContourC1PatchVorticity g _ Z₀ r hr href hsmall

theorem abs_phaseFiniteContourPatchVorticity_le (x : ℂ) :
    |phaseFiniteContourPatchVorticity g Z x| ≤ finiteContourPatchSupBound g := by
  rw [phaseFiniteContourPatchVorticity_eq_chart g Z Z₀ r hr href b hsmall]
  exact abs_finiteContourC1PatchVorticity_le g _ Z₀ r hr href hsmall x

theorem integral_abs_phaseFiniteContourPatchVorticity_le :
    (∫ x, |phaseFiniteContourPatchVorticity g Z x|) ≤ finiteContourPatchMassBound g r := by
  rw [phaseFiniteContourPatchVorticity_eq_chart g Z Z₀ r hr href b hsmall]
  exact integral_abs_finiteContourC1PatchVorticity_le g _ Z₀ r hr href hsmall

theorem norm_le_of_phaseFiniteContourPatchVorticity_ne_zero {R : ℝ}
    (hrR : ∀ i, 5 * r i / 4 ≤ R) {x : ℂ} (hx : phaseFiniteContourPatchVorticity g Z x ≠ 0) :
    ‖x‖ ≤ R := by
  by_contra hn
  have hzero (i : ι) : phaseContourPatchVorticity (Z i) x = 0 := by
    apply indicator_of_notMem
    intro hi
    have hb := norm_lt_of_mem_contourRadialFill_of_shift (Z i) (Z₀ i) (hr i) (href i)
      (b i) (hsmall i) hi
    exact hn (hb.le.trans (hrR i))
  apply hx
  simp only [phaseFiniteContourPatchVorticity, hzero, mul_zero, Finset.sum_const_zero]

theorem contourBoundaryField_eq_phase_actual_velocity (i : ι) (θ : ℝ) :
    contourBoundaryField g (fun j => ContourC1Space.lift γ (Z j)) i θ =
      velocityC (phaseFiniteContourPatchVorticity g Z) (ContourC1Space.lift γ (Z i) θ) := by
  let W : ι → ContourC1Space γ := fun j => contourParameterShiftC1 (b j) (Z j)
  have he : (fun j => ContourC1Space.lift γ (W j)) =
      (fun j φ => ContourC1Space.lift γ (Z j) (φ + b j)) := by
    funext j φ
    exact lift_contourParameterShiftC1 (b j) (Z j) φ
  have hfield := contourC1BoundaryField_eq_actual_velocity g W Z₀ r hr href hsmall i (θ - b i)
  change contourBoundaryField g (fun j => ContourC1Space.lift γ (W j)) i (θ - b i) = _ at hfield
  rw [he, contourBoundaryField_reparametrize g (fun j => ContourC1Space.lift γ (Z j)) b
    (fun j x => (ContourC1Space.hasDerivAt_lift (Z j) x).differentiableAt)
    (fun j => ContourC1Space.periodic_lift (Z j))
    (fun j => periodic_deriv (ContourC1Space.periodic_lift (Z j))), sub_add_cancel] at hfield
  have hd := phaseFiniteContourPatchVorticity_eq_chart g Z Z₀ r hr href b hsmall
  rw [hd]
  simpa only [W, lift_contourParameterShiftC1, sub_add_cancel] using hfield

end Chart

end Euler2D

end
