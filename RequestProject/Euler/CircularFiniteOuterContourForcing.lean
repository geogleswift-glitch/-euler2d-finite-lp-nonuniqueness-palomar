module

public import RequestProject.Euler.CircularFinitePhaseLabelIdentification
public import RequestProject.Euler.PhaseOuterContourForcing

/-! Outer-label contour forcing of the very same finite Euler system.
The actual transported label is identified globally with its material
phase density, including outside the torus chart.  Its perturbation
from the original circular reference then has the proved Little norm. -/

@[expose] public section

set_option maxHeartbeats 2900000

noncomputable section

open Complex Set MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D
namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

def finiteOuterLabelComplexPerturbation (s A₀ b R ρ : ℝ) (N : ℕ) (j : Fin (N + 1))
    {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T) (t : ℝ) : ℂ → ℝ :=
  fun x => boxedComplexDensity (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N j) t) x -
    ∑ i : Fin 2, finiteCircularInterfaceStrength A₀ b (j, i) *
      circlePatchVorticity (circularContourRadii i * radScale R ρ j) x

section Label

variable {s A₀ b R ρ : ℝ} (hs : s ≤ 0) (hR : 0 < R) (hRmax : R ≤ 1 / 2)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (N : ℕ) (j : Fin (N + 1))
    {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)
    (Z : FiniteCircularIndex N → ContourC1Space γ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T)
    (hstartbox : ∀ i, complexTorusPoint '' contourRadialFill (ContourC1Space.lift γ
      (finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N (j, i)).val) ⊆ torusBox)
    (hendbox : ∀ i, complexTorusPoint '' contourRadialFill (ContourC1Space.lift γ (Z (j, i))) ⊆ torusBox)
    (himages : ∀ i, S.forward t '' (complexTorusPoint '' contourRadialFill (ContourC1Space.lift γ
        (finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N (j, i)).val)) =
      complexTorusPoint '' contourRadialFill (ContourC1Space.lift γ (Z (j, i))))

include hs hR hRmax hρ hρ1 ht hstartbox hendbox himages

theorem boxed_transported_finitePeriodicLabel_eq_phaseContours (x : ℂ) :
    boxedComplexDensity (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N j) t) x =
      phaseFiniteContourPatchVorticity (fun i => finiteCircularInterfaceStrength A₀ b (j, i))
        (fun i => Z (j, i)) x := by
  by_cases hx : complexTorusPoint x ∈ torusBox
  · rw [boxedComplexDensity, indicator_of_mem hx]
    have hh := P.transported_finitePeriodicLabel_eq_phaseContours (A₀ := A₀) (b := b) hs hR hRmax hρ hρ1
      N j S Z t ht hstartbox hendbox himages hx
    simpa only [centeredComplexHomeomorph_symm_apply, complexTorusPoint,
      add_sub_cancel_right, LinearIsometryEquiv.symm_apply_apply] using hh
  · rw [boxedComplexDensity, indicator_of_notMem hx]
    symm
    apply Finset.sum_eq_zero
    intro i _
    have hn : x ∉ contourRadialFill (ContourC1Space.lift γ (Z (j, i))) :=
      fun hz => hx (hendbox i ⟨x, hz, rfl⟩)
    simp only [phaseContourPatchVorticity, indicator_of_notMem hn, mul_zero]

theorem finiteOuterLabelComplexPerturbation_eq_phaseContours :
    P.finiteOuterLabelComplexPerturbation s A₀ b R ρ N j S t =
      phaseFiniteContourPatchPerturbation (fun i => finiteCircularInterfaceStrength A₀ b (j, i))
        (fun i => Z (j, i)) (fun i => circularContourRadii i * radScale R ρ j) := by
  funext x
  rw [phaseFiniteContourPatchPerturbation_eq_difference]
  exact congrArg (fun v => v - ∑ i : Fin 2, finiteCircularInterfaceStrength A₀ b (j, i) *
    circlePatchVorticity (circularContourRadii i * radScale R ρ j) x)
      (P.boxed_transported_finitePeriodicLabel_eq_phaseContours hs hR hRmax hρ hρ1
        N j S Z t ht hstartbox hendbox himages x)

/-- Actual same-S outer label, with its original circular reference
subtracted, has the squared scale-ratio forcing in the original Little
space. The only geometric input is the true material contour tube. -/
theorem exists_finiteOuterLabel_contourLittle_ratio {η : ℝ≥0} (hη : (η : ℝ) ≤ 1)
    (Z₀ : Fin 2 → ContourC1Space γ) (β : Fin 2 → ℝ) {c B q r L : ℝ}
    (hc : 0 < c) (hB : 0 < B) (hr : 0 < r)
    (href : ∀ i, ContourC1Space.lift γ (Z₀ i) =
      refCircle (circularContourRadii i * radScale R ρ j))
    (hsmall : ∀ i, ‖contourParameterShiftC1 (β i) (Z (j, i)) - Z₀ i‖ ≤
      circularContourRadii i * radScale R ρ j / 4)
    (hq : ∀ i, ‖contourParameterShiftC1 (β i) (Z (j, i)) - Z₀ i‖ ≤ radScale R ρ j * q)
    (hcore : ∀ i, c ≤ 3 * circularContourRadii i / 4)
    (hrot : ∀ i θ, ContourC1Space.lift γ (Z (j, i)) (θ + Real.pi / 2) =
      I * ContourC1Space.lift γ (Z (j, i)) θ)
    (hsep : 8 * (B * r) ≤ c * radScale R ρ j)
    (W : LittleContourSpace η) (hW : ∀ x, ‖ContourC1Space.toBCF η W.val x‖ ≤ B * r)
    (hL : ‖W‖ ≤ r * L) :
    ∃ Q : LittleContourSpace η,
      (∀ θ, LittleContourSpace.lift η Q θ =
        velocityC (P.finiteOuterLabelComplexPerturbation s A₀ b R ρ N j S t)
          (LittleContourSpace.lift η W θ)) ∧
      ‖Q‖ / r ≤ interiorContourNormBudget (η : ℝ) 1 c B L *
        (4 * Real.pi * ∑ i : Fin 2, |finiteCircularInterfaceStrength A₀ b (j, i)| * circularContourRadii i) *
          (r / radScale R ρ j) ^ 2 * q := by
  have he := P.finiteOuterLabelComplexPerturbation_eq_phaseContours (A₀ := A₀) (b := b) hs hR hRmax hρ hρ1
    N j S Z t ht hstartbox hendbox himages
  rw [he]
  simpa only [abs_one, mul_one, one_mul] using
    (exists_phaseOuterLabelContourFieldLittle_ratio (A := 1) hη
      (fun i => finiteCircularInterfaceStrength A₀ b (j, i)) (fun i => Z (j, i)) Z₀
      circularContourRadii β hc hB (radScale_pos hR hρ j) hr
      (fun i => (circularContourRadii_bounds i).1) href hsmall hq hcore hrot hsep W hW hL)

end Label

end CircularMaterialTransferProfile
end Euler2D

end
