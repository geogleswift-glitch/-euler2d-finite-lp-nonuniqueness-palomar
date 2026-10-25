module

public import RequestProject.Euler.CircularFiniteOuterContourForcing
public import RequestProject.Euler.PhaseOuterRadialBounds

/-! Cubic radial feedback of an actual transported finite label,
with the very same Euler particle system and material domain images.
The circular reference is cancelled in the true velocity integral. -/

@[expose] public section

set_option maxHeartbeats 2400000

noncomputable section

open Complex ComplexConjugate Set MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

def circularRadialPerturbationWeight : ℝ :=
  ∑ i : Fin 2, |circularContourStrengths i| * circularContourRadii i

theorem finiteCircularInterfaceRadialWeight_eq (A₀ b : ℝ) {N : ℕ} (j : Fin (N + 1)) :
    (∑ i : Fin 2, |finiteCircularInterfaceStrength A₀ b (j, i)| * circularContourRadii i) =
      |ampScale A₀ b j| * circularRadialPerturbationWeight := by
  simp only [finiteCircularInterfaceStrength, abs_mul, circularRadialPerturbationWeight,
    Finset.mul_sum, mul_assoc]

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem abs_radial_component_boxed_finitePeriodicLabel_le {s A₀ b R ρ : ℝ}
    (hs : s ≤ 0) (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (N : ℕ) (j : Fin (N + 1)) {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)
    (Z : FiniteCircularIndex N → ContourC1Space γ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T)
    (hstartbox : ∀ i, complexTorusPoint '' contourRadialFill (ContourC1Space.lift γ
      (finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N (j, i)).val) ⊆ torusBox)
    (hendbox : ∀ i, complexTorusPoint '' contourRadialFill (ContourC1Space.lift γ (Z (j, i))) ⊆ torusBox)
    (himages : ∀ i, S.forward t '' (complexTorusPoint '' contourRadialFill (ContourC1Space.lift γ
        (finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N (j, i)).val)) =
      complexTorusPoint '' contourRadialFill (ContourC1Space.lift γ (Z (j, i))))
    (Z₀ : Fin 2 → ContourC1Space γ) (β : Fin 2 → ℝ) {c q : ℝ} (hc : 0 < c)
    (href : ∀ i, ContourC1Space.lift γ (Z₀ i) =
      refCircle (circularContourRadii i * radScale R ρ j))
    (hsmall : ∀ i, ‖contourParameterShiftC1 (β i) (Z (j, i)) - Z₀ i‖ ≤
      circularContourRadii i * radScale R ρ j / 4)
    (hq : ∀ i, ‖contourParameterShiftC1 (β i) (Z (j, i)) - Z₀ i‖ ≤ radScale R ρ j * q)
    (hcore : ∀ i, c ≤ 3 * circularContourRadii i / 4)
    (hrot : ∀ i θ, ContourC1Space.lift γ (Z (j, i)) (θ + Real.pi / 2) =
      I * ContourC1Space.lift γ (Z (j, i)) θ)
    {x : ℂ} (hx : ‖x‖ ≤ c * radScale R ρ j / 2) :
    |(velocityC (boxedComplexDensity
        (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N j) t)) x * conj x).re| ≤
      (32 / (15 * c ^ 4) * (|ampScale A₀ b j| * circularRadialPerturbationWeight)) * q *
        ‖x‖ ^ 4 / radScale R ρ j ^ 2 := by
  have he : boxedComplexDensity (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N j) t) =
      phaseFiniteContourPatchVorticity (fun i => finiteCircularInterfaceStrength A₀ b (j, i))
        (fun i => Z (j, i)) := by
    funext y
    exact P.boxed_transported_finitePeriodicLabel_eq_phaseContours hs hR hRmax hρ hρ1
      N j S Z t ht hstartbox hendbox himages y
  rw [he, ← finiteCircularInterfaceRadialWeight_eq A₀ b j]
  exact abs_radial_component_phaseFiniteContourPatchVelocity_le
    (fun i => finiteCircularInterfaceStrength A₀ b (j, i)) (fun i => Z (j, i)) Z₀
    circularContourRadii β hc (radScale_pos hR hρ j) (fun i => (circularContourRadii_bounds i).1)
    href hsmall hq hcore hrot hx

end CircularMaterialTransferProfile
end Euler2D

end
