module

public import RequestProject.Euler.CircularReferenceExteriorVelocity
public import RequestProject.Euler.CircularFiniteOuterRigidDecomposition
public import RequestProject.Euler.CircularFiniteClusterInvariants

/-! The circular reference of each actual finite label has zero mass
and zero full exterior velocity. Its transported perturbation therefore
has zero mass and is the entire exterior interaction of that same S. -/

@[expose] public section

set_option maxHeartbeats 5000000

noncomputable section

open Complex Set MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D
namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem finiteCircularReference_weighted_radius_sq_zero (A₀ b R ρ : ℝ)
    {N : ℕ} (j : Fin (N + 1)) :
    (∑ i : Fin 2, finiteCircularInterfaceStrength A₀ b (j, i) *
      (circularContourRadii i * radScale R ρ j) ^ 2) = 0 := by
  norm_num [Fin.sum_univ_two, finiteCircularInterfaceStrength, circularContourStrengths,
    circularContourRadii, mul_pow, cellA_sq]
  <;> ring

theorem finiteCircularReference_integral_zero {A₀ b R ρ : ℝ}
    (hR : 0 < R) (hρ : 0 < ρ) {N : ℕ} (j : Fin (N + 1)) :
    (∫ x : ℂ, ∑ i : Fin 2, finiteCircularInterfaceStrength A₀ b (j, i) *
      circlePatchVorticity (circularContourRadii i * radScale R ρ j) x) = 0 := by
  rw [integral_finset_sum _ (fun i _ => (integrable_circlePatchVorticity _).const_mul _)]
  simp_rw [integral_const_mul, integral_circlePatchVorticity
    (mul_nonneg (circularContourRadii_bounds _).1.le (radScale_pos hR hρ j).le)]
  calc
    _ = Real.pi * ∑ i : Fin 2, finiteCircularInterfaceStrength A₀ b (j, i) *
        (circularContourRadii i * radScale R ρ j) ^ 2 := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
    _ = 0 := by rw [finiteCircularReference_weighted_radius_sq_zero, mul_zero]

include hγ hγ1 in
theorem finiteCircularReference_velocity_zero_outside {A₀ b R ρ : ℝ}
    (hR : 0 < R) (hρ : 0 < ρ) {N : ℕ} (j : Fin (N + 1))
    {x : ℂ} (hx : radScale R ρ j ≤ ‖x‖) :
    velocityC (fun y => ∑ i : Fin 2, finiteCircularInterfaceStrength A₀ b (j, i) *
      circlePatchVorticity (circularContourRadii i * radScale R ρ j) y) x = 0 := by
  exact velocityC_finiteCircles_zero_outside hγ hγ1.le _ _
    (fun i => mul_pos (circularContourRadii_bounds i).1 (radScale_pos hR hρ j))
    (finiteCircularReference_weighted_radius_sq_zero A₀ b R ρ j)
    (fun i => (mul_le_of_le_one_left (radScale_pos hR hρ j).le
      (circularContourRadii_bounds i).2.2).trans hx)

theorem integral_finiteOuterLabelComplexPerturbation_zero {s A₀ b R ρ : ℝ}
    (hs : s ≤ 0) (hA : 0 ≤ A₀) (hb : 0 < b)
    (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (N : ℕ) (j : Fin (N + 1)) {f : Lp ℝ 2 μT} {T : ℝ}
    (S : BoundedEulerParticleSystem f T) (t : ℝ) :
    (∫ x : ℂ, P.finiteOuterLabelComplexPerturbation s A₀ b R ρ N j S t x) = 0 := by
  obtain ⟨hi, hp, _⟩ := P.finitePeriodicLabel_bounds hs hA hb hR hRmax hρ hρ1 N j
  unfold finiteOuterLabelComplexPerturbation
  rw [integral_sub (integrable_boxedComplexDensity
    (S.integrable_transportedScalar_of_integrable hi t))
    (integrable_finset_sum _ (fun i _ => (integrable_circlePatchVorticity _).const_mul _)),
    integral_boxedComplexDensity, S.integral_transportedScalar hi hp,
    P.integral_finitePeriodicLabel_zero hs hR hRmax hρ hρ1 N j,
    finiteCircularReference_integral_zero hR hρ j, sub_self]

include hγ hγ1 in
theorem velocityC_boxed_finiteLabel_eq_exteriorPerturbation {s A₀ b R ρ : ℝ}
    (hs : s ≤ 0) (hA : 0 ≤ A₀) (hb : 0 < b)
    (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (N : ℕ) (j : Fin (N + 1)) {f : Lp ℝ 2 μT} {T : ℝ}
    (S : BoundedEulerParticleSystem f T) (t : ℝ) {x : ℂ}
    (hx : radScale R ρ j ≤ ‖x‖) :
    velocityC (boxedComplexDensity
      (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N j) t)) x =
      velocityC (P.finiteOuterLabelComplexPerturbation s A₀ b R ρ N j S t) x := by
  let ref : ℂ → ℝ := fun y => ∑ i : Fin 2, finiteCircularInterfaceStrength A₀ b (j, i) *
    circlePatchVorticity (circularContourRadii i * radScale R ρ j) y
  obtain ⟨hi, hbound, _⟩ := P.boxed_finitePeriodicLabel_bounds hs hA hb hR hRmax hρ hρ1 N j S t
  have hiRef : Integrable ref := integrable_finset_sum _ fun i _ =>
    (integrable_circlePatchVorticity _).const_mul _
  have hRef (y : ℂ) : |ref y| ≤ ∑ i : Fin 2, |finiteCircularInterfaceStrength A₀ b (j, i)| := by
    calc
      _ ≤ ∑ i : Fin 2, |finiteCircularInterfaceStrength A₀ b (j, i)| *
          |circlePatchVorticity (circularContourRadii i * radScale R ρ j) y| := by
        simpa only [ref, Real.norm_eq_abs, abs_mul] using norm_sum_le Finset.univ
          (fun i : Fin 2 => finiteCircularInterfaceStrength A₀ b (j, i) *
            circlePatchVorticity (circularContourRadii i * radScale R ρ j) y)
      _ ≤ ∑ i : Fin 2, |finiteCircularInterfaceStrength A₀ b (j, i)| * 1 :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
          (abs_circlePatchVorticity_le_one _ _) (abs_nonneg _))
      _ = _ := by simp
  have hh := velocityC_sub_of_bounded hi hiRef hbound hRef x
  change velocityC (P.finiteOuterLabelComplexPerturbation s A₀ b R ρ N j S t) x =
    velocityC (boxedComplexDensity
      (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N j) t)) x - velocityC ref x at hh
  have hv := finiteCircularReference_velocity_zero_outside (hγ := hγ) (hγ1 := hγ1)
    (A₀ := A₀) (b := b) hR hρ j hx
  change velocityC ref x = 0 at hv
  rw [hv, sub_zero] at hh
  exact hh.symm

end CircularMaterialTransferProfile
end Euler2D

end


