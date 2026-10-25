module

public import RequestProject.Euler.CircularReferenceCoreVelocity
public import RequestProject.Euler.CircularFiniteOuterContourForcing
public import RequestProject.Euler.CircularFinitePlanarClusterVelocity
public import RequestProject.Euler.PhaseOuterRadialBounds

/-! The very same boxed transported outer label equals its full rigid
circular core velocity plus the actual source residual already used by
the outer Little forcing estimate. -/

@[expose] public section

set_option maxHeartbeats 3600000

noncomputable section

open Complex Set MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D
namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

include hγ hγ1

theorem finiteCircularReference_velocity_in_core {A₀ b R ρ : ℝ}
    (hR : 0 < R) (hρ : 0 < ρ) {N : ℕ} (j : Fin (N + 1))
    {x : ℂ} (hx : ‖x‖ ≤ cellA * radScale R ρ j) :
    velocityC (fun y => ∑ i : Fin 2, finiteCircularInterfaceStrength A₀ b (j, i) *
      circlePatchVorticity (circularContourRadii i * radScale R ρ j) y) x =
      ((ampScale A₀ b j : ℝ) : ℂ) * (I / 2) * x := by
  have hr : 0 < radScale R ρ j := radScale_pos hR hρ j
  have hs (i : Fin 2) : 0 < circularContourRadii i * radScale R ρ j :=
    mul_pos (circularContourRadii_bounds i).1 hr
  have hcore (i : Fin 2) : ‖x‖ ≤ circularContourRadii i * radScale R ρ j := by
    fin_cases i
    · exact hx
    · change ‖x‖ ≤ 1 * radScale R ρ j
      exact hx.trans (mul_le_mul_of_nonneg_right cellA_lt_one.le hr.le)
  have hh := velocityC_finiteCircles_inside_core hγ hγ1.le
    (fun i : Fin 2 => finiteCircularInterfaceStrength A₀ b (j, i))
    (fun i => circularContourRadii i * radScale R ρ j) hs hcore
  have he : (∑ i : Fin 2, finiteCircularInterfaceStrength A₀ b (j, i)) = ampScale A₀ b j := by
    norm_num [finiteCircularInterfaceStrength, Fin.sum_univ_two, circularContourStrengths]
    ring
  simpa only [he] using hh

theorem velocityC_boxed_finiteLabel_eq_rigid_add_residual {s A₀ b R ρ : ℝ}
    (hs : s ≤ 0) (hA : 0 ≤ A₀) (hb : 0 < b)
    (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (N : ℕ) (j : Fin (N + 1)) {f : Lp ℝ 2 μT} {T : ℝ}
    (S : BoundedEulerParticleSystem f T) (t : ℝ) {x : ℂ}
    (hx : ‖x‖ ≤ cellA * radScale R ρ j) :
    velocityC (boxedComplexDensity
      (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N j) t)) x =
      ((ampScale A₀ b j : ℝ) : ℂ) * (I / 2) * x +
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
      _ ≤ ∑ i : Fin 2, |finiteCircularInterfaceStrength A₀ b (j, i)| * 1 := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left (abs_circlePatchVorticity_le_one _ _) (abs_nonneg _)
      _ = _ := by simp
  have hh := velocityC_sub_of_bounded hi hiRef hbound hRef x
  change velocityC (P.finiteOuterLabelComplexPerturbation s A₀ b R ρ N j S t) x =
    velocityC (boxedComplexDensity
      (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N j) t)) x - velocityC ref x at hh
  have hv := finiteCircularReference_velocity_in_core (hγ := hγ) (hγ1 := hγ1)
    (A₀ := A₀) (b := b) hR hρ j hx
  change velocityC ref x = _ at hv
  rw [hv] at hh
  linear_combination -hh

end CircularMaterialTransferProfile
end Euler2D

end
