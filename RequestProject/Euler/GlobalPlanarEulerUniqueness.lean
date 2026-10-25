module

public import RequestProject.Euler.PlanarSingularMaterialUniqueness

/-! Global positive-time uniqueness for the actual bounded-vorticity
Euler particle systems constructed with the original singular kernel. -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology

namespace Euler2D

def GlobalPlanarEulerParticleSystem.restrictFinite
    {w : R2 → ℝ} (S : GlobalPlanarEulerParticleSystem w) (T : ℝ) : PlanarEulerParticleSystem w T where
  velocity := S.velocity
  particles := {
    forward := S.forward
    backward := S.backward
    continuous_forward := S.continuous_forward
    continuous_backward := S.continuous_backward
    initial := S.initial
    derivative := fun t ht => S.derivative t ht.1
    left_inv := fun t ht => S.left_inv t ht.1
    right_inv := fun t ht => S.right_inv t ht.1 }
  continuous_velocity := S.continuous_velocity
  forward_area := fun t ht => S.forward_area t ht.1
  backward_area := S.backward_area
  selfconsistent := S.selfconsistent

theorem GlobalPlanarEulerParticleSystem.forward_eq_of_bounded_vorticity
    {w : R2 → ℝ} {B : ℝ} (S Q : GlobalPlanarEulerParticleSystem w)
    (hw : Integrable w) (hB : ∀ x, ‖w x‖ ≤ B)
    {t : ℝ} (ht : 0 ≤ t) (a : R2) : S.forward t a = Q.forward t a :=
  (S.restrictFinite t).forward_eq_of_bounded_vorticity (Q.restrictFinite t) hw hB ht t ⟨ht, le_rfl⟩ a

theorem GlobalPlanarEulerParticleSystem.backward_eq_of_bounded_vorticity
    {w : R2 → ℝ} {B : ℝ} (S Q : GlobalPlanarEulerParticleSystem w)
    (hw : Integrable w) (hB : ∀ x, ‖w x‖ ≤ B)
    {t : ℝ} (ht : 0 ≤ t) (a : R2) : S.backward t a = Q.backward t a :=
  (S.restrictFinite t).backward_eq_of_bounded_vorticity (Q.restrictFinite t) hw hB ht t ⟨ht, le_rfl⟩ a

theorem GlobalPlanarEulerParticleSystem.velocity_eq_of_bounded_vorticity
    {w : R2 → ℝ} {B : ℝ} (S Q : GlobalPlanarEulerParticleSystem w)
    (hw : Integrable w) (hB : ∀ x, ‖w x‖ ≤ B)
    {t : ℝ} (ht : 0 ≤ t) (a : R2) : S.velocity t a = Q.velocity t a := by
  rw [S.selfconsistent, Q.selfconsistent]
  congr 1
  funext y
  rw [S.backward_eq_of_bounded_vorticity Q hw hB ht y]

theorem GlobalPlanarEulerParticleSystem.vorticity_eq_of_bounded_vorticity
    {w : R2 → ℝ} {B : ℝ} (S Q : GlobalPlanarEulerParticleSystem w)
    (hw : Integrable w) (hB : ∀ x, ‖w x‖ ≤ B)
    {t : ℝ} (ht : 0 ≤ t) (a : R2) : S.vorticity t a = Q.vorticity t a := by
  change w (S.backward t a) = w (Q.backward t a)
  rw [S.backward_eq_of_bounded_vorticity Q hw hB ht a]

end Euler2D

end
