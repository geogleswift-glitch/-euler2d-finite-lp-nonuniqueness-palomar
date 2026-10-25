module

public import RequestProject.Euler.GlobalPlanarEulerUniqueness

/-! Restart the same genuine planar Euler particle system at a
nonnegative time. The new initial density is its actual transported
vorticity, and its future agrees with every continuation of that datum. -/

@[expose] public section

set_option maxHeartbeats 3000000

noncomputable section

open MeasureTheory Set Filter Topology

namespace Euler2D

def GlobalPlanarEulerParticleSystem.restart {w : R2 → ℝ}
    (S : GlobalPlanarEulerParticleSystem w) {s : ℝ} (hs : 0 ≤ s) :
    GlobalPlanarEulerParticleSystem (S.vorticity s) where
  velocity := fun t x => S.velocity (s + t) x
  forward := fun t a => S.forward (s + t) (S.backward s a)
  backward := fun t x => S.forward s (S.backward (s + t) x)
  continuous_velocity := S.continuous_velocity.comp
    ((continuous_const.add continuous_fst).prodMk continuous_snd)
  continuous_forward := S.continuous_forward.comp
    ((continuous_const.add continuous_fst).prodMk
      (S.continuous_backward.comp (continuous_const.prodMk continuous_snd)))
  continuous_backward := S.continuous_forward.comp
    (continuous_const.prodMk
      (S.continuous_backward.comp ((continuous_const.add continuous_fst).prodMk continuous_snd)))
  initial := by
    intro a
    simpa only [add_zero] using S.right_inv s hs a
  derivative := by
    intro t ht a
    have hd := (S.derivative (s + t) (add_nonneg hs ht) (S.backward s a)).scomp t
      ((hasDerivAt_id t).const_add s)
    simpa only [Function.comp_def, one_smul] using hd
  left_inv := by
    intro t ht a
    rw [S.left_inv (s + t) (add_nonneg hs ht), S.right_inv s hs]
  right_inv := by
    intro t ht a
    rw [S.left_inv s hs, S.right_inv (s + t) (add_nonneg hs ht)]
  forward_area := fun t ht =>
    (S.forward_area (s + t) (add_nonneg hs ht)).comp (S.backward_area s)
  backward_area := fun t => (S.forward_area s hs).comp (S.backward_area (s + t))
  selfconsistent := by
    intro t x
    rw [S.selfconsistent]
    congr 1
    funext y
    change w (S.backward (s + t) y) =
      w (S.backward s (S.forward s (S.backward (s + t) y)))
    rw [S.left_inv s hs]

theorem GlobalPlanarEulerParticleSystem.restart_vorticity {w : R2 → ℝ}
    (S : GlobalPlanarEulerParticleSystem w) {s : ℝ} (hs : 0 ≤ s) (t : ℝ) (x : R2) :
    (S.restart hs).vorticity t x = S.vorticity (s + t) x := by
  change w (S.backward s (S.forward s (S.backward (s + t) x))) =
    w (S.backward (s + t) x)
  rw [S.left_inv s hs]

theorem GlobalPlanarEulerParticleSystem.vorticity_add_eq_of_atTime_eq
    {w f : R2 → ℝ} {B : ℝ} (S : GlobalPlanarEulerParticleSystem w)
    {s : ℝ} (hs : 0 ≤ s) (Q : GlobalPlanarEulerParticleSystem f)
    (hf : Integrable f) (hB : ∀ x, ‖f x‖ ≤ B) (hmatch : S.vorticity s = f)
    {t : ℝ} (ht : 0 ≤ t) (x : R2) :
    S.vorticity (s + t) x = Q.vorticity t x := by
  subst f
  have he := (S.restart hs).vorticity_eq_of_bounded_vorticity Q hf hB ht x
  simpa only [restart_vorticity] using he

end Euler2D

end
