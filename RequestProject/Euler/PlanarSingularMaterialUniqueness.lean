module

public import RequestProject.Euler.CoupledPlanarBiotSavartAffine
public import RequestProject.Euler.UniformLogLabelParticleUniqueness
public import RequestProject.Euler.PlanarMaterialParticleUniqueness
public import RequestProject.Euler.GlobalPlanarEulerBounds

/-! Actual nonlinear uniqueness for bounded integrable planar
vorticity and the original singular kernel. The proved coupling
estimate is instantiated on the genuine volume-preserving maps. -/

@[expose] public section

set_option maxHeartbeats 6000000

noncomputable section

open MeasureTheory Set Filter Topology

namespace Euler2D

theorem PlanarMaterialParticleFlow.forward_eq_of_measurePreserving_homeomorphs
    {w : R2 → ℝ} {T B : ℝ} (P Q : PlanarMaterialParticleFlow kernelK w T)
    (hw : Integrable w) (hB : ∀ x, ‖w x‖ ≤ B) (hT : 0 ≤ T)
    (XP XQ : Icc (0 : ℝ) T → R2 ≃ₜ R2)
    (hXP : ∀ t, (XP t : R2 → R2) = P.forward t)
    (hXQ : ∀ t, (XQ t : R2 → R2) = Q.forward t)
    (hPX : ∀ t, MeasurePreserving (XP t) volume volume)
    (hQX : ∀ t, MeasurePreserving (XQ t) volume volume) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ a, P.forward t a = Q.forward t a := by
  let V : ℝ := B + ∫ b, ‖w b‖
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hV : 0 ≤ V := add_nonneg hB0 (integral_nonneg (fun b => norm_nonneg _))
  have hvP (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (x : R2) : ‖P.velocity t x‖ ≤ V := by
    rw [P.source_integral t ht, ← hXP ⟨t, ht⟩]
    exact norm_planarMaterialBiotSavart_le_sum hw hB (XP ⟨t, ht⟩) (hPX ⟨t, ht⟩) x
  have hvQ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (x : R2) : ‖Q.velocity t x‖ ≤ V := by
    rw [Q.source_integral t ht, ← hXQ ⟨t, ht⟩]
    exact norm_planarMaterialBiotSavart_le_sum hw hB (XQ ⟨t, ht⟩) (hQX ⟨t, ht⟩) x
  have hp (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (a : R2) : ‖P.forward t a - a‖ ≤ V * t := by
    have he := norm_trajectory_sub_time_le (fun s hs => P.derivative s hs a) hvP
      (show (0 : ℝ) ∈ Icc (0 : ℝ) T from ⟨le_rfl, hT⟩) ht
    simpa only [P.initial, sub_zero, abs_of_nonneg ht.1] using he
  have hq (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (a : R2) : ‖Q.forward t a - a‖ ≤ V * t := by
    have he := norm_trajectory_sub_time_le (fun s hs => Q.derivative s hs a) hvQ
      (show (0 : ℝ) ∈ Icc (0 : ℝ) T from ⟨le_rfl, hT⟩) ht
    simpa only [Q.initial, sub_zero, abs_of_nonneg ht.1] using he
  let vx : ℝ → R2 → R2 := fun t a => P.velocity t (P.forward t a)
  let vy : ℝ → R2 → R2 := fun t a => Q.velocity t (Q.forward t a)
  have hvc (a : R2) : Continuous (fun t => vx t a) := P.continuous_velocity.comp
    (continuous_id.prodMk (P.continuous_forward.comp (continuous_id.prodMk continuous_const)))
  have hwc (a : R2) : Continuous (fun t => vy t a) := Q.continuous_velocity.comp
    (continuous_id.prodMk (Q.continuous_forward.comp (continuous_id.prodMk continuous_const)))
  have hbound (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (a : R2) :
      ‖P.forward t a - Q.forward t a‖ ≤ 2 * V * T := by
    calc
      _ ≤ ‖P.forward t a - a‖ + ‖a - Q.forward t a‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ V * t + V * t := add_le_add (hp t ht a) (by simpa only [norm_sub_rev] using hq t ht a)
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left ht.2 hV]
  apply uniform_log_label_particle_uniqueness (B := 2 * V * T) (C := 20 * V)
    (by positivity) (by positivity) P.forward Q.forward vx vy hvc hwc P.derivative Q.derivative
    (fun a => (P.initial a).trans (Q.initial a).symm) hbound
  intro t ht D hD hd a ε hε hε1
  dsimp only [vx, vy]
  rw [P.source_integral t ht, Q.source_integral t ht, ← hXP ⟨t, ht⟩, ← hXQ ⟨t, ht⟩]
  exact norm_coupled_planarBiotSavart_le_epsilon_affine hw hB (XP ⟨t, ht⟩) (XQ ⟨t, ht⟩)
    (hPX ⟨t, ht⟩) (hQX ⟨t, ht⟩) hD (by simpa only [hXP, hXQ] using hd) a hε hε1

def PlanarEulerParticleSystem.toSingularMaterialFlow
    {w : R2 → ℝ} {T : ℝ} (S : PlanarEulerParticleSystem w T) : PlanarMaterialParticleFlow kernelK w T where
  velocity := S.velocity
  forward := S.particles.forward
  continuous_velocity := S.continuous_velocity
  continuous_forward := S.particles.continuous_forward
  initial := S.particles.initial
  derivative := S.particles.derivative
  source_integral := fun t ht x => by
    rw [S.selfconsistent t x]
    exact (planarMaterialBiotSavart_eq_spatial w (S.particles.homeomorph ⟨t, ht⟩)
      (S.forward_area t ht) x).symm

theorem PlanarEulerParticleSystem.forward_eq_of_bounded_vorticity
    {w : R2 → ℝ} {T B : ℝ} (S Q : PlanarEulerParticleSystem w T)
    (hw : Integrable w) (hB : ∀ x, ‖w x‖ ≤ B) (hT : 0 ≤ T) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ a, S.particles.forward t a = Q.particles.forward t a :=
  S.toSingularMaterialFlow.forward_eq_of_measurePreserving_homeomorphs Q.toSingularMaterialFlow hw hB hT
    S.particles.homeomorph Q.particles.homeomorph (fun _ => rfl) (fun _ => rfl)
    (fun t => S.forward_area t t.property) (fun t => Q.forward_area t t.property)

theorem PlanarEulerParticleSystem.backward_eq_of_bounded_vorticity
    {w : R2 → ℝ} {T B : ℝ} (S Q : PlanarEulerParticleSystem w T)
    (hw : Integrable w) (hB : ∀ x, ‖w x‖ ≤ B) (hT : 0 ≤ T)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (x : R2) :
    S.particles.backward t x = Q.particles.backward t x := by
  have he := S.forward_eq_of_bounded_vorticity Q hw hB hT t ht (Q.particles.backward t x)
  rw [Q.particles.right_inv t ht x] at he
  have hh := congrArg (S.particles.backward t) he
  rw [S.particles.left_inv t ht] at hh
  exact hh.symm

end Euler2D

end
