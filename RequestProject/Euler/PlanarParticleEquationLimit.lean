module

public import RequestProject.Euler.PlanarRegularizedFlowLimit
public import RequestProject.Euler.ParticleEquationLimit

/-! The original nonlinear planar particle equation is obtained by
passing the actual regularized integral equations to the same limit.
The primitive extension gives true derivatives even at both endpoints. -/

@[expose] public section

set_option maxHeartbeats 3500000

noncomputable section

open MeasureTheory Set Filter Topology

namespace Euler2D
namespace PlanarRegularizedFlowLimit

variable {w : R2 → ℝ} {T B : ℝ} (S : PlanarRegularizedFlowLimit w T)

theorem particle_integral_eq (hw : Integrable w μT) (hB : 0 ≤ B)
    (hwB : ∀ x ∈ torusBox, ‖w x‖ ≤ B) (hT : 0 ≤ T)
    (t : Icc (0 : ℝ) T) (a : R2) :
    planarPairForwardAt S.limit.maps t a = a + ∫ s in (0 : ℝ)..(t : ℝ),
      clampedParticleDerivative hT S.limit.velocity (fun r x => planarPairForwardAt S.limit.maps r x) s a := by
  let gn (n : ℕ) (s : ℝ) :=
    (S.system (S.indices n)).velocity s ((S.system (S.indices n)).particles.forward s a)
  let g (s : ℝ) :=
    clampedParticleDerivative hT S.limit.velocity (fun r x => planarPairForwardAt S.limit.maps r x) s a
  have hgnc (n : ℕ) : Continuous (gn n) :=
    (S.system (S.indices n)).bounded.continuous.comp
      (continuous_id.prodMk ((S.system (S.indices n)).particles.continuous_forward.comp
        (continuous_id.prodMk continuous_const)))
  have hgnbound (n : ℕ) : ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) T), ‖gn n s‖ ≤ S.V := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact S.speed (S.indices n) s hs _
  have hgnpoint (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) :
      Tendsto (fun n => gn n s) atTop (𝓝 (g s)) := by
    have hg : g s = S.limit.velocity ⟨s, hs⟩ (planarPairForwardAt S.limit.maps ⟨s, hs⟩ a) := by
      dsimp only [g, clampedParticleDerivative]
      rw [projIcc_of_mem hT hs]
    rw [hg]
    exact S.velocity_tendsto_along_positions hw hB hwB ⟨s, hs⟩ (S.forward_tendsto ⟨s, hs⟩ a)
  have hgnlim : ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) T),
      Tendsto (fun n => gn n s) atTop (𝓝 (g s)) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact hgnpoint s hs
  have hXlim (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) :
      Tendsto (fun n => (S.system (S.indices n)).particles.forward s a) atTop
        (𝓝 (planarPairForwardAt S.limit.maps (projIcc 0 T hT s) a)) := by
    simpa only [projIcc_of_mem hT hs] using S.forward_tendsto ⟨s, hs⟩ a
  have heq := particle_integral_eq_of_tendsto
    (Xn := fun n s => (S.system (S.indices n)).particles.forward s a)
    (X := fun s => planarPairForwardAt S.limit.maps (projIcc 0 T hT s) a) (gn := gn) (g := g)
    (fun n => (S.system (S.indices n)).particles.initial a)
    (fun n s hs => (S.system (S.indices n)).particles.derivative s hs a)
    (fun n => (hgnc n).aestronglyMeasurable) hgnbound hgnlim hXlim t.property
  simpa only [projIcc_of_mem hT t.property] using heq

end PlanarRegularizedFlowLimit

structure PlanarEulerParticleSystem (w : R2 → ℝ) (T : ℝ) where
  velocity : ℝ → R2 → R2
  particles : PlanarLogParticleFlow velocity T
  continuous_velocity : Continuous (Function.uncurry velocity)
  forward_area : ∀ t ∈ Icc (0 : ℝ) T, MeasurePreserving (particles.forward t) volume volume
  backward_area : ∀ t, MeasurePreserving (particles.backward t) volume volume
  selfconsistent : ∀ t x, velocity t x =
    planarKernelVelocity kernelK (fun y => w (particles.backward t y)) x

theorem exists_planarEulerParticleSystem {w : R2 → ℝ} {B : ℝ}
    (hw : Integrable w μT) (hB : 0 ≤ B) (hwB : ∀ x ∈ torusBox, ‖w x‖ ≤ B)
    {T : ℝ} (hT : 0 ≤ T) : Nonempty (PlanarEulerParticleSystem (planarBoxSource w) T) := by
  obtain ⟨S⟩ := exists_planarRegularizedFlowLimit hw hB hwB hT
  let F : Icc (0 : ℝ) T → R2 → R2 := fun t a => planarPairForwardAt S.limit.maps t a
  let v := S.limit.velocity
  have hFc : Continuous (Function.uncurry F) := S.limit.maps.continuous.fst
  have hvc : Continuous (Function.uncurry v) :=
    S.limit.continuous_velocity (integrable_planarBoxSource hw) (norm_planarBoxSource_le hB hwB)
  have hInt : ∀ (t : Icc (0 : ℝ) T) a,
      F t a = a + ∫ s in (0 : ℝ)..(t : ℝ), clampedParticleDerivative hT v F s a :=
    S.particle_integral_eq hw hB hwB hT
  let X := particleIntegralExtension hT v F
  let Y : ℝ → R2 → R2 := fun t a => planarPairBackwardAt S.limit.maps (projIcc 0 T hT t) a
  have hXeq (t : Icc (0 : ℝ) T) (a : R2) : X t a = F t a :=
    particleIntegralExtension_eq hT hInt t a
  have hYeq (t : Icc (0 : ℝ) T) (a : R2) : Y t a = planarPairBackwardAt S.limit.maps t a := by
    dsimp only [Y]
    rw [projIcc_val]
  let P : PlanarLogParticleFlow (particleVelocityExtension hT v) T := {
    forward := X
    backward := Y
    continuous_forward := continuous_particleIntegralExtension hT hvc hFc
    continuous_backward := S.limit.maps.continuous.snd.comp
      (((continuous_projIcc (h := hT)).comp continuous_fst).prodMk continuous_snd)
    initial := particleIntegralExtension_zero hT v F
    derivative := fun t ht a => particleIntegralExtension_hasDerivAt_on_Icc hT hvc hFc hInt ht a
    left_inv := by
      intro t ht a
      rw [hXeq ⟨t, ht⟩, hYeq ⟨t, ht⟩]
      exact S.limit.left_inv _ a
    right_inv := by
      intro t ht a
      rw [hYeq ⟨t, ht⟩, hXeq ⟨t, ht⟩]
      exact S.limit.right_inv _ a
  }
  refine ⟨⟨particleVelocityExtension hT v, P, continuous_particleVelocityExtension hT hvc,
    ?_, ?_, ?_⟩⟩
  · intro t ht
    change MeasurePreserving (X t) volume volume
    have he : X t = F ⟨t, ht⟩ := funext (hXeq ⟨t, ht⟩)
    rw [he]
    exact S.limit.forward_area _
  · intro t
    change MeasurePreserving (Y t) volume volume
    exact S.limit.backward_area (projIcc 0 T hT t)
  · intro t x
    rfl

end Euler2D

end
