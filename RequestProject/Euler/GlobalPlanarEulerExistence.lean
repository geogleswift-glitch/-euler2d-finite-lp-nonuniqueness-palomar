module

public import RequestProject.Euler.ExpandingPlanarEulerLimit
public import RequestProject.Euler.PositiveParticleIntegralExtension

/-! Actual global positive-time planar Euler particle solutions for
the original singular Biot--Savart kernel and the actual boxed source.
No global flow or positive-time continuation is assumed. -/

@[expose] public section

set_option maxHeartbeats 3500000

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal

namespace Euler2D
namespace ExpandingPlanarEulerLimit

variable {w : R2 → ℝ} {B : ℝ} (S : ExpandingPlanarEulerLimit w)

theorem particle_integral_eq (hw : Integrable w) (hB : ∀ x, ‖w x‖ ≤ B)
    (t : ℝ≥0) (a : R2) :
    positivePairForwardAt S.limit.maps t a = a + ∫ s in (0 : ℝ)..(t : ℝ),
      positiveParticleDerivative S.limit.velocity (fun r x => positivePairForwardAt S.limit.maps r x) s a := by
  let N : ℕ := ⌈(t : ℝ)⌉₊
  have hTN (n : ℕ) : (t : ℝ) ≤ (S.indices (n + N) : ℝ) + 1 := by
    have ha : N ≤ n + N := Nat.le_add_left N n
    have hb : n + N ≤ S.indices (n + N) := S.indices_strictMono.id_le _
    have hc : (N : ℝ) ≤ (S.indices (n + N) : ℝ) := by exact_mod_cast ha.trans hb
    have hd : (t : ℝ) ≤ (N : ℝ) := Nat.le_ceil _
    linarith
  have hsub (n : ℕ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) (t : ℝ)) :
      s ∈ Icc (0 : ℝ) ((S.indices (n + N) : ℝ) + 1) := ⟨hs.1, hs.2.trans (hTN n)⟩
  let gn (n : ℕ) (s : ℝ) := (S.system (S.indices (n + N))).velocity s
    ((S.system (S.indices (n + N))).particles.forward s a)
  let g (s : ℝ) := positiveParticleDerivative S.limit.velocity
    (fun r x => positivePairForwardAt S.limit.maps r x) s a
  have hgnc (n : ℕ) : Continuous (gn n) :=
    (S.system (S.indices (n + N))).continuous_velocity.comp
      (continuous_id.prodMk ((S.system (S.indices (n + N))).particles.continuous_forward.comp
        (continuous_id.prodMk continuous_const)))
  have hbound (n : ℕ) : ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) (t : ℝ)), ‖gn n s‖ ≤ S.V := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact S.speed (S.indices (n + N)) s (hsub n hs) _
  have hgnlim : ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) (t : ℝ)),
      Tendsto (fun n => gn n s) atTop (𝓝 (g s)) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    have hp := (S.velocity_tendsto_along_positions hw hB ⟨s, hs.1⟩
      (S.forward_tendsto ⟨s, hs.1⟩ a)).comp (tendsto_add_atTop_nat N)
    simpa only [Function.comp_apply, gn, g, positiveParticleDerivative,
      Real.toNNReal_of_nonneg hs.1] using hp
  have hXlim (s : ℝ) (hs : s ∈ Icc (0 : ℝ) (t : ℝ)) :
      Tendsto (fun n => (S.system (S.indices (n + N))).particles.forward s a) atTop
        (𝓝 (positivePairForwardAt S.limit.maps s.toNNReal a)) := by
    simpa only [Function.comp_apply, Real.toNNReal_of_nonneg hs.1] using
      (S.forward_tendsto ⟨s, hs.1⟩ a).comp (tendsto_add_atTop_nat N)
  have heq := particle_integral_eq_of_tendsto
    (Xn := fun n s => (S.system (S.indices (n + N))).particles.forward s a)
    (X := fun s => positivePairForwardAt S.limit.maps s.toNNReal a) (gn := gn) (g := g)
    (fun n => (S.system (S.indices (n + N))).particles.initial a)
    (fun n s hs => (S.system (S.indices (n + N))).particles.derivative s (hsub n hs) a)
    (fun n => (hgnc n).aestronglyMeasurable) hbound hgnlim hXlim
    (show (t : ℝ) ∈ Icc (0 : ℝ) (t : ℝ) from ⟨t.coe_nonneg, le_rfl⟩)
  simpa only [Real.toNNReal_coe] using heq

end ExpandingPlanarEulerLimit

structure GlobalPlanarEulerParticleSystem (w : R2 → ℝ) where
  velocity : ℝ → R2 → R2
  forward : ℝ → R2 → R2
  backward : ℝ → R2 → R2
  continuous_velocity : Continuous (Function.uncurry velocity)
  continuous_forward : Continuous (Function.uncurry forward)
  continuous_backward : Continuous (Function.uncurry backward)
  initial : ∀ a, forward 0 a = a
  derivative : ∀ t, 0 ≤ t → ∀ a, HasDerivAt (fun s => forward s a) (velocity t (forward t a)) t
  left_inv : ∀ t, 0 ≤ t → ∀ a, backward t (forward t a) = a
  right_inv : ∀ t, 0 ≤ t → ∀ a, forward t (backward t a) = a
  forward_area : ∀ t, 0 ≤ t → MeasurePreserving (forward t) volume volume
  backward_area : ∀ t, MeasurePreserving (backward t) volume volume
  selfconsistent : ∀ t x, velocity t x = planarKernelVelocity kernelK (fun y => w (backward t y)) x

theorem exists_globalPlanarEulerParticleSystem {w : R2 → ℝ} {B : ℝ}
    (hw : Integrable w μT) (hB : 0 ≤ B) (hwB : ∀ x ∈ torusBox, ‖w x‖ ≤ B) :
    Nonempty (GlobalPlanarEulerParticleSystem (planarBoxSource w)) := by
  obtain ⟨S⟩ := exists_expandingPlanarEulerLimit hw hB hwB
  let F : ℝ≥0 → R2 → R2 := fun t a => positivePairForwardAt S.limit.maps t a
  let v := S.limit.velocity
  have hFc : Continuous (Function.uncurry F) := S.limit.maps.continuous.fst
  have hvc : Continuous (Function.uncurry v) :=
    S.limit.continuous_velocity (integrable_planarBoxSource hw) (norm_planarBoxSource_le hB hwB)
  have hInt : ∀ (t : ℝ≥0) a,
      F t a = a + ∫ s in (0 : ℝ)..(t : ℝ), positiveParticleDerivative v F s a :=
    S.particle_integral_eq (integrable_planarBoxSource hw) (norm_planarBoxSource_le hB hwB)
  let X := positiveParticleIntegralExtension v F
  let Y : ℝ → R2 → R2 := fun t a => positivePairBackwardAt S.limit.maps t.toNNReal a
  have hXeq (t : ℝ) (ht : 0 ≤ t) (a : R2) : X t a = F t.toNNReal a := by
    simpa only [Real.coe_toNNReal t ht] using positiveParticleIntegralExtension_eq hInt t.toNNReal a
  refine ⟨{
    velocity := positiveParticleVelocityExtension v
    forward := X
    backward := Y
    continuous_velocity := continuous_positiveParticleVelocityExtension hvc
    continuous_forward := continuous_positiveParticleIntegralExtension hvc hFc
    continuous_backward := S.limit.maps.continuous.snd.comp
      ((continuous_real_toNNReal.comp continuous_fst).prodMk continuous_snd)
    initial := positiveParticleIntegralExtension_zero v F
    derivative := fun t ht a => positiveParticleIntegralExtension_hasDerivAt_nonneg hvc hFc hInt ht a
    left_inv := ?_
    right_inv := ?_
    forward_area := ?_
    backward_area := fun t => S.limit.backward_area t.toNNReal
    selfconsistent := fun t x => rfl
  }⟩
  · intro t ht a
    rw [hXeq t ht a]
    exact S.limit.left_inv t.toNNReal a
  · intro t ht a
    rw [hXeq t ht (Y t a)]
    exact S.limit.right_inv t.toNNReal a
  · intro t ht
    have he : X t = F t.toNNReal := funext (hXeq t ht)
    rw [he]
    exact S.limit.forward_area t.toNNReal

end Euler2D

end
