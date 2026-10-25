module

public import RequestProject.Euler.PlanarRegularizedUniformBounds
public import RequestProject.Euler.PlanarTransportFlowLimit

/-! A genuine common subsequence of the constructed nonlinear planar
regularizations. Its limit transports the actual initial density,
and its velocities converge along the actual moving particles. -/

@[expose] public section

set_option maxHeartbeats 3000000

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal

namespace Euler2D

theorem norm_planarBoxSource_le {w : R2 → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hwB : ∀ x ∈ torusBox, ‖w x‖ ≤ B) (x : R2) : ‖planarBoxSource w x‖ ≤ B := by
  by_cases hx : x ∈ torusBox
  · simpa only [planarBoxSource, indicator_of_mem hx] using hwB x hx
  · simpa only [planarBoxSource, indicator_of_notMem hx, norm_zero] using hB

structure PlanarRegularizedFlowLimit (w : R2 → ℝ) (T : ℝ) where
  L : ℕ → ℝ≥0
  M : ℕ → ℝ≥0
  system : ∀ n, SmoothPlanarRegularizedParticleSystem (planarSmoothedBiotSavartKernel n) w T (L n) (M n)
  V : ℝ
  C : ℝ
  speed_nonneg : 0 ≤ V
  modulus_nonneg : 0 ≤ C
  speed : ∀ n t, t ∈ Icc (0 : ℝ) T → ∀ x, ‖(system n).velocity t x‖ ≤ V
  modulus : ∀ n t, t ∈ Icc (0 : ℝ) T → ∀ x y, ‖x - y‖ ≤ 1 / 2 →
    ‖(system n).velocity t x - (system n).velocity t y‖ ≤ C * logFlowModulus ‖x - y‖
  error : ∀ n t, t ∈ Icc (0 : ℝ) T → ∀ x,
    ‖(system n).velocity t x - planarKernelVelocity kernelK ((system n).vorticity t) x‖ ≤
      C * logFlowModulus (planarVelocityApproxScale n)
  limit : PlanarTransportFlowLimit (planarBoxSource w) T
  indices : ℕ → ℕ
  indices_strictMono : StrictMono indices
  converges : Tendsto (fun n => planarFlowPairMap ((system (indices n)).particles)) atTop (𝓝 limit.maps)

theorem exists_planarRegularizedFlowLimit {w : R2 → ℝ} {B : ℝ}
    (hw : Integrable w μT) (hB : 0 ≤ B) (hwB : ∀ x ∈ torusBox, ‖w x‖ ≤ B)
    {T : ℝ} (hT : 0 ≤ T) : Nonempty (PlanarRegularizedFlowLimit w T) := by
  obtain ⟨L, M, S, V, C, hV, hC, hspeed, hlog, herr⟩ :=
    exists_uniform_planarBiotSavart_regularized_systems hw hB hwB hT
  obtain ⟨H, φ, hφ, hlim⟩ := exists_compactOpen_planarFlow_pair_subseq hT hC hV
    (fun n => (S n).particles) hspeed hlog
  obtain ⟨hleft, hright, harea, hinit⟩ := planarFlowPair_limit_inverse_area
    (fun n => (S (φ n)).particles) (fun n => (S (φ n)).forward_area)
    (fun n => (S (φ n)).backward_area) hlim
  exact ⟨{
    L := L
    M := M
    system := S
    V := V
    C := C
    speed_nonneg := hV
    modulus_nonneg := hC
    speed := hspeed
    modulus := hlog
    error := herr
    limit := ⟨H, hleft, hright, fun t => (harea t).1, fun t => (harea t).2, hinit⟩
    indices := φ
    indices_strictMono := hφ
    converges := hlim
  }⟩

namespace PlanarRegularizedFlowLimit

variable {w : R2 → ℝ} {T : ℝ} (S : PlanarRegularizedFlowLimit w T)

theorem forward_tendsto (t : Icc (0 : ℝ) T) (a : R2) :
    Tendsto (fun n => (S.system (S.indices n)).particles.forward t a) atTop
      (𝓝 (planarPairForwardAt S.limit.maps t a)) :=
  (((continuous_eval_const (t, a)).tendsto S.limit.maps).comp S.converges).fst_nhds

theorem density_L1_tendsto (hw : Integrable w μT) (t : Icc (0 : ℝ) T) :
    Tendsto (fun n => ∫ x, ‖(S.system (S.indices n)).vorticity t x - S.limit.density t x‖)
      atTop (𝓝 (0 : ℝ)) := by
  have hg := ((continuous_planarPairBackwardAt_map t).tendsto S.limit.maps).comp S.converges
  exact tendsto_integral_norm_planarTransport_sub (integrable_planarBoxSource hw) hg
    (fun n => (S.system (S.indices n)).backward_area t t.property) (S.limit.backward_area t)

theorem smoothing_error_tendsto :
    Tendsto (fun n => S.C * logFlowModulus (planarVelocityApproxScale (S.indices n)))
      atTop (𝓝 (0 : ℝ)) := by
  have hs := tendsto_planarVelocityApproxScale.comp S.indices_strictMono.tendsto_atTop
  simpa only [logFlowModulus, zero_mul, mul_zero, sub_zero] using
    ((continuous_logFlowModulus.tendsto 0).comp hs).const_mul S.C

theorem velocity_tendsto_along_positions {B : ℝ}
    (hw : Integrable w μT) (hB : 0 ≤ B) (hwB : ∀ x ∈ torusBox, ‖w x‖ ≤ B)
    (t : Icc (0 : ℝ) T) {x : ℕ → R2} {x₀ : R2} (hx : Tendsto x atTop (𝓝 x₀)) :
    Tendsto (fun n => (S.system (S.indices n)).velocity t (x n)) atTop
      (𝓝 (S.limit.velocity t x₀)) := by
  have hb := tendsto_planarBiotSavart_apply_of_L1
    (fun n => (S.system (S.indices n)).integrable_vorticity hw t.property)
    (S.limit.integrable_density (integrable_planarBoxSource hw) t)
    (fun n => (S.system (S.indices n)).norm_vorticity_le hB hwB t)
    (S.limit.norm_density_le (norm_planarBoxSource_le hB hwB) t)
    (S.density_L1_tendsto hw t) hx
  have he : Tendsto (fun n => (S.system (S.indices n)).velocity t (x n) -
      planarKernelVelocity kernelK ((S.system (S.indices n)).vorticity t) (x n))
      atTop (𝓝 (0 : R2)) :=
    squeeze_zero_norm (fun n => S.error (S.indices n) t t.property (x n)) S.smoothing_error_tendsto
  simpa only [sub_add_cancel, zero_add] using he.add hb

end PlanarRegularizedFlowLimit

end Euler2D

end
