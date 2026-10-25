module

public import RequestProject.Euler.PlanarEulerParticleBounds
public import RequestProject.Euler.PositivePlanarTransport

/-! The actual singular planar Euler solutions on expanding windows
have one common global forward/backward limit. Its transported
densities converge strongly in L1 at every nonnegative time. -/

@[expose] public section

set_option maxHeartbeats 3000000

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal

namespace Euler2D

structure ExpandingPlanarEulerLimit (w : R2 → ℝ) where
  system : ∀ n : ℕ, PlanarEulerParticleSystem w ((n : ℝ) + 1)
  V : ℝ
  C : ℝ
  speed_nonneg : 0 ≤ V
  modulus_nonneg : 0 ≤ C
  speed : ∀ (n : ℕ) t, t ∈ Icc (0 : ℝ) ((n : ℝ) + 1) → ∀ x, ‖(system n).velocity t x‖ ≤ V
  modulus : ∀ (n : ℕ) t, t ∈ Icc (0 : ℝ) ((n : ℝ) + 1) → ∀ x y, ‖x - y‖ ≤ 1 / 2 →
    ‖(system n).velocity t x - (system n).velocity t y‖ ≤ C * logFlowModulus ‖x - y‖
  limit : PositivePlanarTransportFlow w
  indices : ℕ → ℕ
  indices_strictMono : StrictMono indices
  converges : Tendsto (fun n => positivePlanarFlowPairMap ((system (indices n)).particles))
    atTop (𝓝 limit.maps)

theorem exists_expandingPlanarEulerLimit {w : R2 → ℝ} {B : ℝ}
    (hw : Integrable w μT) (hB : 0 ≤ B) (hwB : ∀ x ∈ torusBox, ‖w x‖ ≤ B) :
    Nonempty (ExpandingPlanarEulerLimit (planarBoxSource w)) := by
  obtain ⟨S, V, C, hV, hC, hspeed, hlog⟩ := exists_expanding_planarEulerParticleSystems hw hB hwB
  obtain ⟨H, φ, hφ, hlim⟩ := exists_compactOpen_expandingPlanarFlow_subseq hC hV
    (fun n => (S n).particles) hspeed hlog
  obtain ⟨hleft, hright, harea, hinit⟩ := positivePlanarFlow_limit_inverse_area
    (fun n => (S n).particles) (fun n => (S n).forward_area)
    (fun n t _ => (S n).backward_area t) hφ hlim
  exact ⟨{
    system := S
    V := V
    C := C
    speed_nonneg := hV
    modulus_nonneg := hC
    speed := hspeed
    modulus := hlog
    limit := ⟨H, hleft, hright, fun t => (harea t).1, fun t => (harea t).2, hinit⟩
    indices := φ
    indices_strictMono := hφ
    converges := hlim
  }⟩

namespace ExpandingPlanarEulerLimit

variable {w : R2 → ℝ} (S : ExpandingPlanarEulerLimit w)

theorem forward_tendsto (t : ℝ≥0) (a : R2) :
    Tendsto (fun n => (S.system (S.indices n)).particles.forward t a) atTop
      (𝓝 (positivePairForwardAt S.limit.maps t a)) :=
  (((continuous_eval_const (t, a)).tendsto S.limit.maps).comp S.converges).fst_nhds

theorem density_L1_tendsto (hw : Integrable w) (t : ℝ≥0) :
    Tendsto (fun n => ∫ x, ‖(S.system (S.indices n)).vorticity t x - S.limit.density t x‖)
      atTop (𝓝 (0 : ℝ)) := by
  have hg := ((continuous_positivePairBackwardAt_map t).tendsto S.limit.maps).comp S.converges
  exact tendsto_integral_norm_planarTransport_sub hw hg
    (fun n => (S.system (S.indices n)).backward_area t) (S.limit.backward_area t)

theorem velocity_tendsto_along_positions {B : ℝ}
    (hw : Integrable w) (hB : ∀ y, ‖w y‖ ≤ B)
    (t : ℝ≥0) {x : ℕ → R2} {x₀ : R2} (hx : Tendsto x atTop (𝓝 x₀)) :
    Tendsto (fun n => (S.system (S.indices n)).velocity t (x n)) atTop
      (𝓝 (S.limit.velocity t x₀)) := by
  simp_rw [PlanarEulerParticleSystem.velocity_eq]
  exact tendsto_planarBiotSavart_apply_of_L1
    (fun n => (S.system (S.indices n)).integrable_vorticity hw t)
    (S.limit.integrable_density hw t)
    (fun n => (S.system (S.indices n)).norm_vorticity_le hB t)
    (S.limit.norm_density_le hB t) (S.density_L1_tendsto hw t) hx

end ExpandingPlanarEulerLimit

end Euler2D

end
