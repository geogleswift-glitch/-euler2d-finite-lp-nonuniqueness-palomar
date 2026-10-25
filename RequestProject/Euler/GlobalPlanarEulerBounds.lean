module

public import RequestProject.Euler.GlobalPlanarEulerExistence

/-! Exact density transport, all planar Lp norms, a uniform speed
bound and actual linear support propagation for the constructed
global singular-kernel particle flow. -/

@[expose] public section

set_option maxHeartbeats 2500000

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Euler2D
namespace GlobalPlanarEulerParticleSystem

variable {w : R2 → ℝ} (S : GlobalPlanarEulerParticleSystem w)

def vorticity (t : ℝ) (x : R2) : ℝ := w (S.backward t x)

def homeomorph (t : ℝ) (ht : 0 ≤ t) : R2 ≃ₜ R2 where
  toFun := S.forward t
  invFun := S.backward t
  left_inv := S.left_inv t ht
  right_inv := S.right_inv t ht
  continuous_toFun := S.continuous_forward.comp (continuous_const.prodMk continuous_id)
  continuous_invFun := S.continuous_backward.comp (continuous_const.prodMk continuous_id)

theorem vorticity_zero : S.vorticity 0 = w := by
  funext x
  have hi := S.left_inv 0 le_rfl x
  rw [S.initial] at hi
  exact congrArg w hi

theorem vorticity_forward (t : ℝ) (ht : 0 ≤ t) (a : R2) :
    S.vorticity t (S.forward t a) = w a := congrArg w (S.left_inv t ht a)

theorem integrable_vorticity (hw : Integrable w) (t : ℝ) : Integrable (S.vorticity t) :=
  (S.backward_area t).integrable_comp_of_integrable hw

theorem norm_vorticity_le {B : ℝ} (hB : ∀ x, ‖w x‖ ≤ B) (t : ℝ) (x : R2) :
    ‖S.vorticity t x‖ ≤ B := hB _

theorem integral_norm_vorticity (hw : Integrable w) (t : ℝ) :
    (∫ x, ‖S.vorticity t x‖) = ∫ x, ‖w x‖ := by
  have hm : AEStronglyMeasurable (fun x => ‖w x‖) (volume.map (S.backward t)) := by
    rw [(S.backward_area t).map_eq]
    exact hw.norm.aestronglyMeasurable
  have he := integral_map (S.backward_area t).aemeasurable hm
  rw [(S.backward_area t).map_eq] at he
  exact he.symm

theorem eLpNorm_vorticity (hw : Integrable w) (p : ℝ≥0∞) (t : ℝ) :
    eLpNorm (S.vorticity t) p volume = eLpNorm w p volume :=
  eLpNorm_comp_measurePreserving hw.aestronglyMeasurable (S.backward_area t)

theorem density_L1_time (hw : Integrable w) (t : ℝ) :
    Tendsto (fun s => ∫ x, ‖S.vorticity s x - S.vorticity t x‖) (𝓝 t) (𝓝 (0 : ℝ)) := by
  let g (s : ℝ) : C(R2, R2) :=
    ⟨S.backward s, S.continuous_backward.comp (continuous_const.prodMk continuous_id)⟩
  have hg : Continuous g := ContinuousMap.continuous_of_continuous_uncurry _ S.continuous_backward
  exact tendsto_integral_norm_planarTransport_time hw hg S.backward_area t

theorem norm_velocity_le {B : ℝ} (hw : Integrable w) (hB : ∀ x, ‖w x‖ ≤ B)
    (t : ℝ) (x : R2) : ‖S.velocity t x‖ ≤ planarBiotSavartMassBound B (∫ y, ‖w y‖) := by
  rw [S.selfconsistent]
  exact norm_planarBiotSavart_le_massBound (S.integrable_vorticity hw t)
    (S.norm_vorticity_le hB t) (S.integral_norm_vorticity hw t).le x

theorem norm_forward_sub_initial_le {V : ℝ} (hV : ∀ t x, ‖S.velocity t x‖ ≤ V)
    {t : ℝ} (ht : 0 ≤ t) (a : R2) : ‖S.forward t a - a‖ ≤ V * t := by
  have he := norm_trajectory_sub_time_le
    (fun s hs => S.derivative s hs.1 a) (fun s _ x => hV s x)
    (show (0 : ℝ) ∈ Icc (0 : ℝ) t from ⟨le_rfl, ht⟩)
    (show t ∈ Icc (0 : ℝ) t from ⟨ht, le_rfl⟩)
  simpa only [S.initial, sub_zero, abs_of_nonneg ht] using he

theorem norm_forward_le {V : ℝ} (hV : ∀ t x, ‖S.velocity t x‖ ≤ V)
    {t : ℝ} (ht : 0 ≤ t) (a : R2) : ‖S.forward t a‖ ≤ ‖a‖ + V * t := by
  calc
    _ ≤ ‖S.forward t a - a‖ + ‖a‖ := norm_le_norm_sub_add _ _
    _ ≤ V * t + ‖a‖ := add_le_add (S.norm_forward_sub_initial_le hV ht a) le_rfl
    _ = _ := add_comm _ _

theorem norm_le_of_vorticity_ne_zero {R V : ℝ}
    (hsource : ∀ a, w a ≠ 0 → ‖a‖ ≤ R) (hV : ∀ t x, ‖S.velocity t x‖ ≤ V)
    {t : ℝ} (ht : 0 ≤ t) {x : R2} (hx : S.vorticity t x ≠ 0) : ‖x‖ ≤ R + V * t := by
  have hb : ‖S.backward t x‖ ≤ R := hsource _ hx
  have hf := S.norm_forward_le hV ht (S.backward t x)
  rw [S.right_inv t ht x] at hf
  exact hf.trans (add_le_add hb le_rfl)

end GlobalPlanarEulerParticleSystem

end Euler2D

end
