module

public import RequestProject.Euler.PlanarFourthMomentBounds

/-! The actual global Euler fourth moment is continuous on all
nonnegative times and grows at most polynomially, by the proved
transport and linear support propagation of the same real flow. -/

@[expose] public section

set_option maxHeartbeats 2500000

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal

namespace Euler2D
namespace GlobalPlanarEulerParticleSystem

variable {w : R2 → ℝ} (S : GlobalPlanarEulerParticleSystem w)

theorem continuous_positive_fourthMoment {R V : ℝ} (hw : Integrable w)
    (hR : 0 ≤ R) (hV : 0 ≤ V) (hsource : ∀ x, w x ≠ 0 → ‖x‖ ≤ R)
    (hspeed : ∀ t x, ‖S.velocity t x‖ ≤ V) :
    Continuous (fun t : ℝ≥0 => planarFourthMoment (S.vorticity t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  let K : ℝ := (t : ℝ) + 1
  have htK : (t : ℝ) < K := by dsimp only [K]; linarith
  have hnear : ∀ᶠ s : ℝ≥0 in 𝓝 t, (s : ℝ) ≤ K :=
    NNReal.continuous_coe.continuousAt.eventually (eventually_le_nhds htK)
  have hsupport {s : ℝ≥0} (hs : (s : ℝ) ≤ K) {x : R2} (hx : S.vorticity s x ≠ 0) :
      ‖x‖ ≤ R + V * K :=
    (S.norm_le_of_vorticity_ne_zero hsource hspeed s.coe_nonneg hx).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left hs hV))
  have hevent : ∀ᶠ s : ℝ≥0 in 𝓝 t, ∀ x, S.vorticity s x ≠ 0 → ‖x‖ ≤ R + V * K := by
    filter_upwards [hnear] with s hs x hx
    exact hsupport hs hx
  have hL : Tendsto (fun s : ℝ≥0 => ∫ x, ‖S.vorticity s x - S.vorticity t x‖)
      (𝓝 t) (𝓝 (0 : ℝ)) := (S.density_L1_time hw t).comp NNReal.continuous_coe.continuousAt
  exact tendsto_planarFourthMoment_of_L1 (fun s => S.integrable_vorticity hw s)
    (S.integrable_vorticity hw t) hevent (fun x hx => hsupport htK.le hx) hL

theorem continuousOn_fourthMoment_nonneg {R V : ℝ} (hw : Integrable w)
    (hR : 0 ≤ R) (hV : 0 ≤ V) (hsource : ∀ x, w x ≠ 0 → ‖x‖ ≤ R)
    (hspeed : ∀ t x, ‖S.velocity t x‖ ≤ V) :
    ContinuousOn (fun t : ℝ => planarFourthMoment (S.vorticity t)) (Ici (0 : ℝ)) :=
  continuousOn_iff_continuous_restrict.mpr (S.continuous_positive_fourthMoment hw hR hV hsource hspeed)

theorem norm_fourthMoment_le {R V : ℝ} (hw : Integrable w)
    (hsource : ∀ x, w x ≠ 0 → ‖x‖ ≤ R) (hspeed : ∀ t x, ‖S.velocity t x‖ ≤ V)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖planarFourthMoment (S.vorticity t)‖ ≤ (∫ x, ‖w x‖) * (R + V * t) ^ 4 := by
  have he := norm_planarFourthMoment_le (S.integrable_vorticity hw t)
    (fun x hx => S.norm_le_of_vorticity_ne_zero hsource hspeed ht hx)
  rwa [S.integral_norm_vorticity hw t] at he

theorem fourthMoment_polynomial_bound {R V : ℝ} (hw : Integrable w)
    (hR : 0 ≤ R) (hV : 0 ≤ V) (hsource : ∀ x, w x ≠ 0 → ‖x‖ ≤ R)
    (hspeed : ∀ t x, ‖S.velocity t x‖ ≤ V) {t : ℝ} (ht : 0 ≤ t) :
    ‖planarFourthMoment (S.vorticity t)‖ ≤
      ((∫ x, ‖w x‖) * (R + V) ^ 4) * (1 + t) ^ 4 := by
  have hM : 0 ≤ ∫ x, ‖w x‖ := integral_nonneg (fun x => norm_nonneg _)
  have hb : R + V * t ≤ (R + V) * (1 + t) := by nlinarith [mul_nonneg hR ht]
  have hpow : (R + V * t) ^ 4 ≤ ((R + V) * (1 + t)) ^ 4 := by gcongr
  calc
    _ ≤ (∫ x, ‖w x‖) * (R + V * t) ^ 4 := S.norm_fourthMoment_le hw hsource hspeed ht
    _ ≤ (∫ x, ‖w x‖) * ((R + V) * (1 + t)) ^ 4 := mul_le_mul_of_nonneg_left hpow hM
    _ = _ := by rw [mul_pow]; ring

end GlobalPlanarEulerParticleSystem

end Euler2D

end
