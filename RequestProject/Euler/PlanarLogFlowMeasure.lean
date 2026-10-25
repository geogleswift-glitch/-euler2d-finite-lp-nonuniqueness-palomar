module

public import RequestProject.Euler.PlanarLogParticleFlow
public import RequestProject.Euler.LogFlowApproximationLimit
public import RequestProject.Euler.MeasurePreservingPairLimit
public import RequestProject.Euler.SpatialC1ParticleFlow

/-! The actual planar logarithmic particle flow preserves genuine
infinite planar volume when its true smooth approximations are
divergence free. No periodicity is imposed on the plane. -/

@[expose] public section

set_option maxHeartbeats 2000000

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

theorem planarLogParticleFlow_measurePreserving_of_approximation
    {v : ℝ → R2 → R2}
    (vn : ℕ → ℝ → R2 → R2) (Kn : ℕ → ℝ≥0) (M C : ℝ≥0)
    (hvn : ∀ n, IsBoundedLipschitzVelocity (vn n) (Kn n) M)
    (hmod : ∀ n t x y, ‖x - y‖ ≤ 1 / 2 →
      ‖vn n t x - vn n t y‖ ≤ (C : ℝ) * logFlowModulus ‖x - y‖)
    (hconv : TendstoUniformly (fun n (p : ℝ × R2) => vn n p.1 p.2) (Function.uncurry v) atTop)
    (hC1 : ∀ n, IsC1SpatialVelocity (vn n))
    (hdiv : ∀ n t x, pd 0 (vn n t) x 0 + pd 1 (vn n t) x 1 = 0)
    {T : ℝ} (hT : 0 ≤ T) (S : PlanarLogParticleFlow v T)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    MeasurePreserving (S.forward t) volume volume ∧ MeasurePreserving (S.backward t) volume volume := by
  have hinit (n : ℕ) (a : R2) : boundedParticleForward (hvn n) hT 0 a = S.forward 0 a := by
    rw [boundedParticleForward_zero, S.initial]
  have hlim := tendstoUniformly_logFlow_of_velocity_approximation hT C.coe_nonneg
    (fun n => boundedParticleForward_continuous (hvn n) hT) S.continuous_forward
    (fun n q hq a => boundedParticleForward_hasDerivAt (hvn n) hT hq a) S.derivative hinit
    (fun n q _ x y hxy => hmod n q x y hxy) hconv
  have hfixed : TendstoUniformly (fun n => boundedParticleForward (hvn n) hT t) (S.forward t) atTop := by
    rw [Metric.tendstoUniformly_iff] at hlim ⊢
    intro ε hε
    filter_upwards [hlim ε hε] with n hn a
    exact hn (⟨t, ht⟩, a)
  have hback (a : R2) : Tendsto (fun n => boundedParticleBackward (hvn n) hT t a) atTop
      (𝓝 (S.backward t a)) :=
    tendsto_inverse_of_uniform_forward_limit
      (S.continuous_backward.comp (continuous_const.prodMk continuous_id)) (S.left_inv t ht)
      (fun n => boundedParticleForward_backward (hvn n) hT ht) hfixed a
  exact measurePreserving_inverse_pair_of_ae_tendsto
    (fun n => measurePreserving_boundedParticleForward_of_spatialC1 (hvn n) (hC1 n) hT (hdiv n) ht)
    (fun n => measurePreserving_boundedParticleBackward_of_spatialC1 (hvn n) (hC1 n) hT (hdiv n) ht)
    (S.continuous_forward.comp (continuous_const.prodMk continuous_id)).measurable
    (S.continuous_backward.comp (continuous_const.prodMk continuous_id)).measurable
    (Eventually.of_forall fun a => hfixed.tendsto_at a) (Eventually.of_forall hback)
    (S.left_inv t ht) (S.right_inv t ht)

theorem exists_measurePreserving_planarLogParticleFlow
    {v : ℝ → R2 → R2} (hv : Continuous (Function.uncurry v))
    (vn : ℕ → ℝ → R2 → R2) (Kn : ℕ → ℝ≥0) (M C : ℝ≥0)
    (hvn : ∀ n, IsBoundedLipschitzVelocity (vn n) (Kn n) M)
    (hmod : ∀ n t x y, ‖x - y‖ ≤ 1 / 2 →
      ‖vn n t x - vn n t y‖ ≤ (C : ℝ) * logFlowModulus ‖x - y‖)
    (hconv : TendstoUniformly (fun n (p : ℝ × R2) => vn n p.1 p.2) (Function.uncurry v) atTop)
    (hC1 : ∀ n, IsC1SpatialVelocity (vn n))
    (hdiv : ∀ n t x, pd 0 (vn n t) x 0 + pd 1 (vn n t) x 1 = 0)
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ S : PlanarLogParticleFlow v T, ∀ t ∈ Icc (0 : ℝ) T,
      MeasurePreserving (S.forward t) volume volume ∧ MeasurePreserving (S.backward t) volume volume := by
  obtain ⟨S⟩ := exists_planarLogParticleFlow_of_uniform_approximation hv vn Kn M C hvn hmod hconv hT
  exact ⟨S, fun t ht => planarLogParticleFlow_measurePreserving_of_approximation vn Kn M C
    hvn hmod hconv hC1 hdiv hT S ht⟩

end Euler2D

end
