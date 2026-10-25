module

public import RequestProject.Euler.RegularizedTorusParticleSystem
public import RequestProject.Euler.RegularizedKernelVelocityBounds
public import RequestProject.Euler.TorusTransportLimit

/-!
# Velocity convergence along actual inverse-particle limits

Strong transport convergence is derived for arbitrary bounded `L²` data.
The actual self-consistent regularized velocities then converge uniformly
in space, including along converging particle positions.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace Euler2D

lemma norm_torusTransportL2_ae_le (f : Lp ℝ 2 μT) {B : ℝ}
    (hB : ∀ᵐ a ∂μT, ‖f a‖ ≤ B) (Y : R2 → R2) (hY : TorusAreaPreserving Y) :
    ∀ᵐ a ∂μT, ‖torusTransportL2 f Y hY a‖ ≤ B := by
  filter_upwards [torusTransportL2_ae f Y hY, hY.quasiMeasurePreserving.ae hB] with a ha hb
  rw [ha]
  exact hb

lemma regularizedParticleVelocity_eq_transportAverage (f : Lp ℝ 2 μT)
    {ε T : ℝ} (hε : 0 < ε) {L M : ℝ≥0}
    (S : SmoothRegularizedParticleSystem (regularizedTorusKernel ε hε) f T L M)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (x : R2) :
    S.velocity t x = torusKernelAverage (torusTransportL2 f (S.backward t) (S.backward_area t))
      (regularizedTorusKernel ε hε) x := by
  rw [S.transported_integral t ht x]
  apply integral_congr_ae
  filter_upwards [torusTransportL2_ae f (S.backward t) (S.backward_area t)] with y hy
  rw [hy]

theorem tendstoUniformly_regularizedParticleVelocity (f : Lp ℝ 2 μT)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεlim : Tendsto ε atTop (𝓝 0))
    {T : ℝ} {L M : ℕ → ℝ≥0}
    (S : ∀ n, SmoothRegularizedParticleSystem (regularizedTorusKernel (ε n) (hε n)) f T (L n) (M n))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ᵐ a ∂μT, ‖f a‖ ≤ B)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) {Y : R2 → R2} (hY : TorusAreaPreserving Y)
    (hlim : ∀ᵐ a ∂μT, Tendsto (fun n => (S n).backward t a) atTop (𝓝 (Y a))) :
    TendstoUniformly (fun n => (S n).velocity t)
      (torusKernelVelocity (torusTransportL2 f Y hY)) atTop := by
  let W (n : ℕ) := torusTransportL2 f ((S n).backward t) ((S n).backward_area t)
  have hW : Tendsto W atTop (𝓝 (torusTransportL2 f Y hY)) :=
    tendsto_torusTransportL2_of_ae_tendsto f (fun n => (S n).backward_area t) hY hlim
  have hboundW (n : ℕ) : ∀ᵐ a ∂μT, ‖W n a‖ ≤ B :=
    norm_torusTransportL2_ae_le f hB _ _
  have hboundY : ∀ᵐ a ∂μT, ‖torusTransportL2 f Y hY a‖ ≤ B :=
    norm_torusTransportL2_ae_le f hB Y hY
  have he : (fun n => (S n).velocity t) =
      fun n => torusKernelAverage (W n) (regularizedTorusKernel (ε n) (hε n)) := by
    funext n x
    exact regularizedParticleVelocity_eq_transportAverage f (hε n) (S n) ht x
  rw [he]
  exact tendstoUniformly_regularizedTorusVelocity ε hε hεlim hW hB0 hboundW hboundY

theorem tendsto_regularizedParticleVelocity_along_positions (f : Lp ℝ 2 μT)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεlim : Tendsto ε atTop (𝓝 0))
    {T : ℝ} {L M : ℕ → ℝ≥0}
    (S : ∀ n, SmoothRegularizedParticleSystem (regularizedTorusKernel (ε n) (hε n)) f T (L n) (M n))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ᵐ a ∂μT, ‖f a‖ ≤ B)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) {Y : R2 → R2} (hY : TorusAreaPreserving Y)
    (hlim : ∀ᵐ a ∂μT, Tendsto (fun n => (S n).backward t a) atTop (𝓝 (Y a)))
    {a : ℕ → R2} {b : R2} (ha : Tendsto a atTop (𝓝 b)) :
    Tendsto (fun n => (S n).velocity t (a n)) atTop
      (𝓝 (torusKernelVelocity (torusTransportL2 f Y hY) b)) := by
  have hv := tendstoUniformly_regularizedParticleVelocity f ε hε hεlim S hB0 hB ht hY hlim
  have hc := continuous_torusKernelVelocity (Lp.aestronglyMeasurable (torusTransportL2 f Y hY))
    (norm_torusTransportL2_ae_le f hB Y hY)
  exact hv.tendsto_comp hc.continuousAt ha

end Euler2D

end
