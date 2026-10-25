module

public import RequestProject.Euler.PlanarRegularizedParticleSystem
public import RequestProject.Euler.PlanarConvolutionWeakDivergence

/-! The actual source labels of the planar Picard system are
transported as a density on the whole plane. Genuine volume changes
give the true spatial convolution, all Lp norms, and the signed mass. -/

@[expose] public section

set_option maxHeartbeats 2000000

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace Euler2D

def planarBoxSource (w : R2 → ℝ) : R2 → ℝ := torusBox.indicator w

theorem integrable_planarBoxSource {w : R2 → ℝ} (hw : Integrable w μT) :
    Integrable (planarBoxSource w) volume :=
  (integrable_indicator_iff measurableSet_torusBox).mpr hw

namespace SmoothPlanarRegularizedParticleSystem

variable {K : R2 → R2} {w : R2 → ℝ} {T : ℝ} {L M : ℝ≥0}
  (S : SmoothPlanarRegularizedParticleSystem K w T L M)

def vorticity (t : ℝ) (x : R2) : ℝ := planarBoxSource w (S.particles.backward t x)

theorem vorticity_zero (hT : 0 ≤ T) : S.vorticity 0 = planarBoxSource w := by
  funext x
  have he := S.particles.left_inv 0 ⟨le_rfl, hT⟩ x
  rw [S.particles.initial] at he
  exact congrArg (planarBoxSource w) he

theorem velocity_eq_planarKernelVelocity {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (x : R2) :
    S.velocity t x = planarKernelVelocity K (S.vorticity t) x := by
  calc
    _ = ∫ b, w b • K (x - S.particles.forward t b) ∂μT := S.label_integral t ht x
    _ = ∫ b, planarBoxSource w b • K (x - S.particles.forward t b) := by
      change (∫ b in torusBox, w b • K (x - S.particles.forward t b)) = _
      rw [← integral_indicator measurableSet_torusBox]
      apply integral_congr_ae
      exact ae_of_all _ (fun b => by
        dsimp only
        by_cases hb : b ∈ torusBox <;> simp [planarBoxSource, hb])
    _ = _ := by
      have hc := (S.forward_area t ht).integral_comp
        (S.particles.homeomorph ⟨t, ht⟩).measurableEmbedding
        (fun y : R2 => planarBoxSource w (S.particles.backward t y) • K (x - y))
      change (∫ b, planarBoxSource w (S.particles.backward t (S.particles.forward t b)) •
        K (x - S.particles.forward t b)) = _ at hc
      simp_rw [S.particles.left_inv t ht] at hc
      exact hc

theorem eLpNorm_vorticity (hw : Integrable w μT) (p : ℝ≥0∞)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    eLpNorm (S.vorticity t) p volume = eLpNorm (planarBoxSource w) p volume :=
  eLpNorm_comp_measurePreserving (integrable_planarBoxSource hw).aestronglyMeasurable (S.backward_area t ht)

theorem memLp_vorticity {p : ℝ≥0∞} (hw : MemLp (planarBoxSource w) p volume)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) : MemLp (S.vorticity t) p volume :=
  hw.comp_measurePreserving (S.backward_area t ht)

theorem integral_vorticity {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    (∫ x, S.vorticity t x) = ∫ x, planarBoxSource w x :=
  (S.backward_area t ht).integral_comp (S.particles.homeomorph ⟨t, ht⟩).symm.measurableEmbedding _

theorem norm_vorticity_le {B : ℝ} (hB : 0 ≤ B) (hw : ∀ x ∈ torusBox, ‖w x‖ ≤ B)
    (t : ℝ) (x : R2) : ‖S.vorticity t x‖ ≤ B := by
  unfold vorticity planarBoxSource
  by_cases hx : S.particles.backward t x ∈ torusBox
  · rw [indicator_of_mem hx]
    exact hw _ hx
  · rw [indicator_of_notMem hx, norm_zero]
    exact hB

end SmoothPlanarRegularizedParticleSystem

end Euler2D

end
