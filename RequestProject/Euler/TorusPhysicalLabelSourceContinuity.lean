module

public import RequestProject.Euler.TorusPhysicalSourceContinuity
public import RequestProject.Euler.TorusTransportedLabelBounds

/-! Every genuine transported label uses the same actual Euler inverse
flow. Its physical L1 continuity does not require the label to equal the
full vorticity defining that flow. -/

@[expose] public section

set_option maxHeartbeats 2500000

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace Euler2D
namespace BoundedEulerParticleSystem

variable {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)

theorem particleCurlL2_label_ae_transportedScalar (g : Lp ℝ 2 μT) {w : R2 → ℝ}
    (hwg : w =ᵐ[μT] (g : R2 → ℝ)) (t : ℝ) :
    (particleCurlL2 g S.backward S.backward_area t : R2 → ℝ) =ᵐ[μT]
      S.transportedScalar w t :=
  S.torusTransportL2_ae_transportedScalar g hwg t

theorem integrable_physicalComplexLabelSource {w : R2 → ℝ}
    (hw : Integrable w μT) (t : ℝ) : Integrable (S.physicalComplexSource w t) :=
  integrable_boxedComplexDensity (S.integrable_transportedScalar_of_integrable hw t)

theorem integral_physicalComplexLabelSource {w : R2 → ℝ}
    (hw : Integrable w μT) (hwper : IsTorusPeriodic w) (t : ℝ) :
    (∫ z : ℂ, S.physicalComplexSource w t z) = ∫ x in torusBox, w x := by
  rw [physicalComplexSource, integral_boxedComplexDensity]
  simp_rw [S.transportedScalar_eq_of_periodic hwper]
  exact (S.backward_area t).integral_comp hw.aestronglyMeasurable hwper

theorem integral_abs_physicalComplexLabelSource {w : R2 → ℝ}
    (hw : Integrable w μT) (hwper : IsTorusPeriodic w) (t : ℝ) :
    (∫ z : ℂ, |S.physicalComplexSource w t z|) = ∫ x in torusBox, |w x| := by
  have he : (fun z : ℂ => |S.physicalComplexSource w t z|) =
      boxedComplexDensity (fun x => |S.transportedScalar w t x|) := by
    funext z
    dsimp only [physicalComplexSource, boxedComplexDensity]
    by_cases hz : complexTorusPoint z ∈ torusBox <;> simp [hz]
  rw [he, integral_boxedComplexDensity, S.integral_abs_transportedScalar hw hwper t]

theorem physicalComplexLabelSource_L1_sub_le (g : Lp ℝ 2 μT) {w : R2 → ℝ}
    (hwg : w =ᵐ[μT] (g : R2 → ℝ)) (t s : ℝ) :
    (∫ z : ℂ, |S.physicalComplexSource w t z - S.physicalComplexSource w s z|) ≤
      scalarL2L1Constant * ‖particleCurlL2 g S.backward S.backward_area t -
        particleCurlL2 g S.backward S.backward_area s‖ := by
  rw [physicalComplexSource, physicalComplexSource, integral_abs_boxedComplexDensity_sub]
  calc
    _ = ∫ x in torusBox, ‖(particleCurlL2 g S.backward S.backward_area t -
          particleCurlL2 g S.backward S.backward_area s) x‖ := by
      apply integral_congr_ae
      filter_upwards [S.particleCurlL2_label_ae_transportedScalar g hwg t,
        S.particleCurlL2_label_ae_transportedScalar g hwg s,
        Lp.coeFn_sub (particleCurlL2 g S.backward S.backward_area t)
          (particleCurlL2 g S.backward S.backward_area s)] with x ht hs he
      rw [he]
      change |S.transportedScalar w t x - S.transportedScalar w s x| =
        ‖particleCurlL2 g S.backward S.backward_area t x -
          particleCurlL2 g S.backward S.backward_area s x‖
      rw [ht, hs, Real.norm_eq_abs]
    _ ≤ _ := integral_norm_scalarL2_le _

theorem tendsto_physicalComplexLabelSource_L1 (g : Lp ℝ 2 μT) {w : R2 → ℝ}
    (hwg : w =ᵐ[μT] (g : R2 → ℝ))
    {α : Type*} {l : Filter α} {τ : α → ℝ} {s : ℝ} (hτ : Tendsto τ l (𝓝 s)) :
    Tendsto (fun t => ∫ z : ℂ, |S.physicalComplexSource w (τ t) z -
      S.physicalComplexSource w s z|) l (𝓝 0) := by
  have hc := ((continuous_particleCurlL2 g S.backward_area S.backward_continuous).tendsto s).comp hτ
  have hn := tendsto_iff_norm_sub_tendsto_zero.mp hc
  exact squeeze_zero (fun t => integral_nonneg (fun z => abs_nonneg _))
    (fun t => S.physicalComplexLabelSource_L1_sub_le g hwg (τ t) s)
    (by simpa only [mul_zero] using hn.const_mul scalarL2L1Constant)

theorem tendsto_physicalComplexSource_L1_of_memLp {w : R2 → ℝ}
    (hw : MemLp w 2 μT) {α : Type*} {l : Filter α} {τ : α → ℝ} {s : ℝ}
    (hτ : Tendsto τ l (𝓝 s)) :
    Tendsto (fun t => ∫ z : ℂ, |S.physicalComplexSource w (τ t) z -
      S.physicalComplexSource w s z|) l (𝓝 0) :=
  S.tendsto_physicalComplexLabelSource_L1 (hw.toLp w) hw.coeFn_toLp.symm hτ

end BoundedEulerParticleSystem
end Euler2D

end
