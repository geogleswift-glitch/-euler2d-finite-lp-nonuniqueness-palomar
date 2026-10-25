module

public import RequestProject.Euler.TorusParticleMaterialVelocity
public import RequestProject.Euler.TorusPhysicalLabelCommonField

/-! Splitting the actual Euler material velocity into active labels and
the same transported inner labels. No identification of the inner labels
with near-circular contours is required. -/

@[expose] public section

set_option maxHeartbeats 3000000

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace Euler2D
namespace BoundedEulerParticleSystem

variable {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)

theorem periodicLocalMaterialVelocity_eq_transportedScalar
    {w : R2 → ℝ} {B : ℝ} (hw : Integrable w μT) (hwper : IsTorusPeriodic w)
    (hB : ∀ᵐ b ∂μT, ‖w b‖ ≤ B) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (x : R2) :
    periodicLocalMaterialVelocity w (S.forward t) x =
      ∫ y in torusBox, S.transportedScalar w t y •
        periodicLocalKernel ((x + torusCenter) - y) := by
  let A : R2 → R2 := fun y => S.transportedScalar w t y •
    periodicLocalKernel ((x + torusCenter) - y)
  have hk : Integrable (fun y => periodicLocalKernel ((x + torusCenter) - y)) μT :=
    (torusAreaPreserving_sub_left (x + torusCenter)).integrable_comp
      integrable_periodicLocalKernel isTorusPeriodic_periodicLocalKernel
  have hi : Integrable A μT := hk.bdd_smul B
    (S.aestronglyMeasurable_transportedScalar hw.aestronglyMeasurable t)
    (S.norm_transportedScalar_ae_le hB t)
  have hp : IsTorusPeriodic A := by
    intro y i
    dsimp only [A]
    rw [S.isTorusPeriodic_transportedScalar w t y i]
    exact congrArg (fun z : R2 => S.transportedScalar w t y • z)
      ((isTorusPeriodic_comp_sub_left isTorusPeriodic_periodicLocalKernel
        (x + torusCenter)) y i)
  have he := (S.forward_area t ht).integral_comp hi.aestronglyMeasurable hp
  calc
    _ = ∫ b in torusBox, A (S.forward t b) := by
      apply integral_congr_ae
      exact ae_of_all _ fun b => by
        dsimp only [A]
        rw [S.transportedScalar_eq_of_periodic hwper, S.backward_forward t ht b]
    _ = _ := he

theorem periodicLocalMaterialVelocity_eq_physicalLabelVelocity
    {w : R2 → ℝ} {B : ℝ} (hw : Integrable w μT) (hwper : IsTorusPeriodic w)
    (hB : ∀ᵐ b ∂μT, ‖w b‖ ≤ B) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (x : R2)
    (hsmall : ∀ᵐ y ∂μT, S.transportedScalar w t y ≠ 0 → ‖x - y‖ ≤ 1 / 2) :
    periodicLocalMaterialVelocity w (S.forward t) x =
      planarKernelVelocity kernelK (torusBox.indicator (S.transportedScalar w t)) x := by
  rw [S.periodicLocalMaterialVelocity_eq_transportedScalar hw hwper hB ht x]
  have he : (fun y => torusBox.indicator (S.transportedScalar w t) y • kernelK (x - y)) =
      torusBox.indicator (fun y => S.transportedScalar w t y • kernelK (x - y)) := by
    funext y
    by_cases hy : y ∈ torusBox <;> simp [hy]
  rw [planarKernelVelocity, he, integral_indicator measurableSet_torusBox]
  apply integral_congr_ae
  filter_upwards [hsmall] with y hy
  by_cases hz : S.transportedScalar w t y = 0
  · simp only [hz, zero_smul]
  · have harg : (x + torusCenter) - y - torusCenter = x - y := by abel
    rw [periodicLocalKernel_eq_kernelK_near (by rw [harg]; exact hy hz), harg]

theorem particleVelocityRepresentative_eq_partialMaterial_add_commonField
    {v w : R2 → ℝ} {Bv Bw : ℝ}
    (hv : Integrable v μT) (hw : Integrable w μT)
    (hvper : IsTorusPeriodic v) (hwper : IsTorusPeriodic w)
    (hvf : (fun b => v b + w b) =ᵐ[μT] (f : R2 → ℝ))
    (hBv : ∀ᵐ b ∂μT, ‖v b‖ ≤ Bv) (hBw : ∀ᵐ b ∂μT, ‖w b‖ ≤ Bw)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (x : R2)
    (hsmall : ∀ᵐ y ∂μT, S.transportedScalar w t y ≠ 0 → ‖x - y‖ ≤ 1 / 2) :
    particleVelocityRepresentative f S.backward S.backward_area t x =
      periodicLocalMaterialVelocity v (S.forward t) x + S.physicalLabelCommonField w t x := by
  have hper : IsTorusPeriodic (fun b => v b + w b) := by
    intro b i
    change v _ + w _ = v b + w b
    rw [hvper b i, hwper b i]
  have hB : ∀ᵐ b ∂μT, ‖v b + w b‖ ≤ Bv + Bw := by
    filter_upwards [hBv, hBw] with b hb hc
    exact (norm_add_le _ _).trans (add_le_add hb hc)
  have hsplit : periodicLocalMaterialVelocity (fun b => v b + w b) (S.forward t) x =
      periodicLocalMaterialVelocity v (S.forward t) x +
        periodicLocalMaterialVelocity w (S.forward t) x := by
    unfold periodicLocalMaterialVelocity
    simp_rw [add_smul]
    exact integral_add
      (integrable_periodicLocalMaterial_integrand hv hBv (S.forward_area t ht) x)
      (integrable_periodicLocalMaterial_integrand hw hBw (S.forward_area t ht) x)
  rw [S.particleVelocityRepresentative_eq_localMaterial_add_correction hvf hper hB ht x,
    hsplit, S.periodicLocalMaterialVelocity_eq_physicalLabelVelocity hw hwper hBw ht x hsmall]
  exact add_assoc _ _ _

theorem derivative_partialMaterial_add_commonField
    {v w : R2 → ℝ} {Bv Bw : ℝ}
    (hv : Integrable v μT) (hw : Integrable w μT)
    (hvper : IsTorusPeriodic v) (hwper : IsTorusPeriodic w)
    (hvf : (fun b => v b + w b) =ᵐ[μT] (f : R2 → ℝ))
    (hBv : ∀ᵐ b ∂μT, ‖v b‖ ≤ Bv) (hBw : ∀ᵐ b ∂μT, ‖w b‖ ≤ Bw)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (a : R2)
    (hsmall : ∀ᵐ y ∂μT, S.transportedScalar w t y ≠ 0 → ‖S.forward t a - y‖ ≤ 1 / 2) :
    HasDerivAt (fun s => S.forward s a)
      (periodicLocalMaterialVelocity v (S.forward t) (S.forward t a) +
        S.physicalLabelCommonField w t (S.forward t a)) t := by
  have hd := S.derivative t ht a
  rw [S.particleVelocityRepresentative_eq_partialMaterial_add_commonField
    hv hw hvper hwper hvf hBv hBw ht (S.forward t a) hsmall] at hd
  exact hd

end BoundedEulerParticleSystem
end Euler2D

end
