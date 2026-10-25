module

public import RequestProject.Euler.TorusParticleCorrectionField
public import RequestProject.Euler.PeriodicLocalMaterialCoupling

/-! The original singular torus velocity in actual initial-label
coordinates, split into its genuine periodic local kernel and the
known Green correction of the same particle system. -/

@[expose] public section

set_option maxHeartbeats 3000000

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace Euler2D
namespace BoundedEulerParticleSystem

variable {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)

theorem particleVelocityRepresentative_eq_material {w : R2 → ℝ} {B : ℝ}
    (hwf : w =ᵐ[μT] (f : R2 → ℝ)) (hwper : IsTorusPeriodic w)
    (hB : ∀ᵐ b ∂μT, ‖w b‖ ≤ B) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (x : R2) :
    particleVelocityRepresentative f S.backward S.backward_area t x =
      ∫ b in torusBox, w b • torusBiotSavartKernel ((x + torusCenter) - S.forward t b) := by
  let v := S.transportedScalar w t
  let A : R2 → R2 := fun y => v y • torusBiotSavartKernel ((x + torusCenter) - y)
  have hw : AEStronglyMeasurable w μT := (Lp.aestronglyMeasurable f).congr hwf.symm
  have hi : Integrable A μT := by
    have hh := integrable_torusKernelVelocity_integrand
      (S.aestronglyMeasurable_transportedScalar hw t) (S.norm_transportedScalar_ae_le hB t) x
    convert hh using 1
    funext y
    dsimp only [A, v]
    rw [show (x + torusCenter) - y = x - y + torusCenter by abel]
  have hp : IsTorusPeriodic A := by
    intro y i
    dsimp only [A, v]
    rw [S.isTorusPeriodic_transportedScalar w t y i]
    exact congrArg (fun z : R2 => S.transportedScalar w t y • z)
      ((isTorusPeriodic_comp_sub_left isTorusPeriodic_torusBiotSavartKernel (x + torusCenter)) y i)
  have he := (S.forward_area t ht).integral_comp hi.aestronglyMeasurable hp
  calc
    _ = ∫ y in torusBox, A y := by
      rw [S.particleVelocityRepresentative_eq_raw w hwf]
      unfold torusKernelVelocity
      apply integral_congr_ae
      exact ae_of_all _ (fun y => by dsimp only [A, v]; congr 1 <;> abel)
    _ = ∫ b in torusBox, A (S.forward t b) := he.symm
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ (fun b => by
        dsimp only [A, v]
        rw [S.transportedScalar_eq_of_periodic hwper, S.backward_forward t ht b])

theorem particleVelocityRepresentative_eq_localMaterial_add_correction
    {w : R2 → ℝ} {B : ℝ}
    (hwf : w =ᵐ[μT] (f : R2 → ℝ)) (hwper : IsTorusPeriodic w)
    (hB : ∀ᵐ b ∂μT, ‖w b‖ ≤ B) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (x : R2) :
    particleVelocityRepresentative f S.backward S.backward_area t x =
      periodicLocalMaterialVelocity w (S.forward t) x + S.correctionLabelField t x := by
  have hw : Integrable w μT :=
    ((Lp.memLp f).integrable (by norm_num : (1 : ENNReal) ≤ 2)).congr hwf.symm
  have hi := integrable_periodicLocalMaterial_integrand hw hB (S.forward_area t ht) x
  have hs : Integrable (fun b => w b • torusSmoothCorrectionKernel
      ((x + torusCenter) - S.forward t b)) μT := by
    apply (S.integrable_correctionLabelField_integrand t x).congr
    filter_upwards [hwf] with b hb
    rw [hb]
    congr 1
    abel
  have hsEq : (∫ b in torusBox, w b • torusSmoothCorrectionKernel
      ((x + torusCenter) - S.forward t b)) = S.correctionLabelField t x := by
    apply integral_congr_ae
    filter_upwards [hwf] with b hb
    rw [hb]
    congr 1
    abel
  rw [S.particleVelocityRepresentative_eq_material hwf hwper hB ht x]
  change (∫ b in torusBox, w b • (periodicLocalKernel ((x + torusCenter) - S.forward t b) +
    torusSmoothCorrectionKernel ((x + torusCenter) - S.forward t b))) = _
  simp_rw [smul_add]
  rw [integral_add hi hs, hsEq]
  rfl

theorem derivative_localMaterial_add_correction
    {w : R2 → ℝ} {B : ℝ}
    (hwf : w =ᵐ[μT] (f : R2 → ℝ)) (hwper : IsTorusPeriodic w)
    (hB : ∀ᵐ b ∂μT, ‖w b‖ ≤ B) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (a : R2) :
    HasDerivAt (fun s => S.forward s a)
      (periodicLocalMaterialVelocity w (S.forward t) (S.forward t a) +
        S.correctionLabelField t (S.forward t a)) t := by
  have hd := S.derivative t ht a
  rw [S.particleVelocityRepresentative_eq_localMaterial_add_correction hwf hwper hB ht] at hd
  exact hd

end BoundedEulerParticleSystem
end Euler2D

end
