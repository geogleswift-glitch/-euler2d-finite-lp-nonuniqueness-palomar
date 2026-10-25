module

public import RequestProject.Euler.TorusPhysicalSourceContinuity
public import RequestProject.Euler.ComplexPlanarBiotSavart
public import RequestProject.Euler.CoupledPlanarBiotSavartAffine

/-! The actual center translation identifies complex contour particles
with physical plane particles, preserving measure and the original
singular initial-label velocity. -/

@[expose] public section

set_option maxHeartbeats 2500000

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal

namespace Euler2D

def centeredComplexHomeomorph : ℂ ≃ₜ R2 :=
  complexPhysicalPlane.toHomeomorph.trans (Homeomorph.addRight torusCenter)

@[simp] theorem centeredComplexHomeomorph_apply (z : ℂ) :
    centeredComplexHomeomorph z = complexTorusPoint z := rfl

@[simp] theorem centeredComplexHomeomorph_symm_apply (x : R2) :
    centeredComplexHomeomorph.symm x = complexPhysicalPlane.symm (x - torusCenter) := rfl

theorem measurePreserving_centeredComplexHomeomorph :
    MeasurePreserving centeredComplexHomeomorph volume volume := measurePreserving_complexTorusPoint

def physicalComplexHomeomorph (F : ℂ ≃ₜ ℂ) : R2 ≃ₜ R2 :=
  centeredComplexHomeomorph.symm.trans (F.trans centeredComplexHomeomorph)

@[simp] theorem physicalComplexHomeomorph_apply (F : ℂ ≃ₜ ℂ) (x : R2) :
    physicalComplexHomeomorph F x = centeredComplexHomeomorph (F (centeredComplexHomeomorph.symm x)) := rfl

@[simp] theorem physicalComplexHomeomorph_symm_apply (F : ℂ ≃ₜ ℂ) (x : R2) :
    (physicalComplexHomeomorph F).symm x =
      centeredComplexHomeomorph (F.symm (centeredComplexHomeomorph.symm x)) := rfl

theorem measurePreserving_physicalComplexHomeomorph (F : ℂ ≃ₜ ℂ)
    (hF : MeasurePreserving F volume volume) :
    MeasurePreserving (physicalComplexHomeomorph F) volume volume :=
  measurePreserving_centeredComplexHomeomorph.comp (hF.comp
    (MeasurePreserving.symm centeredComplexHomeomorph.toMeasurableEquiv
      measurePreserving_centeredComplexHomeomorph))

theorem continuous_physicalComplexHomeomorph_flow {F : ℝ → ℂ ≃ₜ ℂ}
    (hF : Continuous (fun p : ℝ × ℂ => F p.1 p.2)) :
    Continuous (fun p : ℝ × R2 => physicalComplexHomeomorph (F p.1) p.2) :=
  centeredComplexHomeomorph.continuous.comp
    (hF.comp (continuous_fst.prodMk (centeredComplexHomeomorph.symm.continuous.comp continuous_snd)))

theorem hasDerivAt_complexTorusPoint_comp {Z : ℝ → ℂ} {z : ℂ} {t : ℝ}
    (hZ : HasDerivAt Z z t) :
    HasDerivAt (fun s => complexTorusPoint (Z s)) (complexPhysicalPlane z) t := by
  exact (complexPhysicalPlane.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hZ).add_const torusCenter

theorem complexTorus_velocityC_eq_spatial (w : ℂ → ℝ) (x : ℂ) :
    complexPhysicalPlane (velocityC w x) =
      planarKernelVelocity kernelK (fun y => w (centeredComplexHomeomorph.symm y)) (complexTorusPoint x) := by
  have he := complexPhysicalPlane_velocityC w (complexPhysicalPlane x)
  rw [LinearIsometryEquiv.symm_apply_apply] at he
  rw [he]
  unfold planarKernelVelocity
  calc
    _ = ∫ y, w (centeredComplexHomeomorph.symm (y + torusCenter)) •
        kernelK (complexTorusPoint x - (y + torusCenter)) := by
      apply integral_congr_ae
      exact ae_of_all _ fun y => by
        simp only [centeredComplexHomeomorph_symm_apply, add_sub_cancel_right,
          complexTorusPoint, add_sub_add_right_eq_sub]
    _ = _ := integral_add_right_eq_self (μ := volume)
      (fun y => w (centeredComplexHomeomorph.symm y) • kernelK (complexTorusPoint x - y)) torusCenter

theorem complexTorus_velocityC_eq_material
    (w w₀ : ℂ → ℝ) (F : ℂ ≃ₜ ℂ) (hF : MeasurePreserving F volume volume)
    (htransport : ∀ x, w x = w₀ (F.symm x)) (x : ℂ) :
    complexPhysicalPlane (velocityC w x) =
      planarMaterialLabelVelocity kernelK (fun y => w₀ (centeredComplexHomeomorph.symm y))
        (physicalComplexHomeomorph F) (complexTorusPoint x) := by
  rw [complexTorus_velocityC_eq_spatial,
    planarMaterialBiotSavart_eq_spatial _ _ (measurePreserving_physicalComplexHomeomorph F hF)]
  congr 1
  funext y
  rw [htransport, physicalComplexHomeomorph_symm_apply, Homeomorph.symm_apply_apply]

theorem hasDerivAt_physicalComplexHomeomorph_material
    {F : ℝ → ℂ ≃ₜ ℂ} {w w₀ : ℂ → ℝ} {E : R2 → R2} {t : ℝ}
    (hF : MeasurePreserving (F t) volume volume)
    (htransport : ∀ x, w x = w₀ ((F t).symm x))
    (hFd : ∀ z, HasDerivAt (fun s => F s z)
      (velocityC w (F t z) + planeComplexEquiv (E (complexTorusPoint (F t z)))) t)
    (a : R2) :
    HasDerivAt (fun s => physicalComplexHomeomorph (F s) a)
      (planarMaterialLabelVelocity kernelK (fun y => w₀ (centeredComplexHomeomorph.symm y))
        (physicalComplexHomeomorph (F t)) (physicalComplexHomeomorph (F t) a) +
        E (physicalComplexHomeomorph (F t) a)) t := by
  have hd := hasDerivAt_complexTorusPoint_comp (hFd (centeredComplexHomeomorph.symm a))
  rw [map_add, complexTorus_velocityC_eq_material w w₀ (F t) hF htransport] at hd
  have hp (y : R2) : complexPhysicalPlane (planeComplexEquiv y) = y := by
    rw [complexPhysicalPlane_eq_planeComplexEquiv_symm, MeasurableEquiv.symm_apply_apply]
  simp_rw [hp] at hd
  exact hd

end Euler2D

end
