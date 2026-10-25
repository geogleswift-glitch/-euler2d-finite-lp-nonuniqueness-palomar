module

public import RequestProject.Euler.BoundedEulerGeometry
public import RequestProject.Euler.DatumSeries

/-! Actual relative finite Euler particle maps in normalized planar
coordinates. Dilation changes both measures by the same factor;
conjugation retains exact global area and the same original particles. -/

@[expose] public section

set_option maxHeartbeats 5000000
set_option maxRecDepth 5000

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace Euler2D

def centeredDilationHomeomorph (r : ℝ) (hr : r ≠ 0) : R2 ≃ₜ R2 :=
  (Homeomorph.smul (Units.mk0 r hr)).trans (Homeomorph.addRight torusCenter)

@[simp] theorem centeredDilationHomeomorph_apply (r : ℝ) (hr : r ≠ 0) (a : R2) :
    centeredDilationHomeomorph r hr a = r • a + torusCenter := rfl

@[simp] theorem centeredDilationHomeomorph_symm_apply (r : ℝ) (hr : r ≠ 0) (a : R2) :
    (centeredDilationHomeomorph r hr).symm a = r⁻¹ • (a - torusCenter) := rfl

theorem measurePreserving_centeredDilationHomeomorph {r : ℝ} (hr : 0 < r) :
    MeasurePreserving (centeredDilationHomeomorph r hr.ne') volume
      (ENNReal.ofReal ((r⁻¹) ^ 2) • volume) := by
  have hscale : MeasurePreserving (fun x : R2 => r • x) volume
      (ENNReal.ofReal ((r⁻¹) ^ 2) • volume) := by
    refine ⟨by fun_prop, ?_⟩
    simpa only [inv_inv] using map_volume_inv_smul (inv_pos.mpr hr)
  change MeasurePreserving (fun x : R2 => r • x + torusCenter) _ _
  exact ((measurePreserving_add_right volume torusCenter).smul_measure
    (ENNReal.ofReal ((r⁻¹) ^ 2))).comp hscale

def normalizedPlanarHomeomorph (r : ℝ) (hr : r ≠ 0) (F : R2 ≃ₜ R2) : R2 ≃ₜ R2 :=
  (centeredDilationHomeomorph r hr).trans (F.trans (centeredDilationHomeomorph r hr).symm)

@[simp] theorem normalizedPlanarHomeomorph_apply (r : ℝ) (hr : r ≠ 0) (F : R2 ≃ₜ R2) (a : R2) :
    normalizedPlanarHomeomorph r hr F a = r⁻¹ • (F (r • a + torusCenter) - torusCenter) := rfl

theorem measurePreserving_normalizedPlanarHomeomorph {r : ℝ} (hr : 0 < r)
    (F : R2 ≃ₜ R2) (hF : MeasurePreserving F volume volume) :
    MeasurePreserving (normalizedPlanarHomeomorph r hr.ne' F) volume volume := by
  have hscale := measurePreserving_centeredDilationHomeomorph hr
  have hinv := MeasurePreserving.symm (centeredDilationHomeomorph r hr.ne').toMeasurableEquiv hscale
  exact hinv.comp ((hF.smul_measure (ENNReal.ofReal ((r⁻¹) ^ 2))).comp hscale)

namespace BoundedEulerParticleSystem

variable {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)

def normalizedRelativeHomeomorph (r : ℝ) (hr : r ≠ 0) (entrance : ℝ)
    (he : entrance ∈ Icc (0 : ℝ) T) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : R2 ≃ₜ R2 :=
  normalizedPlanarHomeomorph r hr ((S.homeomorph entrance he).symm.trans (S.homeomorph t ht))

@[simp] theorem normalizedRelativeHomeomorph_apply (r : ℝ) (hr : r ≠ 0) (entrance : ℝ)
    (he : entrance ∈ Icc (0 : ℝ) T) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (a : R2) :
    S.normalizedRelativeHomeomorph r hr entrance he t ht a =
      r⁻¹ • (S.forward t (S.backward entrance (r • a + torusCenter)) - torusCenter) := rfl

@[simp] theorem normalizedRelativeHomeomorph_entrance (r : ℝ) (hr : r ≠ 0) (entrance : ℝ)
    (he : entrance ∈ Icc (0 : ℝ) T) (a : R2) :
    S.normalizedRelativeHomeomorph r hr entrance he entrance he a = a := by
  rw [S.normalizedRelativeHomeomorph_apply, S.forward_backward entrance he,
    add_sub_cancel_right, inv_smul_smul₀ hr]

theorem measurePreserving_normalizedRelativeHomeomorph {r : ℝ} (hr : 0 < r)
    {entrance t : ℝ} (he : entrance ∈ Icc (0 : ℝ) T) (ht : t ∈ Icc (0 : ℝ) T)
    (hentry : MeasurePreserving (S.backward entrance) volume volume)
    (htarget : MeasurePreserving (S.forward t) volume volume) :
    MeasurePreserving (S.normalizedRelativeHomeomorph r hr.ne' entrance he t ht) volume volume :=
  measurePreserving_normalizedPlanarHomeomorph hr
    ((S.homeomorph entrance he).symm.trans (S.homeomorph t ht)) (htarget.comp hentry)

end BoundedEulerParticleSystem
end Euler2D

end
