module

public import RequestProject.Euler.CircularPhaseMaterialTransport
public import RequestProject.Euler.CircularMaterialTransferProfile

/-! Every actual finite window of the ancient material orbit has a
genuine area-preserving particle flow and exact physical density
transport. All ancient planar Lp norms equal the norms at time zero. -/

@[expose] public section

set_option maxHeartbeats 2500000

noncomputable section

open Complex Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace Euler2D

theorem exists_circularAncient_material_area_transport_window
    {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
    {Y : ℝ → Fin 2 → LittleContourSpace γ} (hYc : ContinuousOn Y (Iic (0 : ℝ)))
    (hYm : ∀ s ≤ 0, Y s ∈ circularQuarterPhaseDomain hγ hγ1)
    (hYd : ∀ s ≤ 0, HasDerivAt Y (circularBanachField hγ hγ1 (Y s)) s)
    {a b : ℝ} (hab : a ≤ b) (hb : b ≤ 0) :
    ∃ F : ℝ → ℂ ≃ₜ ℂ,
      Continuous (fun p : ℝ × ℂ => F p.1 p.2) ∧
      Continuous (fun p : ℝ × ℂ => (F p.1).symm p.2) ∧
      (∀ x, F 0 x = x) ∧
      (∀ t ∈ Icc (0 : ℝ) (b - a), ∀ x, HasDerivAt (fun s => F s x)
        (velocityC (circularPhasePatchVorticity (Y (t + a))) (F t x)) t) ∧
      (∀ t ∈ Icc (0 : ℝ) (b - a), MeasurePreserving (F t) volume volume ∧
        MeasurePreserving (F t).symm volume volume) ∧
      (∀ t ∈ Icc (0 : ℝ) (b - a), ∀ x, circularPhasePatchVorticity (Y (t + a)) x =
        circularPhasePatchVorticity (Y a) ((F t).symm x)) ∧
      ∀ (p : ℝ≥0∞) t, t ∈ Icc (0 : ℝ) (b - a) →
        eLpNorm (circularPhasePatchVorticity (Y (t + a))) p volume =
          eLpNorm (circularPhasePatchVorticity (Y a)) p volume := by
  let Z : ℝ → Fin 2 → LittleContourSpace γ := fun t => Y (t + a)
  have hsub {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (b - a)) : t + a ≤ 0 := by linarith [ht.2]
  have hZc : ContinuousOn Z (Icc (0 : ℝ) (b - a)) :=
    hYc.comp (continuous_id.add continuous_const).continuousOn (fun t ht => hsub ht)
  have hZm : ∀ t ∈ Icc (0 : ℝ) (b - a), Z t ∈ circularQuarterPhaseDomain hγ hγ1 :=
    fun t ht => hYm (t + a) (hsub ht)
  have hZd : ∀ t ∈ Icc (0 : ℝ) (b - a), HasDerivAt Z (circularBanachField hγ hγ1 (Z t)) t := by
    intro t ht
    exact (hYd (t + a) (hsub ht)).comp_add_const t a
  simpa only [Z, zero_add] using exists_circularPhase_material_area_transport hγ hγ1 Z
    (sub_nonneg.mpr hab) hZc hZm hZd

theorem circularAncientMaterial_eLpNorm_phasePatch
    {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
    {Y : ℝ → Fin 2 → LittleContourSpace γ} (hYc : ContinuousOn Y (Iic (0 : ℝ)))
    (hYm : ∀ s ≤ 0, Y s ∈ circularQuarterPhaseDomain hγ hγ1)
    (hYd : ∀ s ≤ 0, HasDerivAt Y (circularBanachField hγ hγ1 (Y s)) s)
    {t : ℝ} (ht : t ≤ 0) (p : ℝ≥0∞) :
    eLpNorm (circularPhasePatchVorticity (Y t)) p volume =
      eLpNorm (circularPhasePatchVorticity (Y 0)) p volume := by
  obtain ⟨F, hFc, hFic, hF0, hFd, hFarea, htransport, hnorm⟩ :=
    exists_circularAncient_material_area_transport_window hγ hγ1 hYc hYm hYd ht (le_refl (0 : ℝ))
  have he := hnorm p (0 - t) ⟨by linarith, le_rfl⟩
  simpa only [sub_add_cancel] using he.symm

end Euler2D

end
