module

public import RequestProject.Euler.ContourLogCutoffRegularity
public import RequestProject.Euler.ContourCompactDifferentiation

/-! Differentiation of the literal cutoff log self-interaction and its
integration-by-parts formula, before taking the cutoff to zero. -/

@[expose] public section

noncomputable section

open Complex Set Filter Topology MeasureTheory

namespace Euler2D

theorem hasDerivAt_contourSelfIntegralTruncated {z dz ddz : ℝ → ℂ} {c δ : ℝ}
    (hzc : Continuous z) (hdzc : Continuous dz) (hddzc : Continuous ddz)
    (hc : 0 < c) (hδ : 0 < δ)
    (hz : ∀ s, HasDerivAt z (dz s) s) (hdz : ∀ s, HasDerivAt dz (ddz s) s)
    (hchord : ∀ θ τ : ℝ, |τ| ≤ Real.pi → c * |τ| ≤ ‖z θ - z (θ + τ)‖) (θ : ℝ) :
    HasDerivAt (contourSelfIntegralTruncated z dz δ)
      (∫ τ in symmetricContourTruncation Real.pi δ, contourSelfThetaDeriv z dz ddz θ τ) θ :=
  hasDerivAt_setIntegral_of_continuousOn_compact
    (isCompact_symmetricContourTruncation Real.pi δ)
    (contourSelfIntegrand z dz) (contourSelfThetaDeriv z dz ddz)
    (continuousOn_contourSelfIntegrand_cutoff hzc hdzc hc hδ hchord)
    (continuousOn_contourSelfThetaDeriv_cutoff hzc hdzc hddzc hc hδ hchord)
    (fun θ τ hτ => hasDerivAt_contourSelfIntegrand_theta hz hdz
      (contourChord_ne_zero_on_cutoff hc hδ hchord hτ)) θ

theorem integral_contourSelfThetaDeriv_eq {z dz ddz : ℝ → ℂ} {c δ θ : ℝ}
    (hzc : Continuous z) (hdzc : Continuous dz) (hddzc : Continuous ddz)
    (hc : 0 < c) (hδ : 0 < δ) (hδπ : δ ≤ Real.pi)
    (hz : ∀ s, HasDerivAt z (dz s) s) (hdz : ∀ s, HasDerivAt dz (ddz s) s)
    (hchord : ∀ θ τ : ℝ, |τ| ≤ Real.pi → c * |τ| ≤ ‖z θ - z (θ + τ)‖)
    (hzper : Function.Periodic z (2 * Real.pi)) (hdzper : Function.Periodic dz (2 * Real.pi)) :
    (∫ τ in symmetricContourTruncation Real.pi δ, contourSelfThetaDeriv z dz ddz θ τ) =
      (∫ τ in symmetricContourTruncation Real.pi δ,
        (dz θ / (z θ - z (θ + τ))).re • dz (θ + τ)) +
          (contourSelfIntegrand z dz θ (-δ) - contourSelfIntegrand z dz θ δ) := by
  have hΘ := continuousOn_contourSelfThetaDeriv_cutoff hzc hdzc hddzc hc hδ hchord
  have hΤ := continuousOn_contourSelfTauDeriv_cutoff hzc hdzc hddzc hc hδ hchord
  have hpair : Continuous (fun τ : ℝ => (θ, τ)) := continuous_const.prodMk continuous_id
  have hmap : MapsTo (fun τ : ℝ => (θ, τ))
      (symmetricContourTruncation Real.pi δ) (univ ×ˢ symmetricContourTruncation Real.pi δ) :=
    fun τ hτ => ⟨mem_univ θ, hτ⟩
  have hΘcomp := ContinuousOn.comp
    (g := fun p : ℝ × ℝ => contourSelfThetaDeriv z dz ddz p.1 p.2)
    (f := fun τ : ℝ => (θ, τ)) hΘ hpair.continuousOn hmap
  have hΤcomp := ContinuousOn.comp
    (g := fun p : ℝ × ℝ => contourSelfTauDeriv z dz ddz p.1 p.2)
    (f := fun τ : ℝ => (θ, τ)) hΤ hpair.continuousOn hmap
  have hΘc : ContinuousOn (contourSelfThetaDeriv z dz ddz θ)
      (symmetricContourTruncation Real.pi δ) :=
    hΘcomp.congr (fun τ _ => rfl)
  have hΤc : ContinuousOn (contourSelfTauDeriv z dz ddz θ)
      (symmetricContourTruncation Real.pi δ) :=
    hΤcomp.congr (fun τ _ => rfl)
  have hΘi : IntegrableOn (contourSelfThetaDeriv z dz ddz θ)
      (symmetricContourTruncation Real.pi δ) :=
    hΘc.integrableOn_compact (isCompact_symmetricContourTruncation Real.pi δ)
  have hΤi : IntegrableOn (contourSelfTauDeriv z dz ddz θ)
      (symmetricContourTruncation Real.pi δ) :=
    hΤc.integrableOn_compact (isCompact_symmetricContourTruncation Real.pi δ)
  have heq : (fun τ => contourSelfThetaDeriv z dz ddz θ τ - contourSelfTauDeriv z dz ddz θ τ) =
      (fun τ => (dz θ / (z θ - z (θ + τ))).re • dz (θ + τ)) :=
    funext (contourSelfThetaDeriv_sub_tauDeriv z dz ddz θ)
  have he := integral_sub hΘi hΤi
  change (∫ τ in symmetricContourTruncation Real.pi δ,
    contourSelfThetaDeriv z dz ddz θ τ - contourSelfTauDeriv z dz ddz θ τ) = _ at he
  rw [heq, integral_contourSelfTauDeriv hzc hdzc hddzc hc hδ hδπ hz hdz hchord hzper hdzper] at he
  exact sub_eq_iff_eq_add.mp he.symm

theorem hasDerivAt_contourSelfIntegralTruncated_eq {z dz ddz : ℝ → ℂ} {c δ : ℝ}
    (hzc : Continuous z) (hdzc : Continuous dz) (hddzc : Continuous ddz)
    (hc : 0 < c) (hδ : 0 < δ) (hδπ : δ ≤ Real.pi)
    (hz : ∀ s, HasDerivAt z (dz s) s) (hdz : ∀ s, HasDerivAt dz (ddz s) s)
    (hchord : ∀ θ τ : ℝ, |τ| ≤ Real.pi → c * |τ| ≤ ‖z θ - z (θ + τ)‖)
    (hzper : Function.Periodic z (2 * Real.pi)) (hdzper : Function.Periodic dz (2 * Real.pi)) (θ : ℝ) :
    HasDerivAt (contourSelfIntegralTruncated z dz δ)
      ((∫ τ in symmetricContourTruncation Real.pi δ,
        (dz θ / (z θ - z (θ + τ))).re • dz (θ + τ)) +
          (contourSelfIntegrand z dz θ (-δ) - contourSelfIntegrand z dz θ δ)) θ := by
  have h := hasDerivAt_contourSelfIntegralTruncated hzc hdzc hddzc hc hδ hz hdz hchord θ
  rwa [integral_contourSelfThetaDeriv_eq hzc hdzc hddzc hc hδ hδπ hz hdz hchord hzper hdzper] at h

end Euler2D

end
