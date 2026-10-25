module

public import RequestProject.Euler.ContourLogCutoffDerivative
public import RequestProject.Euler.ContourLogTruncation

/-! Actual joint continuity away from the pole and genuine integration
by parts on the two cutoff components. -/

@[expose] public section

noncomputable section

open Complex Set Filter Topology MeasureTheory

namespace Euler2D

lemma contourChord_ne_zero_on_cutoff {z : ℝ → ℂ} {c δ θ τ : ℝ}
    (hc : 0 < c) (hδ : 0 < δ)
    (hchord : ∀ θ τ : ℝ, |τ| ≤ Real.pi → c * |τ| ≤ ‖z θ - z (θ + τ)‖)
    (hτ : τ ∈ symmetricContourTruncation Real.pi δ) :
    z θ - z (θ + τ) ≠ 0 :=
  norm_pos_iff.mp ((mul_pos hc (hδ.trans_le hτ.2)).trans_le
    (hchord θ τ (abs_le.mpr hτ.1)))

theorem continuousOn_logChord_cutoff {z : ℝ → ℂ} {c δ : ℝ}
    (hz : Continuous z) (hc : 0 < c) (hδ : 0 < δ)
    (hchord : ∀ θ τ : ℝ, |τ| ≤ Real.pi → c * |τ| ≤ ‖z θ - z (θ + τ)‖) :
    ContinuousOn (fun p : ℝ × ℝ => Real.log ‖z p.1 - z (p.1 + p.2)‖)
      (univ ×ˢ symmetricContourTruncation Real.pi δ) := by
  have hden : Continuous (fun p : ℝ × ℝ => z p.1 - z (p.1 + p.2)) :=
    (hz.comp continuous_fst).sub (hz.comp (continuous_fst.add continuous_snd))
  exact hden.norm.continuousOn.log (fun p hp =>
    norm_ne_zero_iff.mpr (contourChord_ne_zero_on_cutoff hc hδ hchord hp.2))

theorem continuousOn_contourSelfIntegrand_cutoff {z dz : ℝ → ℂ} {c δ : ℝ}
    (hz : Continuous z) (hdz : Continuous dz) (hc : 0 < c) (hδ : 0 < δ)
    (hchord : ∀ θ τ : ℝ, |τ| ≤ Real.pi → c * |τ| ≤ ‖z θ - z (θ + τ)‖) :
    ContinuousOn (fun p : ℝ × ℝ => contourSelfIntegrand z dz p.1 p.2)
      (univ ×ˢ symmetricContourTruncation Real.pi δ) :=
  (continuousOn_logChord_cutoff hz hc hδ hchord).smul
    (hdz.comp (continuous_fst.add continuous_snd)).continuousOn

theorem continuousOn_contourSelfThetaDeriv_cutoff {z dz ddz : ℝ → ℂ} {c δ : ℝ}
    (hz : Continuous z) (hdz : Continuous dz) (hddz : Continuous ddz)
    (hc : 0 < c) (hδ : 0 < δ)
    (hchord : ∀ θ τ : ℝ, |τ| ≤ Real.pi → c * |τ| ≤ ‖z θ - z (θ + τ)‖) :
    ContinuousOn (fun p : ℝ × ℝ => contourSelfThetaDeriv z dz ddz p.1 p.2)
      (univ ×ˢ symmetricContourTruncation Real.pi δ) := by
  have hquot : ContinuousOn (fun p : ℝ × ℝ =>
      (dz p.1 - dz (p.1 + p.2)) / (z p.1 - z (p.1 + p.2)))
      (univ ×ˢ symmetricContourTruncation Real.pi δ) :=
    ((hdz.comp continuous_fst).sub (hdz.comp (continuous_fst.add continuous_snd))).continuousOn.div
      ((hz.comp continuous_fst).sub (hz.comp (continuous_fst.add continuous_snd))).continuousOn
      (fun p hp => contourChord_ne_zero_on_cutoff hc hδ hchord hp.2)
  exact ((continuousOn_logChord_cutoff hz hc hδ hchord).smul
    (hddz.comp (continuous_fst.add continuous_snd)).continuousOn).add
      ((Complex.continuous_re.comp_continuousOn hquot).smul
        (hdz.comp (continuous_fst.add continuous_snd)).continuousOn)

theorem continuousOn_contourSelfTauDeriv_cutoff {z dz ddz : ℝ → ℂ} {c δ : ℝ}
    (hz : Continuous z) (hdz : Continuous dz) (hddz : Continuous ddz)
    (hc : 0 < c) (hδ : 0 < δ)
    (hchord : ∀ θ τ : ℝ, |τ| ≤ Real.pi → c * |τ| ≤ ‖z θ - z (θ + τ)‖) :
    ContinuousOn (fun p : ℝ × ℝ => contourSelfTauDeriv z dz ddz p.1 p.2)
      (univ ×ˢ symmetricContourTruncation Real.pi δ) := by
  have hquot : ContinuousOn (fun p : ℝ × ℝ =>
      -dz (p.1 + p.2) / (z p.1 - z (p.1 + p.2)))
      (univ ×ˢ symmetricContourTruncation Real.pi δ) :=
    (hdz.comp (continuous_fst.add continuous_snd)).neg.continuousOn.div
      ((hz.comp continuous_fst).sub (hz.comp (continuous_fst.add continuous_snd))).continuousOn
      (fun p hp => contourChord_ne_zero_on_cutoff hc hδ hchord hp.2)
  exact ((continuousOn_logChord_cutoff hz hc hδ hchord).smul
    (hddz.comp (continuous_fst.add continuous_snd)).continuousOn).add
      ((Complex.continuous_re.comp_continuousOn hquot).smul
        (hdz.comp (continuous_fst.add continuous_snd)).continuousOn)

theorem integral_contourSelfTauDeriv {z dz ddz : ℝ → ℂ} {c δ θ : ℝ}
    (hzc : Continuous z) (hdzc : Continuous dz) (hddzc : Continuous ddz)
    (hc : 0 < c) (hδ : 0 < δ) (hδπ : δ ≤ Real.pi)
    (hz : ∀ s, HasDerivAt z (dz s) s) (hdz : ∀ s, HasDerivAt dz (ddz s) s)
    (hchord : ∀ θ τ : ℝ, |τ| ≤ Real.pi → c * |τ| ≤ ‖z θ - z (θ + τ)‖)
    (hzper : Function.Periodic z (2 * Real.pi)) (hdzper : Function.Periodic dz (2 * Real.pi)) :
    (∫ τ in symmetricContourTruncation Real.pi δ, contourSelfTauDeriv z dz ddz θ τ) =
      contourSelfIntegrand z dz θ (-δ) - contourSelfIntegrand z dz θ δ := by
  have hG := continuousOn_contourSelfTauDeriv_cutoff hzc hdzc hddzc hc hδ hchord
  have hpair : Continuous (fun τ : ℝ => (θ, τ)) := continuous_const.prodMk continuous_id
  have hmap : MapsTo (fun τ : ℝ => (θ, τ))
      (symmetricContourTruncation Real.pi δ) (univ ×ˢ symmetricContourTruncation Real.pi δ) :=
    fun τ hτ => ⟨mem_univ θ, hτ⟩
  have hcomp := ContinuousOn.comp
    (g := fun p : ℝ × ℝ => contourSelfTauDeriv z dz ddz p.1 p.2)
    (f := fun τ : ℝ => (θ, τ)) hG hpair.continuousOn hmap
  have hGc : ContinuousOn (contourSelfTauDeriv z dz ddz θ)
      (symmetricContourTruncation Real.pi δ) :=
    hcomp.congr (fun τ _ => rfl)
  have hi : IntegrableOn (contourSelfTauDeriv z dz ddz θ)
      (symmetricContourTruncation Real.pi δ) :=
    hGc.integrableOn_compact (isCompact_symmetricContourTruncation Real.pi δ)
  have hFTC := integral_symmetricContourTruncation_of_hasDerivAt
    (F := contourSelfIntegrand z dz θ) (g := contourSelfTauDeriv z dz ddz θ) hδ hδπ hi
    (fun τ hτ => hasDerivAt_contourSelfIntegrand_tau hz hdz
      (contourChord_ne_zero_on_cutoff hc hδ hchord hτ))
  have he : θ + -Real.pi + 2 * Real.pi = θ + Real.pi := by ring
  have hzends := hzper (θ + -Real.pi)
  have hdzends := hdzper (θ + -Real.pi)
  rw [he] at hzends hdzends
  have hends : contourSelfIntegrand z dz θ Real.pi = contourSelfIntegrand z dz θ (-Real.pi) := by
    unfold contourSelfIntegrand contourLogIntegrand
    rw [hzends, hdzends]
  rw [hFTC, hends]
  abel

end Euler2D

end
