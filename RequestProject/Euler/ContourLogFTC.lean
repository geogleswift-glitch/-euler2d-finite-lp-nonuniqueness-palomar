module

public import RequestProject.Euler.ContourLogRatioLimit
public import RequestProject.Euler.ContourReferenceCauchy

/-! Actual fundamental-theorem identities on the two components of a
positive symmetric cutoff. All derivatives and integrals are genuine. -/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter Topology Complex

namespace Euler2D

theorem symmetricContourTruncation_eq_union {r ε : ℝ} (hε : 0 < ε) :
    symmetricContourTruncation r ε = Icc (-r) (-ε) ∪ Icc ε r := by
  ext τ
  simp only [symmetricContourTruncation, mem_inter_iff, mem_Icc,
    mem_setOf_eq, mem_union, le_abs]
  constructor
  · rintro ⟨⟨h₁, h₂⟩, h₃ | h₃⟩
    · exact Or.inr ⟨h₃, h₂⟩
    · exact Or.inl ⟨h₁, by linarith⟩
  · rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
    · exact ⟨⟨h₁, by linarith⟩, Or.inr (by linarith)⟩
    · exact ⟨⟨by linarith, h₂⟩, Or.inl h₁⟩

theorem integral_symmetricContourTruncation_of_hasDerivAt {F g : ℝ → ℂ} {r ε : ℝ}
    (hε : 0 < ε) (hεr : ε ≤ r)
    (hg : IntegrableOn g (symmetricContourTruncation r ε))
    (hF : ∀ τ ∈ symmetricContourTruncation r ε, HasDerivAt F (g τ) τ) :
    (∫ τ in symmetricContourTruncation r ε, g τ) =
      F (-ε) - F (-r) + (F r - F ε) := by
  have hl : -r ≤ -ε := neg_le_neg hεr
  have hs := symmetricContourTruncation_eq_union (r := r) hε
  have h₁ : IntegrableOn g (Icc (-r) (-ε)) := hg.mono_set (by rw [hs]; exact subset_union_left)
  have h₂ : IntegrableOn g (Icc ε r) := hg.mono_set (by rw [hs]; exact subset_union_right)
  have hd : Disjoint (Icc (-r) (-ε)) (Icc ε r) := by
    apply disjoint_left.mpr
    intro τ hτ hτ'
    have := hτ.2
    have := hτ'.1
    linarith
  have hFTC₁ : (∫ τ in (-r)..(-ε), g τ) = F (-ε) - F (-r) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun τ hτ => hF τ (by rw [hs]; exact Or.inl (by simpa [uIcc_of_le hl] using hτ)))
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hl).mpr h₁)
  have hFTC₂ : (∫ τ in ε..r, g τ) = F r - F ε :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun τ hτ => hF τ (by rw [hs]; exact Or.inr (by simpa [uIcc_of_le hεr] using hτ)))
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hεr).mpr h₂)
  rw [hs, setIntegral_union hd measurableSet_Icc h₁ h₂,
    integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hl, ← intervalIntegral.integral_of_le hεr,
    hFTC₁, hFTC₂]

def contourCauchyKernelDifference (z : ℝ → ℂ) (r θ τ : ℝ) : ℂ :=
  deriv (refCircle r) (θ + τ) / (refCircle r θ - refCircle r (θ + τ)) -
    deriv z (θ + τ) / (z θ - z (θ + τ))

theorem hasDerivAt_nearCircleLog {z : ℝ → ℂ} {r ε θ τ : ℝ}
    (hr : 0 < r) (hε : 0 ≤ ε) (hsmall : ε < 2 * r / Real.pi)
    (hz : ContDiff ℝ 1 z) (hp : ContDiff ℝ 1 (fun t => z t - refCircle r t))
    (hd : ∀ t, ‖deriv (fun s => z s - refCircle r s) t‖ ≤ ε)
    (hτ : |τ| ≤ Real.pi) (hτ0 : τ ≠ 0) :
    HasDerivAt (fun t => Complex.log (contourChordRatio z r θ (θ + t)))
      (contourCauchyKernelDifference z r θ τ) τ := by
  have hangle : |θ - (θ + τ)| ≤ Real.pi := by
    simpa only [show θ - (θ + τ) = -τ by ring, abs_neg] using hτ
  have hne : θ ≠ θ + τ := by intro he; exact hτ0 (by linarith)
  have hgap : 0 < |θ - (θ + τ)| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hz0 : z θ - z (θ + τ) ≠ 0 := norm_pos_iff.mp
    ((mul_pos (sub_pos.mpr hsmall) hgap).trans_le
      (contour_lift_chordArc_lower z hr.le hε hp hd hangle))
  have hr0 : refCircle r θ - refCircle r (θ + τ) ≠ 0 := norm_pos_iff.mp
    ((mul_pos (by positivity : 0 < 2 * r / Real.pi) hgap).trans_le
      (refCircle_chord_lower hr.le hangle))
  have hh := hasDerivAt_log_contourChordRatio
    ((hz.differentiable one_ne_zero (θ + τ)).hasDerivAt) hz0 hr0
    (contourChordRatio_mem_slitPlane hr hε hsmall hp hd hangle hne)
  have ht : HasDerivAt (fun t : ℝ => θ + t) 1 τ := by
    simpa only [Pi.add_def, id_eq, zero_add] using
      ((hasDerivAt_const τ θ).add (hasDerivAt_id τ))
  have hcomp := hh.scomp τ ht
  simpa only [Function.comp_def, zero_add, one_smul, contourCauchyKernelDifference] using hcomp

end Euler2D

end
