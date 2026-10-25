module

public import RequestProject.Euler.ContourSelfFirstVariation

/-! The first variation of the singular self integral, in the original
unregularized chord coordinates. The normalized proof supplies both
integrability and the almost-everywhere identity at the diagonal. -/

@[expose] public section

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) selfIntegralVariation_group (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) := Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)
local instance (priority := 2000) selfIntegralVariation_space (γ : ℝ≥0) :
    NormedSpace ℝ (ContourC1Space γ) := Submodule.normedSpace (contourC1GraphSubmodule γ)

set_option maxHeartbeats 800000 in
theorem fderiv_selfLogIntegral_fixed_apply {γ : ℝ≥0}
    (hγ : 0 < (γ : ℝ)) (θ : ℝ) (Z H : ContourC1Space γ)
    (hZ : ContourC1Space.HasPositiveChordArc Z) :
    fderiv ℝ (fun W : ContourC1Space γ => ContourC1Space.selfLogIntegral W θ) Z H =
      ∫ τ in Icc (-Real.pi) Real.pi,
        ((ContourC1Space.lift γ H θ - ContourC1Space.lift γ H (θ + τ)) /
          (ContourC1Space.lift γ Z θ - ContourC1Space.lift γ Z (θ + τ))).re •
            deriv (ContourC1Space.lift γ Z) (θ + τ) +
        Real.log ‖ContourC1Space.lift γ Z θ - ContourC1Space.lift γ Z (θ + τ)‖ •
          deriv (ContourC1Space.lift γ H) (θ + τ) := by
  let S : Set ℝ := Icc (-Real.pi) Real.pi
  let L := contourSelfLogLinearFamily hγ θ
  let N : ℝ → ℂ := fun τ => ((L τ H).1 / (L τ Z).1).re • (L τ Z).2 +
    Real.log ‖(L τ Z).1‖ • (L τ H).2
  obtain ⟨c, hc, hchord⟩ := hZ
  have hCZ : Continuous (fun τ : ℝ => L τ Z) :=
    (continuous_contourSelfLogLinearFamily hγ θ).clm_apply continuous_const
  have hCH : Continuous (fun τ : ℝ => L τ H) :=
    (continuous_contourSelfLogLinearFamily hγ θ).clm_apply continuous_const
  have hn (τ : ℝ) (hτ : τ ∈ S) : (L τ Z).1 ≠ 0 := by
    rw [contourSelfLogLinearFamily_coe hγ θ τ (abs_le.mpr hτ)]
    exact neg_ne_zero.mpr (smoothContourNormalizedChord_ne_zero
      (ContourC1Space.contDiff_lift Z) hc hchord θ τ (abs_le.mpr hτ))
  have hratio : ContinuousOn (fun τ : ℝ => ((L τ H).1 / (L τ Z).1).re) S :=
    Complex.continuous_re.comp_continuousOn (hCH.fst.continuousOn.div hCZ.fst.continuousOn hn)
  have hlog : ContinuousOn (fun τ : ℝ => Real.log ‖(L τ Z).1‖) S :=
    hCZ.fst.norm.continuousOn.log (fun τ hτ => norm_ne_zero_iff.mpr (hn τ hτ))
  have hiN : IntegrableOn N S := ContinuousOn.integrableOn_compact isCompact_Icc
    ((hratio.smul hCZ.snd.continuousOn).add (hlog.smul hCH.snd.continuousOn))
  have hab : (-Real.pi : ℝ) ≤ Real.pi := by linarith [Real.pi_pos]
  have hw : IntegrableOn Real.log S :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp intervalIntegral.intervalIntegrable_log'
  have hiw : IntegrableOn (fun τ => Real.log τ • (L τ H).2) S :=
    integrableOn_smul_continuousOn_compact isCompact_Icc hw hCH.snd.continuousOn
  calc
    fderiv ℝ (fun W : ContourC1Space γ => ContourC1Space.selfLogIntegral W θ) Z H =
        (∫ τ in S, Real.log τ • (L τ H).2) + ∫ τ in S, N τ := by
      rw [fderiv_selfLogIntegral_fixed_normalized hγ θ Z H ⟨c, hc, hchord⟩]
      apply congrArg₂ (fun a b : ℂ => a + b)
      · apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc] with τ hτ
        rw [contourSelfLogLinearFamily_coe hγ θ τ (abs_le.mpr hτ)]
      · apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc] with τ hτ
        dsimp only [N]
        rw [contourSelfLogLinearFamily_coe hγ θ τ (abs_le.mpr hτ),
          contourSelfLogLinearFamily_coe hγ θ τ (abs_le.mpr hτ)]
    _ = ∫ τ in S, Real.log τ • (L τ H).2 + N τ := (integral_add hiw hiN).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae (volume.ae_ne (0 : ℝ))]
        with τ hτ hτ0
      have hR : (L τ H).1 / (L τ Z).1 =
          (ContourC1Space.lift γ H θ - ContourC1Space.lift γ H (θ + τ)) /
            (ContourC1Space.lift γ Z θ - ContourC1Space.lift γ Z (θ + τ)) := by
        rw [contourSelfLogLinearFamily_coe hγ θ τ (abs_le.mpr hτ),
          contourSelfLogLinearFamily_coe hγ θ τ (abs_le.mpr hτ)]
        dsimp only
        rw [neg_div_neg_eq, smoothContourNormalizedChord_eq_div (ContourC1Space.contDiff_lift H) θ hτ0,
          smoothContourNormalizedChord_eq_div (ContourC1Space.contDiff_lift Z) θ hτ0,
          div_div_div_comm, div_self (Complex.ofReal_ne_zero.mpr hτ0), div_one]
        have hH : ContourC1Space.lift γ H (θ + τ) - ContourC1Space.lift γ H θ =
            -(ContourC1Space.lift γ H θ - ContourC1Space.lift γ H (θ + τ)) := by ring
        have hZ' : ContourC1Space.lift γ Z (θ + τ) - ContourC1Space.lift γ Z θ =
            -(ContourC1Space.lift γ Z θ - ContourC1Space.lift γ Z (θ + τ)) := by ring
        rw [hH, hZ', neg_div_neg_eq]
      have hl := contourLogIntegrand_eq_log_add_normalized (ContourC1Space.contDiff_lift Z)
        hc hchord θ τ (abs_le.mpr hτ) hτ0
      change Real.log ‖ContourC1Space.lift γ Z θ - ContourC1Space.lift γ Z (θ + τ)‖ = _ at hl
      dsimp only [N]
      rw [hR, contourSelfLogLinearFamily_coe hγ θ τ (abs_le.mpr hτ),
        contourSelfLogLinearFamily_coe hγ θ τ (abs_le.mpr hτ)]
      simp only [norm_neg]
      rw [hl, add_smul]
      abel

end Euler2D

end
