module

public import RequestProject.Euler.CircularCanonicalCurrentCoordinates
public import RequestProject.Euler.CircularPhaseArea
public import RequestProject.Euler.BanachExistingReferenceStability

/-! A fixed observation window needs only an upper current bound,
not a nonzero growing seed. Small initial data and the true forcing
budget give an O(rho^6) bound on every already existing subinterval. -/

@[expose] public section

set_option maxHeartbeats 12000000
set_option maxRecDepth 6500

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

attribute [local instance 2000] rigidGaugeLittle_group rigidGaugeLittle_space rigidGaugeFamily_tower
attribute [local instance] LittleContourSpace.complexScalarNormedSpace LittleContourSpace.complexScalarTower
attribute [local irreducible] contourC1GraphSubmodule holderGraphSubmodule
  circularBanachField circularBanachDomain

theorem exists_circular_fixed_window_current_bound
    {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
    {D C₀ Lseed B Ktorus δcur : ℝ}
    (hD : 0 < D) (hC₀ : 1 ≤ C₀) (hLseed : 0 ≤ Lseed)
    (hB : 0 ≤ B) (hKtorus : 0 ≤ Ktorus) (hδcur : 0 ≤ δcur) :
    ∃ C > 0, ∀ᶠ ξ : ℝ in atTop,
      let ρ := Real.exp (-ξ)
      let h := C₀ * ρ ^ 6
      ∀ {R H : ℝ}, 0 < R → R ≤ ρ → 0 ≤ H → H ≤ D →
      ∀ y p : ℝ → Fin 2 → LittleContourSpace γ,
      (∀ t ∈ Icc (0 : ℝ) H,
        HasDerivAt y (circularBanachField hγ hγ1 (y t) + p t) t) →
      ‖y 0 - littleCircularReference hγ hγ1‖ ≤ Lseed * h →
      (∀ t ∈ Icc (0 : ℝ) H,
        ‖y t - littleCircularMaterialContours hγ hγ1 t‖ ≤ δcur) →
      (∀ t ∈ Icc (0 : ℝ) H,
        ‖p t‖ ≤ Ktorus * R ^ 8 * ‖y t - littleCircularMaterialContours hγ hγ1 t‖ +
          B * ρ ^ 6 * (1 + t) ^ 4) →
      ∀ t ∈ Icc (0 : ℝ) H,
        ‖y t - littleCircularMaterialContours hγ hγ1 t‖ ≤ C * h := by
  have hdom : IsOpen (circularBanachDomain hγ hγ1) := by
    unfold circularBanachDomain
    exact isOpen_phaseAdmissibleLittleContourFamilies _ _
  have hf : ContDiffOn ℝ 1 (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1) := by
    unfold circularBanachField circularBanachDomain
    exact contDiffOn_finiteContourPhaseFieldTotal hγ hγ1 _ _ _ _ _ 1
  obtain ⟨r, _hr, δ, hδ, εmax, hεmax, K, hstable⟩ :=
    exists_existing_compact_reference_stability_constants hdom hf hD
      (contDiff_littleCircularMaterialContours hγ hγ1).continuous.continuousOn
      (fun t _ => by
        simpa only [circularBanachField] using littleCircularMaterialContours_hasDerivAt hγ hγ1 t)
      (fun t _ => (littleCircularMaterialContours_mem_quarterPhaseDomain hγ hγ1 t).1)
  let Ce := Ktorus * δcur + B * (1 + D) ^ 4
  have hCe : 0 ≤ Ce := by dsimp only [Ce]; positivity
  let C := (Lseed + Ce * D) * Real.exp ((K : ℝ) * D) + 1
  have hC : 0 < C := by dsimp only [C]; positivity
  have he : Tendsto (fun ξ : ℝ => Real.exp (-ξ)) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero
  have hinitLim : Tendsto (fun ξ : ℝ => Lseed * (C₀ * Real.exp (-ξ) ^ 6)) atTop (𝓝 0) := by
    simpa only [zero_pow (by decide : (6 : ℕ) ≠ 0), mul_zero] using
      ((he.pow 6).const_mul C₀).const_mul Lseed
  have hforceLim : Tendsto (fun ξ : ℝ => Ce * Real.exp (-ξ) ^ 6) atTop (𝓝 0) := by
    simpa only [zero_pow (by decide : (6 : ℕ) ≠ 0), mul_zero] using (he.pow 6).const_mul Ce
  have hinitSmall : ∀ᶠ ξ : ℝ in atTop, Lseed * (C₀ * Real.exp (-ξ) ^ 6) ≤ δ :=
    (hinitLim.eventually (gt_mem_nhds hδ)).mono (fun _ h => h.le)
  have hforceSmall : ∀ᶠ ξ : ℝ in atTop, Ce * Real.exp (-ξ) ^ 6 ≤ εmax :=
    (hforceLim.eventually (gt_mem_nhds hεmax)).mono (fun _ h => h.le)
  have hone : ∀ᶠ ξ : ℝ in atTop, Real.exp (-ξ) ≤ 1 :=
    (he.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))).mono (fun _ h => h.le)
  refine ⟨C, hC, ?_⟩
  filter_upwards [hinitSmall, hforceSmall, hone] with ξ hinitSmall hforceSmall hρone
  let ρ := Real.exp (-ξ)
  let h := C₀ * ρ ^ 6
  dsimp only
  intro R H hR hRρ hH hHD y p hyd hinit hcur hp
  have hρ : 0 < ρ := Real.exp_pos (-ξ)
  have hC₀pos : 0 < C₀ := by linarith only [hC₀]
  have hh : 0 < h := mul_pos hC₀pos (pow_pos hρ 6)
  have hρ6h : ρ ^ 6 ≤ h := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hC₀ (pow_nonneg hρ.le 6)
  have hR8 : R ^ 8 ≤ ρ ^ 6 :=
    (pow_le_pow_left₀ hR.le hRρ 8).trans
      (pow_le_pow_of_le_one hρ.le hρone (by decide : (6 : ℕ) ≤ 8))
  have hforce (t : ℝ) (ht : t ∈ Icc (0 : ℝ) H) : ‖p t‖ ≤ Ce * ρ ^ 6 := by
    have htD : t ≤ D := ht.2.trans hHD
    have hpoly : (1 + t) ^ 4 ≤ (1 + D) ^ 4 :=
      pow_le_pow_left₀ (by linarith only [ht.1]) (add_le_add le_rfl htD) 4
    calc
      _ ≤ Ktorus * R ^ 8 * ‖y t - littleCircularMaterialContours hγ hγ1 t‖ +
          B * ρ ^ 6 * (1 + t) ^ 4 := hp t ht
      _ ≤ Ktorus * ρ ^ 6 * δcur + B * ρ ^ 6 * (1 + D) ^ 4 :=
        add_le_add
          (mul_le_mul (mul_le_mul_of_nonneg_left hR8 hKtorus) (hcur t ht) (norm_nonneg _)
            (mul_nonneg hKtorus (pow_nonneg hρ.le 6)))
          (mul_le_mul_of_nonneg_left hpoly (mul_nonneg hB (pow_nonneg hρ.le 6)))
      _ = Ce * ρ ^ 6 := by dsimp only [Ce]; ring
  have hyc : ContinuousOn y (Icc (0 : ℝ) H) :=
    fun t ht => (hyd t ht).continuousAt.continuousWithinAt
  have hinitDist : dist (y 0) (littleCircularMaterialContours hγ hγ1 0) ≤ δ := by
    rw [dist_eq_norm, littleCircularMaterialContours_zero]
    exact hinit.trans hinitSmall
  have hstable' := hstable hH hHD (mul_nonneg hCe (pow_nonneg hρ.le 6)) hforceSmall
    y p hyc hyd hforce hinitDist
  intro t ht
  have hn := hstable'.2 t ht
  simp only [dist_eq_norm, littleCircularMaterialContours_zero] at hn
  have htD : t ≤ D := ht.2.trans hHD
  have heps : Ce * ρ ^ 6 * t ≤ Ce * h * D :=
    mul_le_mul (mul_le_mul_of_nonneg_left hρ6h hCe) htD ht.1 (mul_nonneg hCe hh.le)
  have harg : ‖y 0 - littleCircularReference hγ hγ1‖ + Ce * ρ ^ 6 * t ≤ (Lseed + Ce * D) * h := by
    nlinarith only [hinit, heps]
  have hexp : Real.exp ((K : ℝ) * t) ≤ Real.exp ((K : ℝ) * D) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left htD K.coe_nonneg)
  calc
    _ ≤ (‖y 0 - littleCircularReference hγ hγ1‖ + Ce * ρ ^ 6 * t) *
        Real.exp ((K : ℝ) * t) := hn
    _ ≤ ((Lseed + Ce * D) * h) * Real.exp ((K : ℝ) * D) :=
      mul_le_mul harg hexp (Real.exp_pos _).le (by positivity)
    _ = ((Lseed + Ce * D) * Real.exp ((K : ℝ) * D)) * h := by ring
    _ ≤ C * h := mul_le_mul_of_nonneg_right (by dsimp only [C]; linarith) hh.le

end Euler2D

end
