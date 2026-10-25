module

public import RequestProject.Euler.DatumCurlSeries
public import RequestProject.Euler.CircularFiniteInitialDensity

/-! The original infinite circular vorticity agrees with its root label
away from the actual inner scale. The statement concerns the original
Lebesgue-class series, so no pointwise representative is substituted. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 6000000

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal

namespace Euler2D

lemma datumTerm_eq_zero_of_radScale_le_norm {A₀ b R ρ : ℝ}
    (hR : 0 < R) (hρ : 0 < ρ) (j : ℕ) {x : R2}
    (hx : radScale R ρ j ≤ ‖x‖) : datumTerm A₀ b R ρ j x = 0 := by
  have hr : 0 < radScale R ρ j := mul_pos hR (pow_pos hρ j)
  have hnorm : 1 ≤ ‖(radScale R ρ j)⁻¹ • x‖ := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
    exact (le_inv_mul_iff₀ hr).mpr (by simpa only [mul_one] using hx)
  simp only [datumTerm, cellW_eq_zero_of_one_le_norm hnorm, mul_zero]

theorem circularDatumLp_eq_root_ae_off_inner_scale {A₀ b R ρ q : ℝ}
    [Fact (1 ≤ ENNReal.ofReal q)]
    (hA : 0 ≤ A₀) (hb : 0 < b) (hR : 0 < R) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hq : 0 < q) (hsmall : ρ ^ (2 / q) < b) :
    ∀ᵐ x ∂(volume : Measure R2), R * ρ < ‖x‖ →
      circularDatumLp (A₀ := A₀) (b := b) hR hρ hq x = datumTerm A₀ b R ρ 0 x := by
  let E : Set R2 := {x | R * ρ < ‖x‖}
  have hE : MeasurableSet E := measurableSet_lt measurable_const continuous_norm.measurable
  let F := LpToLpRestrictCLM R2 ℝ ℝ volume (ENNReal.ofReal q) E
  have htail (j : ℕ) (hj : j ≠ 0) :
      F (datumTermLp (A₀ := A₀) (b := b) hR hρ hq j) = 0 := by
    apply Lp.ext
    filter_upwards [LpToLpRestrictCLM_coeFn ℝ E
        (datumTermLp (A₀ := A₀) (b := b) hR hρ hq j),
      ae_restrict_of_ae (datumTerm_memLp (A₀ := A₀) (b := b) hR hρ hq j).coeFn_toLp,
      ae_restrict_mem hE, Lp.coeFn_zero ℝ (ENNReal.ofReal q) (volume.restrict E)]
      with x hre hterm hx hzero
    change datumTermLp (A₀ := A₀) (b := b) hR hρ hq j x = datumTerm A₀ b R ρ j x at hterm
    change (F (datumTermLp hR hρ hq j)) x = (0 : Lp ℝ (ENNReal.ofReal q) (volume.restrict E)) x
    rw [show (F (datumTermLp (A₀ := A₀) (b := b) hR hρ hq j)) x =
      datumTermLp (A₀ := A₀) (b := b) hR hρ hq j x from hre, hterm, hzero]
    apply datumTerm_eq_zero_of_radScale_le_norm hR hρ j
    have hpow : ρ ^ j ≤ ρ := by
      simpa only [pow_one] using pow_le_pow_of_le_one hρ.le hρ1 (Nat.one_le_iff_ne_zero.mpr hj)
    exact (mul_le_mul_of_nonneg_left hpow hR.le).trans (le_of_lt hx)
  have hsum := summable_datumTermLp hA hb hR hρ hq hsmall
  have heq : F (circularDatumLp (A₀ := A₀) (b := b) hR hρ hq) =
      F (datumTermLp (A₀ := A₀) (b := b) hR hρ hq 0) := by
    rw [circularDatumLp, F.map_tsum hsum]
    exact tsum_eq_single 0 htail
  have heqae :
      (circularDatumLp (A₀ := A₀) (b := b) hR hρ hq : R2 → ℝ) =ᵐ[volume.restrict E]
        datumTerm A₀ b R ρ 0 := by
    filter_upwards [LpToLpRestrictCLM_coeFn ℝ E
        (circularDatumLp (A₀ := A₀) (b := b) hR hρ hq),
      LpToLpRestrictCLM_coeFn ℝ E (datumTermLp (A₀ := A₀) (b := b) hR hρ hq 0),
      ae_restrict_of_ae (datumTerm_memLp (A₀ := A₀) (b := b) hR hρ hq 0).coeFn_toLp]
      with x hdatum hroot hterm
    change (F (circularDatumLp (A₀ := A₀) (b := b) hR hρ hq)) x = _ at hdatum
    rw [heq] at hdatum
    exact hdatum.symm.trans (hroot.trans hterm)
  exact (ae_restrict_iff' hE).mp heqae

theorem centeredCircularDatum_eq_root_ae_off_inner_scale {A₀ b R ρ q : ℝ}
    [Fact (1 ≤ ENNReal.ofReal q)]
    (hA : 0 ≤ A₀) (hb : 0 < b) (hR : 0 < R) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hq : 0 < q) (hsmall : ρ ^ (2 / q) < b) :
    ∀ᵐ x ∂μT, R * ρ < ‖x - torusCenter‖ →
      centeredCircularDatum (A₀ := A₀) (b := b) hR hρ hq x =
        datumTerm A₀ b R ρ 0 (x - torusCenter) := by
  exact ae_restrict_of_ae
    ((measurePreserving_sub_right volume torusCenter).quasiMeasurePreserving.ae
      (circularDatumLp_eq_root_ae_off_inner_scale hA hb hR hρ hρ1 hq hsmall))

end Euler2D

end
