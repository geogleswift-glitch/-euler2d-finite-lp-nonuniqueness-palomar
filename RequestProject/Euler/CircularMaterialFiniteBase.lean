module

public import RequestProject.Euler.CircularMaterialTransferProfile
public import RequestProject.Euler.FiniteTransportBounds

/-! The innermost finite datum is an actual ancient material cell.
Its full physical density supplies a genuine planar Lq element at every
geometric scale. The exact norm scaling instantiates the previously
conditional finite-datum convergence and uniform initial bounds. -/

@[expose] public section

set_option maxHeartbeats 2500000

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal

namespace Euler2D

theorem memLp_circularPhasePatchPlanarVorticity {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {Z : Fin 2 → LittleContourSpace γ}
    (hZ : Z ∈ circularQuarterPhaseDomain hγ hγ1) (p : ℝ≥0∞) :
    MemLp (circularPhasePatchPlanarVorticity Z) p volume := by
  let B := finiteContourPatchSupBound circularContourStrengths
  have hmajor : MemLp ((closedBall (0 : R2) (5 / 4)).indicator (fun _ => B)) p volume :=
    memLp_indicator_const p measurableSet_closedBall.nullMeasurableSet B
      (Or.inr (measure_closedBall_lt_top (μ := (volume : Measure R2))
        (x := (0 : R2)) (r := (5 / 4 : ℝ))).ne)
  apply hmajor.mono' (integrable_circularPhasePatchPlanarVorticity hγ hγ1 hZ).aestronglyMeasurable
  apply ae_of_all
  intro x
  by_cases hx : x ∈ closedBall (0 : R2) (5 / 4)
  · rw [indicator_of_mem hx]
    exact norm_circularPhasePatchPlanarVorticity_le hγ hγ1 hZ x
  · have hz : circularPhasePatchPlanarVorticity Z x = 0 := by
      by_contra hn
      exact hx (by simpa only [mem_closedBall, dist_zero_right] using
        norm_le_of_circularPhasePatchPlanarVorticity_ne_zero hγ hγ1 hZ hn)
    simp only [indicator_of_notMem hx, hz, norm_zero, le_refl]

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

def finiteBaseDensity (s A₀ b R ρ : ℝ) (N : ℕ) (x : R2) : ℝ :=
  ampScale A₀ b N * circularPhasePatchPlanarVorticity (P.ancient s) ((radScale R ρ N)⁻¹ • x)

theorem memLp_finiteBaseDensity {s A₀ b R ρ : ℝ} (hs : s ≤ 0)
    (hR : 0 < R) (hρ : 0 < ρ) (p : ℝ≥0∞) (N : ℕ) :
    MemLp (P.finiteBaseDensity s A₀ b R ρ N) p volume := by
  have hr : 0 < radScale R ρ N := mul_pos hR (pow_pos hρ N)
  let e : R2 ≃ᵐ R2 :=
    (Homeomorph.smul (Units.mk0 (radScale R ρ N)⁻¹ (inv_ne_zero hr.ne'))).toMeasurableEquiv
  have hm : MemLp (circularPhasePatchPlanarVorticity (P.ancient s)) p
      (Measure.map (fun x : R2 => (radScale R ρ N)⁻¹ • x) volume) := by
    rw [map_volume_inv_smul hr]
    exact (memLp_circularPhasePatchPlanarVorticity hγ hγ1 (P.ancient_domain s hs) p).smul_measure
      ENNReal.ofReal_ne_top
  exact (hm.comp_of_map e.measurable.aemeasurable).const_mul (ampScale A₀ b N)

def finiteBaseLp {s A₀ b R ρ q : ℝ} (hs : s ≤ 0)
    (hR : 0 < R) (hρ : 0 < ρ) (N : ℕ) : Lp ℝ (ENNReal.ofReal q) (volume : Measure R2) :=
  (P.memLp_finiteBaseDensity (A₀ := A₀) (b := b) hs hR hρ (ENNReal.ofReal q) N).toLp
    (P.finiteBaseDensity s A₀ b R ρ N)

theorem finiteBaseLp_ae {s A₀ b R ρ q : ℝ} (hs : s ≤ 0)
    (hR : 0 < R) (hρ : 0 < ρ) (N : ℕ) :
    (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ N : R2 → ℝ) =ᵐ[volume]
      P.finiteBaseDensity s A₀ b R ρ N :=
  MemLp.coeFn_toLp _

theorem integral_finiteBaseDensity_zero {s A₀ b R ρ : ℝ} (hs : s ≤ 0)
    (hR : 0 < R) (hρ : 0 < ρ) (N : ℕ) :
    (∫ x, P.finiteBaseDensity s A₀ b R ρ N x) = 0 := by
  have hr : 0 < radScale R ρ N := mul_pos hR (pow_pos hρ N)
  unfold finiteBaseDensity
  rw [integral_const_mul, Measure.integral_comp_inv_smul_of_nonneg volume
    (circularPhasePatchPlanarVorticity (P.ancient s)) hr.le,
    integral_circularPhasePatchPlanarVorticity_zero hγ hγ1
      (P.ancient_domain s hs) (P.ancient_area s hs)]
  simp

theorem norm_finiteBaseLp {s A₀ b R ρ q : ℝ} (hs : s ≤ 0)
    (hA : 0 ≤ A₀) (hb : 0 < b) (hR : 0 < R) (hρ : 0 < ρ) (hq : 0 < q) (N : ℕ) :
    ‖P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ N‖ =
      (eLpNorm (circularPhasePatchPlanarVorticity (P.ancient s)) (ENNReal.ofReal q) volume).toReal *
        (ampScale A₀ b N * radScale R ρ N ^ (2 / q)) := by
  have hAj : 0 ≤ ampScale A₀ b N := div_nonneg hA (pow_pos hb N).le
  have hr : 0 < radScale R ρ N := mul_pos hR (pow_pos hρ N)
  have he : eLpNorm (P.finiteBaseDensity s A₀ b R ρ N) (ENNReal.ofReal q) volume =
      ENNReal.ofReal (ampScale A₀ b N * radScale R ρ N ^ (2 / q)) *
        eLpNorm (circularPhasePatchPlanarVorticity (P.ancient s)) (ENNReal.ofReal q) volume := by
    change eLpNorm ((ampScale A₀ b N) • fun x =>
      circularPhasePatchPlanarVorticity (P.ancient s) ((radScale R ρ N)⁻¹ • x)) _ _ = _
    rw [eLpNorm_const_smul, eLpNorm_inv_smul hr hq, ← ofReal_norm_eq_enorm,
      Real.norm_of_nonneg hAj, ← mul_assoc, ← ENNReal.ofReal_mul hAj]
  rw [finiteBaseLp, Lp.norm_toLp, he, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (mul_nonneg hAj (Real.rpow_nonneg hr.le _))]
  ring

theorem tendsto_finiteBaseCurlL2 {s A₀ b R ρ q : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hs : s ≤ 0) (hA : 0 ≤ A₀) (hb : 0 < b) (hR : 0 < R) (hρ : 0 < ρ)
    (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q) (hsmall : ρ ^ (2 / q) < b) :
    Tendsto (finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
      (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ)) atTop
      (𝓝 (centeredPlaneToTorusL2 hqE (circularDatumLp (A₀ := A₀) (b := b) hR hρ hq))) := by
  apply Euler2D.tendsto_finiteBaseCurlL2 hA hb hR hρ hq hqE hsmall
  intro N
  exact (P.norm_finiteBaseLp hs hA hb hR hρ hq N).le

end CircularMaterialTransferProfile

end Euler2D

end
