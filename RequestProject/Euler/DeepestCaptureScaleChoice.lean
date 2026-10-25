module

public import RequestProject.Euler.CircularFiniteInnerStageConfinement
public import RequestProject.Euler.NormalEigen

/-! A single shrinking scale satisfies all spatial and forcing margins
of the deepest actual capture, after its original entrance and finite
block horizon have been fixed. -/

@[expose] public section

set_option maxHeartbeats 8000000
set_option maxRecDepth 6000

noncomputable section

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace Euler2D

abbrev deepestCaptureScale (ξ : ℝ) : ℝ := Real.exp (-ξ)

structure DeepestCaptureScaleData where
  b : ℝ
  L : ℝ
  core : ℝ
  rw : ℝ
  Kboot : ℝ
  δgeom : ℝ
  δcur : ℝ
  Cb : ℝ
  Cr : ℝ
  Kr : ℝ
  d : ℝ
  Cgeo : ℝ
  A₀ : ℝ
  T : ℝ
  torusW : ℝ
  torusC : ℝ
  Cl : ℝ
  C : ℝ
  E : ℝ
  lam : ℝ
  Damp : ℝ
  κ₀ : ℝ
  ε₀ : ℝ
  Bpoly : ℝ
  F : ℝ
  seed : ℝ
  referenceNorm : ℝ
  q : ℝ
  Ncap : ℕ
  blockTime : ℝ

namespace DeepestCaptureScaleData

def duration (p : DeepestCaptureScaleData) : ℝ := (p.Ncap : ℝ) * p.blockTime

structure Admissible (p : DeepestCaptureScaleData) : Prop where
  b_pos : 0 < p.b
  core_pos : 0 < p.core
  rw_pos : 0 < p.rw
  geom_pos : 0 < p.δgeom
  radial_pos : 0 < p.Cr
  d_pos : 0 < p.d
  kappa_pos : 0 < p.κ₀
  error_pos : 0 < p.ε₀
  seed_pos : 0 < p.seed
  drift_margin : 5 / 4 + p.Cgeo * p.A₀ * p.T < p.d
  capture_margin : 9 * p.C * p.Damp / (p.lam - 1) < 1 / 16

structure Budget (p : DeepestCaptureScaleData) (ξ : ℝ) : Prop where
  half : deepestCaptureScale ξ ≤ 1 / 2
  one : deepestCaptureScale ξ ≤ 1
  bhalf : deepestCaptureScale ξ ≤ p.b / 2
  sq_bhalf : deepestCaptureScale ξ ^ 2 ≤ p.b / 2
  initial_sep : deepestCaptureScale ξ ≤ cellA / 128
  initial_core : (5 / 4 : ℝ) * deepestCaptureScale ξ ≤ cellA
  upper_sep : 10 * deepestCaptureScale ξ ≤ cellA / 2
  lower_sep : 8 * p.L * deepestCaptureScale ξ ≤ p.core
  weight : 2 * deepestCaptureScale ξ ^ 6 ≤ 1
  weighted_bootstrap : (2 * deepestCaptureScale ξ ^ 6) * p.Kboot ≤ min p.rw p.δgeom
  row : 2 * deepestCaptureScale ξ ^ 8 ≤ 1 / 2
  torus : p.torusW * deepestCaptureScale ξ ^ 8 ≤ 1
  drift : 5 / 4 + (p.Cgeo * p.A₀ / (1 - deepestCaptureScale ξ / p.b)) * p.T < p.d
  radius : p.d * deepestCaptureScale ξ ≤ 1 / 16
  initial_chart : (5 / 4 : ℝ) * deepestCaptureScale ξ < 1 / 16
  geometry : (p.L + 1) * deepestCaptureScale ξ ≤ 1 / 32
  domain : deepestCaptureScale ξ * (p.referenceNorm + p.δgeom) < 1 / 64
  logarithmic : p.duration ≤ (6 / sigma) * ξ + p.duration
  outer_source : (2 * p.b * 2 * p.Kboot * (p.Cl + p.torusC)) * deepestCaptureScale ξ ^ 2 ≤ 1
  radial : p.b * finiteEulerUniformRadialCoefficient p.Kr p.b
      (deepestCaptureScale ξ) (deepestCaptureScale ξ) p.core p.d p.δcur * p.Cb ^ 3 *
      deepestCaptureScale ξ ^ 2 * (1 + p.duration) ^ 3 ≤ p.Cr / 2
  particle_core : p.Cb * deepestCaptureScale ξ * (1 + p.duration) ≤ p.core / 2
  particle_outer : p.Cb * deepestCaptureScale ξ * (1 + p.duration) ≤ p.d
  particle_box : p.Cb * deepestCaptureScale ξ * deepestCaptureScale ξ * (1 + p.duration) ≤ 1 / 16
  particle_sep : 8 * (p.Cb * deepestCaptureScale ξ * (1 + p.duration)) ≤ cellA / 2
  kappa : p.torusC * deepestCaptureScale ξ ^ 8 ≤ p.κ₀
  capture : 9 * p.C * p.Damp / (p.lam - 1) +
    3 * (p.E * (p.torusC * deepestCaptureScale ξ ^ 8)) * (p.Ncap : ℝ) ≤ 1 / 16
  forcing : p.Bpoly * deepestCaptureScale ξ ^ 6 * (1 + p.duration) ^ 4 +
    (p.torusC * deepestCaptureScale ξ ^ 8) * (3 * p.Damp) ≤ p.ε₀
  source : p.F * p.Bpoly * deepestCaptureScale ξ ^ 6 ≤ p.seed / 32
  lp_ratio : deepestCaptureScale ξ ^ 2 < p.b ^ p.q

private theorem eventually_le_of_tendsto_zero {f : ℝ → ℝ} {ε : ℝ}
    (hf : Tendsto f atTop (𝓝 0)) (hε : 0 < ε) : ∀ᶠ ξ : ℝ in atTop, f ξ ≤ ε :=
  (hf.eventually (eventually_lt_nhds hε)).mono (fun _ h => h.le)

theorem eventually_budget (p : DeepestCaptureScaleData) (h : p.Admissible) :
    ∀ᶠ ξ : ℝ in atTop, p.Budget ξ := by
  have he : Tendsto deepestCaptureScale atTop (𝓝 0) := Real.tendsto_exp_neg_atTop_nhds_zero
  have he2 : Tendsto (fun ξ : ℝ => deepestCaptureScale ξ ^ 2) atTop (𝓝 0) := by simpa using he.pow 2
  have he6 : Tendsto (fun ξ : ℝ => deepestCaptureScale ξ ^ 6) atTop (𝓝 0) := by simpa using he.pow 6
  have he8 : Tendsto (fun ξ : ℝ => deepestCaptureScale ξ ^ 8) atTop (𝓝 0) := by simpa using he.pow 8
  have hlin (A : ℝ) {ε : ℝ} (hε : 0 < ε) :
      ∀ᶠ ξ : ℝ in atTop, A * deepestCaptureScale ξ ≤ ε := by
    apply eventually_le_of_tendsto_zero _ hε
    simpa only [mul_zero] using he.const_mul A
  have hOne : Tendsto (fun _ξ : ℝ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hden : Tendsto (fun ξ : ℝ => 1 - deepestCaptureScale ξ / p.b) atTop (𝓝 1) := by
    simpa only [zero_div, sub_zero] using hOne.sub (he.div_const p.b)
  have hdrift : Tendsto (fun ξ : ℝ => 5 / 4 + (p.Cgeo * p.A₀ /
      (1 - deepestCaptureScale ξ / p.b)) * p.T) atTop (𝓝 (5 / 4 + p.Cgeo * p.A₀ * p.T)) := by
    have hnum : Tendsto (fun _ξ : ℝ => p.Cgeo * p.A₀) atTop (𝓝 (p.Cgeo * p.A₀)) := tendsto_const_nhds
    simpa only [div_one] using
      ((hnum.div hden (by norm_num : (1 : ℝ) ≠ 0)).mul_const p.T).const_add (5 / 4)
  have hmden : Tendsto (fun ξ : ℝ => 1 - deepestCaptureScale ξ ^ 2 / p.b) atTop (𝓝 1) := by
    simpa only [zero_div, sub_zero] using hOne.sub (he2.div_const p.b)
  let m₀ := (eLpNorm cellW 1 volume).toReal
  let M := finiteContourPatchMassBound circularContourStrengths circularContourRadii
  have hmass : Tendsto (fun ξ : ℝ => circularFiniteL1Coefficient p.b (deepestCaptureScale ξ))
      atTop (𝓝 (m₀ + M)) := by
    have hnum : Tendsto (fun _ξ : ℝ => m₀) atTop (𝓝 m₀) := tendsto_const_nhds
    simpa only [circularFiniteL1Coefficient, div_one] using
      (hnum.div hmden (by norm_num : (1 : ℝ) ≠ 0)).add_const M
  have hrden : Tendsto (fun ξ : ℝ => 1 - p.b * deepestCaptureScale ξ ^ 2) atTop (𝓝 1) := by
    simpa only [mul_zero, sub_zero] using hOne.sub (he2.const_mul p.b)
  let radialLimit := (32 / (15 * p.core ^ 4) * circularRadialPerturbationWeight) * p.δcur
  have hradial : Tendsto (fun ξ : ℝ => finiteEulerUniformRadialCoefficient p.Kr p.b
      (deepestCaptureScale ξ) (deepestCaptureScale ξ) p.core p.d p.δcur) atTop (𝓝 radialLimit) := by
    have hnum : Tendsto (fun _ξ : ℝ => radialLimit) atTop (𝓝 radialLimit) := tendsto_const_nhds
    have hfirst := hnum.div hrden (by norm_num : (1 : ℝ) ≠ 0)
    have hsecond := (hmass.const_mul (p.Kr * p.d ^ 4)).mul he8
    simpa only [finiteEulerUniformRadialCoefficient, div_one, mul_zero, add_zero] using hfirst.add hsecond
  have hcubic : Tendsto (fun ξ : ℝ => p.b * finiteEulerUniformRadialCoefficient p.Kr p.b
      (deepestCaptureScale ξ) (deepestCaptureScale ξ) p.core p.d p.δcur * p.Cb ^ 3 *
      deepestCaptureScale ξ ^ 2 * (1 + p.duration) ^ 3) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using
      (((hradial.const_mul p.b).mul_const (p.Cb ^ 3)).mul he2).mul_const ((1 + p.duration) ^ 3)
  have hweight : Tendsto (fun ξ : ℝ => (2 * deepestCaptureScale ξ ^ 6) * p.Kboot) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using (he6.const_mul 2).mul_const p.Kboot
  have houter : Tendsto (fun ξ : ℝ => (2 * p.b * 2 * p.Kboot * (p.Cl + p.torusC)) *
      deepestCaptureScale ξ ^ 2) atTop (𝓝 0) := by
    simpa only [mul_zero] using he2.const_mul (2 * p.b * 2 * p.Kboot * (p.Cl + p.torusC))
  have hclock : Tendsto (fun ξ : ℝ => p.Cb * deepestCaptureScale ξ * (1 + p.duration)) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using (he.const_mul p.Cb).mul_const (1 + p.duration)
  have hbox : Tendsto (fun ξ : ℝ => p.Cb * deepestCaptureScale ξ * deepestCaptureScale ξ *
      (1 + p.duration)) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using ((he.const_mul p.Cb).mul he).mul_const (1 + p.duration)
  have hκ : Tendsto (fun ξ : ℝ => p.torusC * deepestCaptureScale ξ ^ 8) atTop (𝓝 0) := by
    simpa only [mul_zero] using he8.const_mul p.torusC
  have hcap : Tendsto (fun ξ : ℝ => 9 * p.C * p.Damp / (p.lam - 1) +
      3 * (p.E * (p.torusC * deepestCaptureScale ξ ^ 8)) * (p.Ncap : ℝ)) atTop
      (𝓝 (9 * p.C * p.Damp / (p.lam - 1))) := by
    simpa only [mul_zero, zero_mul, add_zero] using
      (((hκ.const_mul p.E).const_mul 3).mul_const (p.Ncap : ℝ)).const_add (9 * p.C * p.Damp / (p.lam - 1))
  have hforce : Tendsto (fun ξ : ℝ => p.Bpoly * deepestCaptureScale ξ ^ 6 * (1 + p.duration) ^ 4 +
      (p.torusC * deepestCaptureScale ξ ^ 8) * (3 * p.Damp)) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul, add_zero] using
      ((he6.const_mul p.Bpoly).mul_const ((1 + p.duration) ^ 4)).add (hκ.mul_const (3 * p.Damp))
  have hsource : Tendsto (fun ξ : ℝ => p.F * p.Bpoly * deepestCaptureScale ξ ^ 6) atTop (𝓝 0) := by
    simpa only [mul_zero] using he6.const_mul (p.F * p.Bpoly)
  have hchartLimit : Tendsto (fun ξ : ℝ => (5 / 4 : ℝ) * deepestCaptureScale ξ) atTop (𝓝 0) := by
    simpa only [mul_zero] using he.const_mul (5 / 4 : ℝ)
  have hdomainLimit : Tendsto (fun ξ : ℝ => deepestCaptureScale ξ * (p.referenceNorm + p.δgeom))
      atTop (𝓝 0) := by
    simpa only [zero_mul] using he.mul_const (p.referenceNorm + p.δgeom)
  filter_upwards [eventually_le_of_tendsto_zero he (by norm_num : (0 : ℝ) < 1 / 2),
    eventually_le_of_tendsto_zero he zero_lt_one,
    eventually_le_of_tendsto_zero he (half_pos h.b_pos),
    eventually_le_of_tendsto_zero he2 (half_pos h.b_pos),
    eventually_le_of_tendsto_zero he (div_pos cellA_pos (by norm_num : (0 : ℝ) < 128)),
    hlin (5 / 4) cellA_pos, hlin 10 (half_pos cellA_pos), hlin (8 * p.L) h.core_pos,
    eventually_le_of_tendsto_zero (by simpa using he6.const_mul (2 : ℝ)) zero_lt_one,
    eventually_le_of_tendsto_zero hweight (lt_min h.rw_pos h.geom_pos),
    eventually_le_of_tendsto_zero (by simpa using he8.const_mul (2 : ℝ)) (by norm_num : (0 : ℝ) < 1 / 2),
    eventually_le_of_tendsto_zero (by simpa using he8.const_mul p.torusW) zero_lt_one,
    hdrift.eventually (eventually_lt_nhds h.drift_margin),
    hlin p.d (by norm_num : (0 : ℝ) < 1 / 16),
    hchartLimit.eventually
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 16)),
    hlin (p.L + 1) (by norm_num : (0 : ℝ) < 1 / 32),
    hdomainLimit.eventually
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 64)),
    eventually_ge_atTop (0 : ℝ), eventually_le_of_tendsto_zero houter zero_lt_one,
    eventually_le_of_tendsto_zero hcubic (half_pos h.radial_pos),
    eventually_le_of_tendsto_zero hclock (half_pos h.core_pos), eventually_le_of_tendsto_zero hclock h.d_pos,
    eventually_le_of_tendsto_zero hbox (by norm_num : (0 : ℝ) < 1 / 16),
    eventually_le_of_tendsto_zero (by simpa only [mul_zero] using hclock.const_mul (8 : ℝ)) (half_pos cellA_pos),
    eventually_le_of_tendsto_zero hκ h.kappa_pos,
    hcap.eventually (eventually_lt_nhds h.capture_margin), eventually_le_of_tendsto_zero hforce h.error_pos,
    eventually_le_of_tendsto_zero hsource (div_pos h.seed_pos (by norm_num : (0 : ℝ) < 32)),
    he2.eventually (eventually_lt_nhds (Real.rpow_pos_of_pos h.b_pos p.q))]
    with ξ hhalf hone hbhalf hsq hinit hcore hup hdown hwei hboot hrow htor hdr hrad hchart hgeom hdom hξ
      hout hcub hpco hpou hpbox hpsep hk hca hfo hso hlp
  exact ⟨hhalf, hone, hbhalf, hsq, hinit, hcore, hup, hdown, hwei, hboot, hrow, htor, hdr, hrad,
    hchart, hgeom, hdom, le_add_of_nonneg_left (mul_nonneg (div_nonneg (by norm_num) sigma_pos.le) hξ),
    hout, hcub, hpco, hpou, hpbox, hpsep, hk, hca.le, hfo, hso, hlp⟩

end DeepestCaptureScaleData
end Euler2D

end
