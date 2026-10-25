module

public import RequestProject.Euler.DeepestCaptureScaleChoice
public import RequestProject.Euler.CircularCaptureCoupledScaleSmallness

/-! All deepest-capture budgets with the amplitude chosen AFTER the
shrinking scale: A0=cA*(1+xi), R=rho^10. The actual radial coefficient,
support drift and physical radius are retained, not bounded by a
fixed-amplitude eventuality with an unjustified choice order. -/

@[expose] public section

set_option maxHeartbeats 8000000
set_option maxRecDepth 6000

noncomputable section

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace Euler2D
namespace DeepestCaptureScaleData

def coupledAmplitude (p : DeepestCaptureScaleData) (ξ : ℝ) : ℝ := p.A₀ * (1 + ξ)

def coupledSupport (p : DeepestCaptureScaleData) (ξ : ℝ) : ℝ :=
  2 + 4 * p.Cgeo * p.coupledAmplitude ξ * p.T

structure CoupledAdmissible (p : DeepestCaptureScaleData) : Prop where
  b_pos : 0 < p.b
  core_pos : 0 < p.core
  rw_pos : 0 < p.rw
  geom_pos : 0 < p.δgeom
  radial_pos : 0 < p.Cr
  amplitude_pos : 0 < p.A₀
  geo_nonneg : 0 ≤ p.Cgeo
  time_nonneg : 0 ≤ p.T
  kappa_pos : 0 < p.κ₀
  error_pos : 0 < p.ε₀
  seed_pos : 0 < p.seed
  capture_margin : 9 * p.C * p.Damp / (p.lam - 1) < 1 / 16

structure CoupledBudget (p : DeepestCaptureScaleData) (ξ : ℝ) : Prop where
  xi_nonneg : 0 ≤ ξ
  amplitude_pos : 0 < p.coupledAmplitude ξ
  support_pos : 0 < p.coupledSupport ξ
  scale_le : deepestCaptureScale ξ ^ 10 ≤ deepestCaptureScale ξ
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
  torus : p.torusW * (deepestCaptureScale ξ ^ 10) ^ 8 ≤ 1
  drift : 5 / 4 + (p.Cgeo * p.coupledAmplitude ξ /
    (1 - deepestCaptureScale ξ / p.b)) * p.T < p.coupledSupport ξ
  radius : p.coupledSupport ξ * deepestCaptureScale ξ ^ 10 ≤ 1 / 16
  initial_chart : (5 / 4 : ℝ) * deepestCaptureScale ξ ^ 10 < 1 / 16
  geometry : (p.L + 1) * deepestCaptureScale ξ ^ 10 ≤ 1 / 32
  domain : deepestCaptureScale ξ ^ 10 * (p.referenceNorm + p.δgeom) < 1 / 64
  logarithmic : p.duration ≤ (6 / sigma) * ξ + p.duration
  outer_source : (2 * p.b * 2 * p.Kboot * (p.Cl + p.torusC)) * deepestCaptureScale ξ ^ 2 ≤ 1
  radial : p.b * finiteEulerUniformRadialCoefficient p.Kr p.b
      (deepestCaptureScale ξ ^ 10) (deepestCaptureScale ξ) p.core (p.coupledSupport ξ)
      p.δcur * p.Cb ^ 3 * deepestCaptureScale ξ ^ 2 * (1 + p.duration) ^ 3 ≤ p.Cr / 2
  particle_core : p.Cb * deepestCaptureScale ξ * (1 + p.duration) ≤ p.core / 2
  particle_outer : p.Cb * deepestCaptureScale ξ * (1 + p.duration) ≤ p.coupledSupport ξ
  particle_box : p.Cb * deepestCaptureScale ξ * deepestCaptureScale ξ ^ 10 *
    (1 + p.duration) ≤ 1 / 16
  particle_sep : 8 * (p.Cb * deepestCaptureScale ξ * (1 + p.duration)) ≤ cellA / 2
  kappa : p.torusC * (deepestCaptureScale ξ ^ 10) ^ 8 ≤ p.κ₀
  capture : 9 * p.C * p.Damp / (p.lam - 1) +
    3 * (p.E * (p.torusC * (deepestCaptureScale ξ ^ 10) ^ 8)) * (p.Ncap : ℝ) ≤ 1 / 16
  forcing : p.Bpoly * deepestCaptureScale ξ ^ 6 * (1 + p.duration) ^ 4 +
    (p.torusC * (deepestCaptureScale ξ ^ 10) ^ 8) * (3 * p.Damp) ≤ p.ε₀
  source : p.F * p.Bpoly * deepestCaptureScale ξ ^ 6 ≤ p.seed / 32
  lp_ratio : deepestCaptureScale ξ ^ 2 < p.b ^ p.q

private theorem eventually_le_zero_limit {f : ℝ → ℝ} {ε : ℝ}
    (hf : Tendsto f atTop (𝓝 0)) (hε : 0 < ε) : ∀ᶠ ξ : ℝ in atTop, f ξ ≤ ε :=
  (hf.eventually (eventually_lt_nhds hε)).mono (fun _ h => h.le)

theorem eventually_coupled_budget (p : DeepestCaptureScaleData) (h : p.CoupledAdmissible) :
    ∀ᶠ ξ : ℝ in atTop, p.CoupledBudget ξ := by
  have he : Tendsto deepestCaptureScale atTop (𝓝 0) := Real.tendsto_exp_neg_atTop_nhds_zero
  have he2 : Tendsto (fun ξ : ℝ => deepestCaptureScale ξ ^ 2) atTop (𝓝 0) := by simpa using he.pow 2
  have he6 : Tendsto (fun ξ : ℝ => deepestCaptureScale ξ ^ 6) atTop (𝓝 0) := by simpa using he.pow 6
  have he8 : Tendsto (fun ξ : ℝ => deepestCaptureScale ξ ^ 8) atTop (𝓝 0) := by simpa using he.pow 8
  have hR : Tendsto (fun ξ : ℝ => deepestCaptureScale ξ ^ 10) atTop (𝓝 0) := by simpa using he.pow 10
  have hR8 : Tendsto (fun ξ : ℝ => (deepestCaptureScale ξ ^ 10) ^ 8) atTop (𝓝 0) := by
    simpa using hR.pow 8
  have hlin (A : ℝ) {ε : ℝ} (hε : 0 < ε) :
      ∀ᶠ ξ : ℝ in atTop, A * deepestCaptureScale ξ ≤ ε := by
    apply eventually_le_zero_limit _ hε
    simpa only [mul_zero] using he.const_mul A
  have hRlin (A : ℝ) {ε : ℝ} (hε : 0 < ε) :
      ∀ᶠ ξ : ℝ in atTop, A * deepestCaptureScale ξ ^ 10 ≤ ε := by
    apply eventually_le_zero_limit _ hε
    simpa only [mul_zero] using hR.const_mul A
  have hd (ξ : ℝ) : p.coupledSupport ξ =
      (2 + 4 * p.Cgeo * p.A₀ * p.T) + (4 * p.Cgeo * p.A₀ * p.T) * ξ := by
    unfold coupledSupport coupledAmplitude
    ring
  have hradial : Tendsto (fun ξ : ℝ => finiteEulerUniformRadialCoefficient p.Kr p.b
      (deepestCaptureScale ξ ^ 10) (deepestCaptureScale ξ) p.core (p.coupledSupport ξ) p.δcur)
      atTop (𝓝 ((32 / (15 * p.core ^ 4) * circularRadialPerturbationWeight) * p.δcur)) := by
    simpa only [hd, deepestCaptureScale] using
      tendsto_circularFinite_radialCoefficient_coupled_scale p.Kr p.b p.core
        (2 + 4 * p.Cgeo * p.A₀ * p.T) (4 * p.Cgeo * p.A₀ * p.T) p.δcur
  have hdR : Tendsto (fun ξ : ℝ => p.coupledSupport ξ * deepestCaptureScale ξ ^ 10)
      atTop (𝓝 0) := by
    convert tendsto_circularCapture_log_monomial 1 (4 * p.Cgeo * p.A₀ * p.T)
      (1 + 4 * p.Cgeo * p.A₀ * p.T) 10 1 (by decide) using 1
    ext ξ
    rw [hd]
    dsimp only [deepestCaptureScale]
    ring
  have hcubic : Tendsto (fun ξ : ℝ => p.b * finiteEulerUniformRadialCoefficient p.Kr p.b
      (deepestCaptureScale ξ ^ 10) (deepestCaptureScale ξ) p.core (p.coupledSupport ξ) p.δcur *
      p.Cb ^ 3 * deepestCaptureScale ξ ^ 2 * (1 + p.duration) ^ 3) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using
      (((hradial.const_mul p.b).mul_const (p.Cb ^ 3)).mul he2).mul_const ((1 + p.duration) ^ 3)
  have hweight : Tendsto (fun ξ : ℝ => (2 * deepestCaptureScale ξ ^ 6) * p.Kboot) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using (he6.const_mul 2).mul_const p.Kboot
  have houter : Tendsto (fun ξ : ℝ => (2 * p.b * 2 * p.Kboot * (p.Cl + p.torusC)) *
      deepestCaptureScale ξ ^ 2) atTop (𝓝 0) := by
    simpa only [mul_zero] using he2.const_mul (2 * p.b * 2 * p.Kboot * (p.Cl + p.torusC))
  have hclock : Tendsto (fun ξ : ℝ => p.Cb * deepestCaptureScale ξ * (1 + p.duration)) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using (he.const_mul p.Cb).mul_const (1 + p.duration)
  have hbox : Tendsto (fun ξ : ℝ => p.Cb * deepestCaptureScale ξ * deepestCaptureScale ξ ^ 10 *
      (1 + p.duration)) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using ((he.const_mul p.Cb).mul hR).mul_const (1 + p.duration)
  have hκ : Tendsto (fun ξ : ℝ => p.torusC * (deepestCaptureScale ξ ^ 10) ^ 8) atTop (𝓝 0) := by
    simpa only [mul_zero] using hR8.const_mul p.torusC
  have hcap : Tendsto (fun ξ : ℝ => 9 * p.C * p.Damp / (p.lam - 1) +
      3 * (p.E * (p.torusC * (deepestCaptureScale ξ ^ 10) ^ 8)) * (p.Ncap : ℝ)) atTop
      (𝓝 (9 * p.C * p.Damp / (p.lam - 1))) := by
    simpa only [mul_zero, zero_mul, add_zero] using
      (((hκ.const_mul p.E).const_mul 3).mul_const (p.Ncap : ℝ)).const_add (9 * p.C * p.Damp / (p.lam - 1))
  have hforce : Tendsto (fun ξ : ℝ => p.Bpoly * deepestCaptureScale ξ ^ 6 * (1 + p.duration) ^ 4 +
      (p.torusC * (deepestCaptureScale ξ ^ 10) ^ 8) * (3 * p.Damp)) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul, add_zero] using
      ((he6.const_mul p.Bpoly).mul_const ((1 + p.duration) ^ 4)).add (hκ.mul_const (3 * p.Damp))
  have hsource : Tendsto (fun ξ : ℝ => p.F * p.Bpoly * deepestCaptureScale ξ ^ 6) atTop (𝓝 0) := by
    simpa only [mul_zero] using he6.const_mul (p.F * p.Bpoly)
  have hchartLimit : Tendsto (fun ξ : ℝ => (5 / 4 : ℝ) * deepestCaptureScale ξ ^ 10) atTop (𝓝 0) := by
    simpa only [mul_zero] using hR.const_mul (5 / 4 : ℝ)
  have hdomainLimit : Tendsto (fun ξ : ℝ => deepestCaptureScale ξ ^ 10 * (p.referenceNorm + p.δgeom))
      atTop (𝓝 0) := by
    simpa only [zero_mul] using hR.mul_const (p.referenceNorm + p.δgeom)
  filter_upwards [eventually_le_zero_limit he (by norm_num : (0 : ℝ) < 1 / 2),
    eventually_le_zero_limit he zero_lt_one,
    eventually_le_zero_limit he (half_pos h.b_pos),
    eventually_le_zero_limit he2 (half_pos h.b_pos),
    eventually_le_zero_limit he (div_pos cellA_pos (by norm_num : (0 : ℝ) < 128)),
    hlin (5 / 4) cellA_pos, hlin 10 (half_pos cellA_pos), hlin (8 * p.L) h.core_pos,
    eventually_le_zero_limit (by simpa using he6.const_mul (2 : ℝ)) zero_lt_one,
    eventually_le_zero_limit hweight (lt_min h.rw_pos h.geom_pos),
    eventually_le_zero_limit (by simpa using he8.const_mul (2 : ℝ)) (by norm_num : (0 : ℝ) < 1 / 2),
    eventually_le_zero_limit (by simpa using hR8.const_mul p.torusW) zero_lt_one,
    eventually_le_zero_limit hdR (by norm_num : (0 : ℝ) < 1 / 16),
    hchartLimit.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 16)),
    hRlin (p.L + 1) (by norm_num : (0 : ℝ) < 1 / 32),
    hdomainLimit.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 64)),
    eventually_ge_atTop (0 : ℝ), eventually_le_zero_limit houter zero_lt_one,
    eventually_le_zero_limit hcubic (half_pos h.radial_pos),
    eventually_le_zero_limit hclock (half_pos h.core_pos),
    eventually_le_zero_limit hclock (by norm_num : (0 : ℝ) < 2),
    eventually_le_zero_limit hbox (by norm_num : (0 : ℝ) < 1 / 16),
    eventually_le_zero_limit (by simpa only [mul_zero] using hclock.const_mul (8 : ℝ)) (half_pos cellA_pos),
    eventually_le_zero_limit hκ h.kappa_pos,
    hcap.eventually (eventually_lt_nhds h.capture_margin), eventually_le_zero_limit hforce h.error_pos,
    eventually_le_zero_limit hsource (div_pos h.seed_pos (by norm_num : (0 : ℝ) < 32)),
    he2.eventually (eventually_lt_nhds (Real.rpow_pos_of_pos h.b_pos p.q))]
    with ξ hhalf hone hbhalf hsq hinit hcore hup hdown hwei hboot hrow htor hrad hchart hgeom hdom hξ
      hout hcub hpco hpou hpbox hpsep hk hca hfo hso hlp
  have hA : 0 < p.coupledAmplitude ξ := mul_pos h.amplitude_pos (by linarith only [hξ])
  have hcat : 0 ≤ p.Cgeo * p.coupledAmplitude ξ * p.T :=
    mul_nonneg (mul_nonneg h.geo_nonneg hA.le) h.time_nonneg
  have hdTwo : 2 ≤ p.coupledSupport ξ := by
    unfold coupledSupport
    nlinarith only [hcat]
  have hden : (1 / 2 : ℝ) ≤ 1 - deepestCaptureScale ξ / p.b := by
    have hh : deepestCaptureScale ξ / p.b ≤ 1 / 2 :=
      (div_le_iff₀ h.b_pos).mpr (by linarith only [hbhalf])
    linarith only [hh]
  have hcoef : p.Cgeo * p.coupledAmplitude ξ / (1 - deepestCaptureScale ξ / p.b) ≤
      2 * p.Cgeo * p.coupledAmplitude ξ := by
    calc
      _ ≤ p.Cgeo * p.coupledAmplitude ξ / (1 / 2) :=
        div_le_div_of_nonneg_left (mul_nonneg h.geo_nonneg hA.le) (by norm_num) hden
      _ = _ := by ring
  have hdrift : 5 / 4 + (p.Cgeo * p.coupledAmplitude ξ /
      (1 - deepestCaptureScale ξ / p.b)) * p.T < p.coupledSupport ξ := by
    have hh := mul_le_mul_of_nonneg_right hcoef h.time_nonneg
    unfold coupledSupport
    nlinarith only [hh, hcat]
  have hscale : deepestCaptureScale ξ ^ 10 ≤ deepestCaptureScale ξ := by
    simpa only [pow_one] using
      pow_le_pow_of_le_one (Real.exp_pos (-ξ)).le hone (by decide : (1 : ℕ) ≤ 10)
  exact ⟨hξ, hA, (by linarith only [hdTwo]), hscale, hhalf, hone, hbhalf, hsq,
    hinit, hcore, hup, hdown, hwei, hboot, hrow, htor, hdrift, hrad, hchart, hgeom, hdom,
    le_add_of_nonneg_left (mul_nonneg (div_nonneg (by norm_num) sigma_pos.le) hξ),
    hout, hcub, hpco, hpou.trans hdTwo, hpbox, hpsep, hk, hca.le, hfo, hso, hlp⟩

end DeepestCaptureScaleData
end Euler2D

end
