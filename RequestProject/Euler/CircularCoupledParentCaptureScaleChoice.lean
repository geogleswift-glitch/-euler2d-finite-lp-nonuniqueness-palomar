module

public import RequestProject.Euler.CircularCoupledDeepestScaleChoice

/-! Uniform coupled physical budgets when the parent capture count is
chosen AFTER xi from its actual entrance seed. The true radial coefficient,
linearly growing support and rho^10 physical radius are retained.
The entrance-dependent source condition is still supplied by the actual
source-ready family; the fixed numeric seed field is not used for that step. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 6500

noncomputable section

open Filter Topology

namespace Euler2D
namespace DeepestCaptureScaleData

theorem eventually_coupled_logarithmic_parent_budget
    (p : DeepestCaptureScaleData) (hp : p.CoupledAdmissible)
    (hCb : 0 ≤ p.Cb) (hBpoly : 0 ≤ p.Bpoly)
    (hE : 0 ≤ p.E) (hTorus : 0 ≤ p.torusC) (hblock : 0 < p.blockTime)
    (Lclock Dclock : ℝ) :
    ∀ᶠ ξ : ℝ in atTop, ∀ Ncap : ℕ,
      let pN : DeepestCaptureScaleData := {p with Ncap := Ncap}
      pN.duration ≤ Lclock * ξ + Dclock →
      pN.CoupledBudget ξ ∧
        p.Cb * deepestCaptureScale ξ * (1 + pN.duration) ≤ cellA / 128 := by
  let dc := 4 * p.Cgeo * p.A₀ * p.T
  let margin := 1 / 16 - 9 * p.C * p.Damp / (p.lam - 1)
  let Kcap := 3 * p.E * p.torusC / p.blockTime
  let particleMax := min (p.core / 2) (min (1 / 16) (cellA / 128))
  have hmargin : 0 < margin := sub_pos.mpr hp.capture_margin
  have hKcap : 0 ≤ Kcap := div_nonneg (by positivity) hblock.le
  have hParticleMax : 0 < particleMax := lt_min (half_pos hp.core_pos)
    (lt_min (by norm_num) (div_pos cellA_pos (by norm_num)))
  have hrad := eventually_circularCapture_log_radial_cubic_budget
    (K := p.Kr) (b := p.b) (core := p.core) (d₀ := 2 + dc) (d₁ := dc)
    (δ := p.δcur) (Cb := p.Cb) (L := Lclock) (D₀ := Dclock) hp.radial_pos
  have hparticles := eventually_circularCapture_log_monomial_small
    (K := p.Cb) (L := Lclock) (D₀ := Dclock) hCb hParticleMax 1 1 (by decide)
  have hcap := eventually_circularCapture_log_monomial_small
    (K := Kcap) (L := Lclock) (D₀ := Dclock) hKcap hmargin 80 1 (by decide)
  have hpoly := eventually_circularCapture_log_monomial_small
    (K := p.Bpoly) (L := Lclock) (D₀ := Dclock) hBpoly (half_pos hp.error_pos) 6 4 (by decide)
  have htorLim : Tendsto (fun ξ : ℝ => p.torusC * (Real.exp (-ξ) ^ 10) ^ 8 * (3 * p.Damp))
      atTop (𝓝 0) := by
    simpa only [zero_pow (by decide : (10 : ℕ) ≠ 0), zero_pow (by decide : (8 : ℕ) ≠ 0),
      mul_zero, zero_mul] using
      (((Real.tendsto_exp_neg_atTop_nhds_zero.pow 10).pow 8).const_mul p.torusC).mul_const (3 * p.Damp)
  have htorSmall := (htorLim.eventually (gt_mem_nhds (half_pos hp.error_pos))).mono (fun _ h => h.le)
  filter_upwards [p.eventually_coupled_budget hp, hrad, hparticles, hcap, hpoly, htorSmall]
    with ξ hbase hradξ hparticlesξ hcapξ hpolyξ htorξ
  intro Ncap
  dsimp only
  intro hDlog
  let pN : DeepestCaptureScaleData := {p with Ncap := Ncap}
  let D := (Ncap : ℝ) * p.blockTime
  let ρ := deepestCaptureScale ξ
  have hD : 0 ≤ D := mul_nonneg (Nat.cast_nonneg _) hblock.le
  change D ≤ Lclock * ξ + Dclock at hDlog
  change pN.CoupledBudget ξ ∧ p.Cb * ρ * (1 + D) ≤ cellA / 128
  have hρ : 0 < ρ := Real.exp_pos (-ξ)
  have hρ1 : ρ ≤ 1 := hbase.one
  have hR1 : ρ ^ 10 ≤ 1 := hbase.scale_le.trans hρ1
  have hd : p.coupledSupport ξ = (2 + dc) + dc * ξ := by
    dsimp only [coupledSupport, coupledAmplitude, dc]
    ring
  have hsupportTwo : 2 ≤ p.coupledSupport ξ := by
    have hh := mul_nonneg (mul_nonneg hp.geo_nonneg hbase.amplitude_pos.le) hp.time_nonneg
    dsimp only [coupledSupport]
    nlinarith only [hh]
  have hradD := hradξ D hD hDlog
  rw [← hd] at hradD
  have hparticle := hparticlesξ D hD hDlog
  simp only [pow_one] at hparticle
  have hparticleCore : p.Cb * ρ * (1 + D) ≤ p.core / 2 :=
    hparticle.trans (min_le_left _ _)
  have hparticle16 : p.Cb * ρ * (1 + D) ≤ 1 / 16 :=
    hparticle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hbuffer : p.Cb * ρ * (1 + D) ≤ cellA / 128 :=
    hparticle.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hparticleOuter : p.Cb * ρ * (1 + D) ≤ p.coupledSupport ξ :=
    hparticle16.trans ((by norm_num : (1 / 16 : ℝ) ≤ 2).trans hsupportTwo)
  have hparticleBox : p.Cb * ρ * ρ ^ 10 * (1 + D) ≤ 1 / 16 := by
    calc
      _ = (p.Cb * ρ * (1 + D)) * ρ ^ 10 := by ring
      _ ≤ p.Cb * ρ * (1 + D) := mul_le_of_le_one_right (by positivity) hR1
      _ ≤ _ := hparticle16
  have hparticleSep : 8 * (p.Cb * ρ * (1 + D)) ≤ cellA / 2 := by
    nlinarith only [hbuffer, cellA_pos]
  have hcapD := hcapξ D hD hDlog
  simp only [pow_one] at hcapD
  have hcapIdentity : 3 * (p.E * (p.torusC * (ρ ^ 10) ^ 8)) * (Ncap : ℝ) =
      Kcap * ρ ^ 80 * D := by
    dsimp only [Kcap, D]
    field_simp [hblock.ne']
    <;> ring
  have hcapture : 9 * p.C * p.Damp / (p.lam - 1) +
      3 * (p.E * (p.torusC * (ρ ^ 10) ^ 8)) * (Ncap : ℝ) ≤ 1 / 16 := by
    rw [hcapIdentity]
    have hsmall : Kcap * ρ ^ 80 * D ≤ margin :=
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1))
        (mul_nonneg hKcap (pow_nonneg hρ.le 80))).trans hcapD
    dsimp only [margin] at hsmall
    linarith only [hsmall]
  have hpolyD := hpolyξ D hD hDlog
  have hforcing : p.Bpoly * ρ ^ 6 * (1 + D) ^ 4 +
      (p.torusC * (ρ ^ 10) ^ 8) * (3 * p.Damp) ≤ p.ε₀ := by
    linarith only [hpolyD, htorξ]
  have hlog : D ≤ (6 / sigma) * ξ + D :=
    le_add_of_nonneg_left (mul_nonneg (div_nonneg (by norm_num) sigma_pos.le) hbase.xi_nonneg)
  refine ⟨{
    xi_nonneg := hbase.xi_nonneg
    amplitude_pos := hbase.amplitude_pos
    support_pos := hbase.support_pos
    scale_le := hbase.scale_le
    half := hbase.half
    one := hbase.one
    bhalf := hbase.bhalf
    sq_bhalf := hbase.sq_bhalf
    initial_sep := hbase.initial_sep
    initial_core := hbase.initial_core
    upper_sep := hbase.upper_sep
    lower_sep := hbase.lower_sep
    weight := hbase.weight
    weighted_bootstrap := hbase.weighted_bootstrap
    row := hbase.row
    torus := hbase.torus
    drift := hbase.drift
    radius := hbase.radius
    initial_chart := hbase.initial_chart
    geometry := hbase.geometry
    domain := hbase.domain
    logarithmic := hlog
    outer_source := hbase.outer_source
    radial := hradD
    particle_core := hparticleCore
    particle_outer := hparticleOuter
    particle_box := hparticleBox
    particle_sep := hparticleSep
    kappa := hbase.kappa
    capture := hcapture
    forcing := hforcing
    source := hbase.source
    lp_ratio := hbase.lp_ratio }, hbuffer⟩

end DeepestCaptureScaleData
end Euler2D

end
