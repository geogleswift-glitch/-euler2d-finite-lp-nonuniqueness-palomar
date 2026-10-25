module

public import RequestProject.Euler.CircularFiniteEulerUniformVectorCorrection
public import RequestProject.Euler.CircularCaptureCoupledScaleSmallness

/-! Actual rotating-label velocity estimates with R=rho^10 and
A0=cA*(1+xi). Every source, support and residual belongs to the SAME
original Euler system. The amplitude is chosen after the scale. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 5500

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

theorem tendsto_circularFinite_torusCoefficient_coupled_scale
    (K b d₀ d₁ : ℝ) :
    Tendsto (fun ξ : ℝ => K * (d₀ + d₁ * ξ) ^ 4 *
      circularFiniteL1Coefficient b (Real.exp (-ξ)) * (Real.exp (-ξ) ^ 10) ^ 8)
      atTop (𝓝 0) := by
  simpa only [finiteEulerUniformRadialCoefficient, mul_zero, zero_div, zero_add] using
    tendsto_circularFinite_radialCoefficient_coupled_scale K b 1 d₀ d₁ 0

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem eventually_actualFinite_coupled_normalizedCorrectionLabelVelocity_le
    {s cA b q T B ε : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hs : s ≤ 0) (hcA : 0 < cA) (hb : 0 < b) (hb1 : b ≤ 1)
    (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q) (hT : 0 ≤ T) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∀ᶠ ξ : ℝ in atTop,
      let ρ := Real.exp (-ξ)
      let hρ := Real.exp_pos (-ξ)
      let R := ρ ^ 10
      let hR := pow_pos hρ 10
      let A₀ := cA * (1 + ξ)
      ∀ N : ℕ, ∀ S : BoundedEulerParticleSystem
        (finiteBaseCurlL2 (A₀ := A₀) (b := b) (ρ := ρ) hR hρ hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := b) (ρ := ρ) (q := q) hs hR hρ) N) T,
      IsFourfoldBoundedEulerParticleSystem S → ∀ t ∈ Icc (0 : ℝ) T,
      ∀ k : ℕ, ∀ θ : ℝ, ∀ z : R2, ‖z‖ ≤ B →
        ‖S.normalizedCorrectionLabelVelocity (ampScale A₀ b k) (radScale R ρ k) t θ z‖ ≤ ε := by
  obtain ⟨Cs, hCs, hsupport⟩ := P.exists_uniform_finiteEuler_support_bound
  obtain ⟨K, hK, hcorrection⟩ := P.exists_uniform_normalizedCorrectionLabelVelocity_bound
  let dc := 4 * Cs * cA * T
  let dsupport := fun ξ : ℝ => B + 2 + dc * (1 + ξ)
  have hdlin (ξ : ℝ) : dsupport ξ = (B + 2 + dc) + dc * ξ := by
    dsimp only [dsupport]
    ring
  have he := Real.tendsto_exp_neg_atTop_nhds_zero
  have he2 : Tendsto (fun ξ : ℝ => Real.exp (-ξ) ^ 2) atTop (𝓝 0) := by simpa using he.pow 2
  have hdRlim : Tendsto (fun ξ : ℝ => dsupport ξ * Real.exp (-ξ) ^ 10) atTop (𝓝 0) := by
    convert tendsto_circularCapture_log_monomial 1 dc (B + 1 + dc) 10 1 (by decide) using 1
    ext ξ
    dsimp only [dsupport]
    ring
  have hsmallLimit : Tendsto (fun ξ : ℝ => K * dsupport ξ ^ 4 *
      circularFiniteL1Coefficient b (Real.exp (-ξ)) * (Real.exp (-ξ) ^ 10) ^ 8 * B ^ 3)
      atTop (𝓝 0) := by
    simpa only [hdlin, zero_mul] using
      (tendsto_circularFinite_torusCoefficient_coupled_scale K b (B + 2 + dc) dc).mul_const (B ^ 3)
  filter_upwards [he.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    he.eventually (eventually_lt_nhds (half_pos hb)),
    he2.eventually (eventually_lt_nhds hb),
    hdRlim.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 16)),
    hsmallLimit.eventually (eventually_lt_nhds hε), eventually_ge_atTop (0 : ℝ)]
      with ξ hhalf hρhalf hsmall hdR hSmall hξ
  try dsimp only
  let ρ := Real.exp (-ξ)
  let R := ρ ^ 10
  let A₀ := cA * (1 + ξ)
  let d := B + 2 + 4 * Cs * A₀ * T
  have hρ : 0 < ρ := Real.exp_pos (-ξ)
  have hR : 0 < R := pow_pos hρ 10
  have hA : 0 < A₀ := mul_pos hcA (by linarith only [hξ])
  have hρ1 : ρ ≤ 1 := hhalf.le.trans (by norm_num)
  have hRρ : R ≤ ρ := by
    simpa only [R, pow_one] using pow_le_pow_of_le_one hρ.le hρ1 (by decide : (1 : ℕ) ≤ 10)
  have hRmax : R ≤ 1 / 2 := hRρ.trans hhalf.le
  have hρb : ρ < b := hρhalf.trans (half_lt_self hb)
  have hcat : 0 ≤ Cs * A₀ * T := mul_nonneg (mul_nonneg hCs.le hA.le) hT
  have hd : 0 < d := by dsimp only [d]; nlinarith only [hB, hcat]
  have hBd : B ≤ d := by dsimp only [d]; nlinarith only [hcat]
  have hdeq : dsupport ξ = d := by dsimp only [dsupport, dc, d, A₀]; ring
  rw [hdeq] at hdR hSmall
  have hden : (1 / 2 : ℝ) ≤ 1 - ρ / b := by
    have hh : ρ / b ≤ 1 / 2 := (div_le_iff₀ hb).mpr (by linarith only [hρhalf])
    linarith only [hh]
  have hdiv : Cs * A₀ / (1 - ρ / b) ≤ 2 * Cs * A₀ := by
    calc
      _ ≤ Cs * A₀ / (1 / 2) :=
        div_le_div_of_nonneg_left (mul_nonneg hCs.le hA.le) (by norm_num) hden
      _ = _ := by ring
  have hDrift : 5 / 4 + (Cs * A₀ / (1 - ρ / b)) * T < d := by
    have hh := mul_le_mul_of_nonneg_right hdiv hT
    dsimp only [d]
    nlinarith only [hh, hcat, hB]
  have hpowBase : b * ρ ^ 2 ≤ 1 :=
    (mul_le_mul_of_nonneg_right hb1 (sq_nonneg ρ)).trans
      (by simpa only [one_mul] using pow_le_one₀ hρ.le hρ1 (n := 2))
  have hmassnn : 0 ≤ circularFiniteL1Coefficient b ρ := circularFiniteL1Coefficient_nonneg_of_ratio hb hsmall
  have hcoef : 0 ≤ K * d ^ 4 * circularFiniteL1Coefficient b ρ * R ^ 8 := by positivity
  intro N S hS t ht k θ z hz
  have hsupp := hsupport (s := s) (A₀ := A₀) (b := b) (R := R) (ρ := ρ) (q := q)
    (T := T) (H := T) (c := d) hs hA.le hb hR hRmax hρ hρ1 hρb hq hqE hT le_rfl hDrift
    (hdR.trans (by norm_num : (1 / 16 : ℝ) < 1)) N S t ht
  have hquery : radScale R ρ k * ‖z‖ ≤ d * R := by
    have hrk : 0 ≤ radScale R ρ k := (radScale_pos hR hρ k).le
    have hrkmax : radScale R ρ k ≤ R := mul_le_of_le_one_right hR.le (pow_le_one₀ hρ.le hρ1)
    calc
      _ ≤ radScale R ρ k * d := mul_le_mul_of_nonneg_left (hz.trans hBd) hrk
      _ ≤ R * d := mul_le_mul_of_nonneg_right hrkmax hd.le
      _ = _ := mul_comm _ _
  have hh := hcorrection (s := s) (A₀ := A₀) (b := b) (R := R) (ρ := ρ) (q := q) (T := T)
    (d := d) hs hA hb hR hRmax hρ hρ1 hq hqE hsmall hd hdR.le N S hS t ht hsupp k θ z hquery
  have hk : (b * ρ ^ 2) ^ k ≤ 1 := pow_le_one₀ (mul_nonneg hb.le (sq_nonneg ρ)) hpowBase
  refine hh.trans (le_trans ?_ hSmall.le)
  calc
    _ ≤ (K * d ^ 4 * circularFiniteL1Coefficient b ρ * R ^ 8) * 1 * B ^ 3 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hk hcoef)
        (pow_le_pow_left₀ (norm_nonneg _) hz 3) (by positivity) (by positivity)
    _ = _ := by ring

end CircularMaterialTransferProfile
end Euler2D

end
