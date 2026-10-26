module

public import RequestProject.Euler.CircularFiniteEulerVectorCorrection
public import RequestProject.Euler.CircularRetardedBudgetFeedback

/-! Uniform smallness of the actual torus vector correction, with its
source support derived from the same original finite Euler system.
The shrinking scale is fixed before every cutoff, label, and time. -/

@[expose] public section

set_option maxHeartbeats 6000000
set_option maxRecDepth 5500

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

theorem tendsto_circularFiniteL1Coefficient_exp_neg (b : ℝ) :
    Tendsto (fun ξ : ℝ => circularFiniteL1Coefficient b (Real.exp (-ξ))) atTop
      (𝓝 ((eLpNorm cellW 1 volume).toReal +
        finiteContourPatchMassBound circularContourStrengths circularContourRadii)) := by
  have he := Real.tendsto_exp_neg_atTop_nhds_zero
  have he2 : Tendsto (fun ξ : ℝ => Real.exp (-ξ) ^ 2) atTop (𝓝 0) := by simpa using he.pow 2
  have hden : Tendsto (fun ξ : ℝ => 1 - Real.exp (-ξ) ^ 2 / b) atTop (𝓝 1) := by
    simpa only [zero_div, sub_zero] using
      (tendsto_const_nhds : Tendsto (fun _ξ : ℝ => (1 : ℝ)) atTop (𝓝 1)).sub (he2.div_const b)
  have hnum : Tendsto (fun _ξ : ℝ => (eLpNorm cellW 1 volume).toReal) atTop
      (𝓝 (eLpNorm cellW 1 volume).toReal) := tendsto_const_nhds
  simpa only [Pi.div_def, circularFiniteL1Coefficient, div_one] using
    (hnum.div hden (by norm_num : (1 : ℝ) ≠ 0)).add_const
      (finiteContourPatchMassBound circularContourStrengths circularContourRadii)

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem eventually_actualFinite_normalizedCorrectionLabelVelocity_le
    {s A₀ b q T B ε : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hs : s ≤ 0) (hA : 0 < A₀) (hb : 0 < b) (hb1 : b ≤ 1)
    (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q) (hT : 0 ≤ T) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∀ᶠ ξ : ℝ in atTop,
      let ρ := Real.exp (-ξ)
      let hρ := Real.exp_pos (-ξ)
      ∀ N : ℕ, ∀ S : BoundedEulerParticleSystem
        (finiteBaseCurlL2 (A₀ := A₀) (b := b) (ρ := ρ) hρ hρ hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := b) (ρ := ρ) (q := q) hs hρ hρ) N) T,
      IsFourfoldBoundedEulerParticleSystem S → ∀ t ∈ Icc (0 : ℝ) T,
      ∀ k : ℕ, ∀ θ : ℝ, ∀ z : R2, ‖z‖ ≤ B →
        ‖S.normalizedCorrectionLabelVelocity (ampScale A₀ b k) (radScale ρ ρ k) t θ z‖ ≤ ε := by
  obtain ⟨Cs, hCs, hsupport⟩ := P.exists_uniform_finiteEuler_support_bound
  obtain ⟨K, hK, hcorrection⟩ := P.exists_uniform_normalizedCorrectionLabelVelocity_bound
  let d := max (B + 1) (2 + 2 * Cs * A₀ * T)
  have hBd : B ≤ d := (by linarith : B ≤ B + 1).trans (le_max_left _ _)
  have hd : 0 < d := (by linarith : (0 : ℝ) < B + 1).trans_le (le_max_left _ _)
  have hcat : 0 ≤ Cs * A₀ * T := mul_nonneg (mul_nonneg hCs.le hA.le) hT
  have hdrift : 5 / 4 + Cs * A₀ * T < d := by
    have hh : 2 + 2 * Cs * A₀ * T ≤ d := le_max_right _ _
    linarith only [hh, hcat]
  have he : Tendsto (fun ξ : ℝ => Real.exp (-ξ)) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero
  have he2 : Tendsto (fun ξ : ℝ => Real.exp (-ξ) ^ 2) atTop (𝓝 0) := by simpa using he.pow 2
  have he8 : Tendsto (fun ξ : ℝ => Real.exp (-ξ) ^ 8) atTop (𝓝 0) := by simpa using he.pow 8
  have hden : Tendsto (fun ξ : ℝ => 1 - Real.exp (-ξ) / b) atTop (𝓝 1) := by
    simpa only [zero_div, sub_zero] using
      (tendsto_const_nhds : Tendsto (fun _ξ : ℝ => (1 : ℝ)) atTop (𝓝 1)).sub (he.div_const b)
  have hdriftLimit : Tendsto (fun ξ : ℝ => 5 / 4 + (Cs * A₀ /
      (1 - Real.exp (-ξ) / b)) * T) atTop (𝓝 (5 / 4 + Cs * A₀ * T)) := by
    have hnum : Tendsto (fun _ξ : ℝ => Cs * A₀) atTop (𝓝 (Cs * A₀)) := tendsto_const_nhds
    simpa only [Pi.div_def, div_one] using
      ((hnum.div hden (by norm_num : (1 : ℝ) ≠ 0)).mul_const T).const_add (5 / 4)
  have hradialLimit : Tendsto (fun ξ : ℝ => d * Real.exp (-ξ)) atTop (𝓝 0) := by
    simpa only [mul_zero] using he.const_mul d
  have hsmallLimit : Tendsto (fun ξ : ℝ =>
      K * d ^ 4 * circularFiniteL1Coefficient b (Real.exp (-ξ)) * Real.exp (-ξ) ^ 8 * B ^ 3)
      atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using
      (((tendsto_circularFiniteL1Coefficient_exp_neg b).const_mul (K * d ^ 4)).mul he8).mul_const (B ^ 3)
  filter_upwards [he.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    he.eventually (eventually_lt_nhds hb), he2.eventually (eventually_lt_nhds hb),
    hdriftLimit.eventually (eventually_lt_nhds hdrift),
    hradialLimit.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 16)),
    hsmallLimit.eventually (eventually_lt_nhds hε)] with ξ hhalf hρb hsmall hDrift hdρ hSmall
  try dsimp only
  let ρ := Real.exp (-ξ)
  have hρ : 0 < ρ := Real.exp_pos (-ξ)
  have hρ1 : ρ ≤ 1 := hhalf.le.trans (by norm_num)
  have hpowBase : b * ρ ^ 2 ≤ 1 :=
    (mul_le_mul_of_nonneg_right hb1 (sq_nonneg ρ)).trans
      (by simpa only [one_mul] using pow_le_one₀ hρ.le hρ1 (n := 2))
  have hmassnn : 0 ≤ circularFiniteL1Coefficient b ρ := circularFiniteL1Coefficient_nonneg_of_ratio hb hsmall
  have hcoef : 0 ≤ K * d ^ 4 * circularFiniteL1Coefficient b ρ * ρ ^ 8 := by positivity
  intro N S hS t ht k θ z hz
  have hsupp := hsupport (s := s) (A₀ := A₀) (b := b) (R := ρ) (ρ := ρ) (q := q)
    (T := T) (H := T) (c := d) hs hA.le hb hρ hhalf.le hρ hρ1 hρb hq hqE hT le_rfl hDrift
    (hdρ.trans (by norm_num : (1 / 16 : ℝ) < 1)) N S t ht
  have hquery : radScale ρ ρ k * ‖z‖ ≤ d * ρ := by
    have hrk : 0 ≤ radScale ρ ρ k := (radScale_pos hρ hρ k).le
    have hrkmax : radScale ρ ρ k ≤ ρ := mul_le_of_le_one_right hρ.le (pow_le_one₀ hρ.le hρ1)
    calc
      _ ≤ radScale ρ ρ k * d := mul_le_mul_of_nonneg_left (hz.trans hBd) hrk
      _ ≤ ρ * d := mul_le_mul_of_nonneg_right hrkmax hd.le
      _ = _ := mul_comm _ _
  have hh := hcorrection (s := s) (A₀ := A₀) (b := b) (R := ρ) (ρ := ρ) (q := q) (T := T)
    (d := d) hs hA hb hρ hhalf.le hρ hρ1 hq hqE hsmall hd hdρ.le N S hS t ht hsupp k θ z hquery
  have hk : (b * ρ ^ 2) ^ k ≤ 1 := pow_le_one₀ (mul_nonneg hb.le (sq_nonneg ρ)) hpowBase
  refine hh.trans (le_trans ?_ hSmall.le)
  calc
    _ ≤ (K * d ^ 4 * circularFiniteL1Coefficient b ρ * ρ ^ 8) * 1 * B ^ 3 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hk hcoef)
        (pow_le_pow_left₀ (norm_nonneg _) hz 3) (by positivity) (by positivity)
    _ = _ := by ring

end CircularMaterialTransferProfile
end Euler2D

end
