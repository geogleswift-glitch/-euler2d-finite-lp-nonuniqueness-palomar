module

public import RequestProject.Euler.CircularActualCapturedRootVelocity
public import RequestProject.Euler.CircularActualRootInnerMomentFamily

/-! One positive velocity departure bound for all cutoffs, on the SAME
already constructed actual captured Euler family at one fixed scale. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 28000000
set_option maxRecDepth 9000

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

attribute [local instance 2000] rigidGaugeLittle_group rigidGaugeLittle_space rigidGaugeFamily_tower
attribute [local instance] LittleContourSpace.complexScalarNormedSpace LittleContourSpace.complexScalarTower
attribute [local instance 2000] phaseDomainC1_group phaseDomainC1_space

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

def HasActualRootVelocityDepartureFamilyAt {q T : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q)
    (b : ℝ≥0) (s : ℝ) (hs : s ≤ 0) (cA ξ : ℝ) : Prop :=
  let ρ := Real.exp (-ξ)
  let hρ := Real.exp_pos (-ξ)
  let R := ρ ^ 10
  let hR := pow_pos hρ 10
  let A₀ := cA * (1 + ξ)
  ρ ≤ 1 / 2 ∧ ρ ^ (2 / q) < (b : ℝ) ∧ ∃ ε > 0,
  ∀ N : ℕ, 0 < N →
    let f := finiteBaseCurlL2 (A₀ := A₀) (b := (b : ℝ)) (ρ := ρ) hR hρ hq hqE
      (P.finiteBaseLp (A₀ := A₀) (b := (b : ℝ)) (ρ := ρ) (q := q) hs hR hρ) N
    ∃ S : BoundedEulerParticleSystem f T,
      IsFourfoldBoundedEulerParticleSystem S ∧
      IsWeakEulerSolution T (biotSavartL2 f) (particleVelocity f S.backward S.backward_area) ∧
      (∀ t ∈ Icc (0 : ℝ) T, MeasurePreserving (S.forward t) volume volume ∧
        MeasurePreserving (S.backward t) volume volume) ∧
      ∃ t ∈ Ioo (0 : ℝ) (T / 2), ε ≤
        ‖particleVelocity f S.backward S.backward_area t -
          velocityDatumL2 (A₀ := A₀) (b := (b : ℝ)) hR hρ‖

theorem eventually_actual_root_velocity_of_innerMoment
    {q T s cA δ η Cb D₀ m : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q) (hq2 : 2 ≤ q) (hT : 0 < T)
    (hs : s ≤ 0) (hcA : 0 < cA) (ℓ : ℕ) (b : ℝ≥0) (hb : 0 < b)
    (hδ : 0 < δ) (hη : 0 < η) (hηa : η ≤ cellA / 16) (hCb : 0 ≤ Cb) (hm : 0 < m) :
    ∀ᶠ ξ : ℝ in atTop,
      P.HasActualRootInnerMomentFamilyAt (T := T) hq hqE ℓ δ η Cb D₀ m b s hs cA ξ →
      P.HasActualRootVelocityDepartureFamilyAt (T := T) hq hqE b s hs cA ξ := by
  obtain ⟨Cgeo, hCgeo, hvelocity⟩ := P.exists_uniform_actualCaptured_root_velocity_departure
  have hbR : 0 < (b : ℝ) := hb
  have hρlim : Tendsto (fun ξ : ℝ => Real.exp (-ξ)) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero
  have hhalf : ∀ᶠ ξ : ℝ in atTop, Real.exp (-ξ) ≤ 1 / 2 :=
    (hρlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).mono (fun _ h => h.le)
  have hbhalf : ∀ᶠ ξ : ℝ in atTop, Real.exp (-ξ) ≤ (b : ℝ) / 2 :=
    (hρlim.eventually (gt_mem_nhds (half_pos hbR))).mono (fun _ h => h.le)
  have hinner : ∀ᶠ ξ : ℝ in atTop, Real.exp (-ξ) ≤ cellA / 4 :=
    (hρlim.eventually (gt_mem_nhds (div_pos cellA_pos (by norm_num)))).mono (fun _ h => h.le)
  let r := ((b : ℝ) / 2) ^ (q / 2)
  have hr : 0 < r := Real.rpow_pos_of_pos (half_pos hbR) _
  have hsmallEv : ∀ᶠ ξ : ℝ in atTop, Real.exp (-ξ) ^ (2 / q) < (b : ℝ) := by
    filter_upwards [hρlim.eventually (gt_mem_nhds hr)] with ξ hξ
    have hrpow : r ^ (2 / q) = (b : ℝ) / 2 := by
      dsimp only [r]
      rw [← Real.rpow_mul (half_pos hbR).le]
      rw [show q / 2 * (2 / q) = 1 by field_simp [hq.ne'], Real.rpow_one]
    exact (Real.rpow_le_rpow (Real.exp_pos _).le hξ.le (by positivity : 0 ≤ 2 / q)).trans_lt
      (by rw [hrpow]; exact half_lt_self hbR)
  let dcoef := 4 * Cgeo * cA * T
  let dsupport := fun ξ : ℝ => 2 + dcoef * (1 + ξ)
  have hdlim : Tendsto (fun ξ : ℝ => dsupport ξ * Real.exp (-ξ) ^ 10) atTop (𝓝 0) := by
    convert tendsto_circularCapture_log_monomial 1 dcoef (1 + dcoef) 10 1 (by decide) using 1
    ext ξ
    dsimp only [dsupport]
    ring
  have hscale : ∀ᶠ ξ : ℝ in atTop, dsupport ξ * Real.exp (-ξ) ^ 10 ≤ 1 / 4 :=
    (hdlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))).mono (fun _ h => h.le)
  have hparticleLim : Tendsto
      (fun ξ : ℝ => Cb * Real.exp (-ξ) * (1 + ((6 / sigma) * ξ + D₀))) atTop (𝓝 0) := by
    convert tendsto_circularCapture_log_monomial Cb (6 / sigma) D₀ 1 1 (by decide) using 1
    ext ξ
    ring
  have hparticleBudget : ∀ᶠ ξ : ℝ in atTop,
      Cb * Real.exp (-ξ) * (1 + ((6 / sigma) * ξ + D₀)) ≤ cellA / 4 :=
    (hparticleLim.eventually (gt_mem_nhds (div_pos cellA_pos (by norm_num)))).mono (fun _ h => h.le)
  have hcellUpper : cellA < 4 / 5 := by nlinarith only [cellA_sq, cellA_pos]
  have hηmax : 3 * η < 1 / 5 := by linarith only [hηa, hcellUpper]
  filter_upwards [hhalf, hbhalf, hinner, hsmallEv, hscale, hparticleBudget,
    eventually_ge_atTop (0 : ℝ)] with ξ hρmax hρhalf hρinner hsmall hdR hparticles hξ
  intro hfamily
  let ρ := Real.exp (-ξ)
  have hρ : 0 < ρ := Real.exp_pos (-ξ)
  let R := ρ ^ 10
  have hR : 0 < R := pow_pos hρ 10
  let A₀ := cA * (1 + ξ)
  have hA : 0 < A₀ := mul_pos hcA (by linarith only [hξ])
  have hρone : ρ ≤ 1 := hρmax.trans (by norm_num)
  have hRρ : R ≤ ρ := by
    simpa only [R, pow_one] using pow_le_pow_of_le_one hρ.le hρone (by decide : (1 : ℕ) ≤ 10)
  have hRmax : R ≤ 1 / 2 := hRρ.trans hρmax
  have hρb : ρ < (b : ℝ) := hρhalf.trans_lt (half_lt_self hbR)
  have hdenHalf : (1 / 2 : ℝ) ≤ 1 - ρ / b := by
    have hfrac : ρ / b ≤ 1 / 2 := (div_le_iff₀ hbR).mpr (by linarith only [hρhalf])
    linarith only [hfrac]
  let d := 2 + 4 * Cgeo * A₀ * T
  have hdeq : dsupport ξ = d := by dsimp only [dsupport, dcoef, d, A₀]; ring
  rw [hdeq] at hdR
  have hcat : 0 < Cgeo * A₀ * T := mul_pos (mul_pos hCgeo hA) hT
  have hdiv : Cgeo * A₀ / (1 - ρ / b) ≤ 2 * Cgeo * A₀ := by
    calc
      _ ≤ Cgeo * A₀ / (1 / 2) :=
        div_le_div_of_nonneg_left (mul_nonneg hCgeo.le hA.le) (by norm_num) hdenHalf
      _ = _ := by ring
  have hdrift : 5 / 4 + (Cgeo * A₀ / (1 - ρ / b)) * T < d := by
    have hh := mul_le_mul_of_nonneg_right hdiv hT.le
    dsimp only [d]
    nlinarith only [hh, hcat]
  dsimp only [HasActualRootInnerMomentFamilyAt] at hfamily
  obtain ⟨_, _, hsolutions⟩ := hfamily
  let K := complexCurlTestBound (contDiff_annularDepartureTest
    (by positivity : 0 < 3 * η) hηmax hR (hRmax.trans (by norm_num)))
  have hdepart (N : ℕ) (hN : 0 < N)
      (S : BoundedEulerParticleSystem
        (finiteBaseCurlL2 (A₀ := A₀) (b := (b : ℝ)) (ρ := ρ) hR hρ hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := (b : ℝ)) (ρ := ρ) (q := q) hs hR hρ) N) T)
      (hsection : P.HasActualCapturedInnerMomentSection (s := s) (A₀ := A₀) (b := (b : ℝ))
        hR hρ (Nat.zero_le N) S ℓ δ η Cb D₀ ξ m) :
      ∃ t ∈ Ioo (0 : ℝ) (T / 2), 0 < K ∧
        (5 / 2 * A₀ * R ^ 2 * ((m / 2) * δ)) / K ≤
          ‖particleVelocity _ S.backward S.backward_area t -
            velocityDatumL2 (A₀ := A₀) (b := (b : ℝ)) hR hρ‖ :=
    hvelocity hs hA hbR hR hRmax hρ hρone hρb hρinner hq hqE hq2 hsmall
      hδ hη hηa hηmax hCb hm hdrift hdR hparticles N ℓ S hsection
  obtain ⟨Sone, _, _, _, hsectionOne⟩ := hsolutions 1 (by decide)
  obtain ⟨tone, _, hK, _⟩ := hdepart 1 (by decide) Sone hsectionOne
  let ε := (5 / 2 * A₀ * R ^ 2 * ((m / 2) * δ)) / K
  have hε : 0 < ε := by dsimp only [ε]; positivity
  refine ⟨hρmax, hsmall, ε, hε, ?_⟩
  intro N hN
  obtain ⟨S, hS, hEuler, harea, hsection⟩ := hsolutions N hN
  obtain ⟨t, ht, _, hgap⟩ := hdepart N hN S hsection
  exact ⟨S, hS, hEuler, harea, t, ht, hgap⟩

end CircularMaterialTransferProfile
end Euler2D

end
