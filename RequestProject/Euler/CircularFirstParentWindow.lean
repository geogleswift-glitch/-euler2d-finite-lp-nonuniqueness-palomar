module

public import RequestProject.Euler.CircularDeepestEarlierEntry
public import RequestProject.Euler.CircularActualParentObservationWindow
public import RequestProject.Euler.CircularActualMaterialClock
public import RequestProject.Euler.CircularWeightedNormParameters

/-! Construct the first parent window on the SAME actual Euler system.
The original slow-rate budget supplies every numerical smallness
condition. The true past parent controls and two-level floor are retained. -/

@[expose] public section

set_option maxHeartbeats 40000000
set_option maxRecDepth 9000

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

attribute [local instance 2000] rigidGaugeLittle_group rigidGaugeLittle_space rigidGaugeFamily_tower
attribute [local instance] LittleContourSpace.complexScalarNormedSpace LittleContourSpace.complexScalarTower
attribute [local irreducible] circularBanachField circularBanachDomain

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_actualDeepest_parent_window_setup :
    ∃ Kself : ℝ≥0, 0 < Kself ∧
      ∀ b : ℝ≥0, 0 < b → b < 1 / 4 →
      (b : ℝ) * Kself + (b : ℝ) *
        (finiteInnerLabelLittleRowCoefficient (γ : ℝ) (cellA / 2)
          (circularCanonicalCellNormBudget hγ hγ1) / (2 - 1)) < sigma / 4 →
      ∀ {s A₀ q T Dcap Dobs η : ℝ}, ∀ [Fact (1 ≤ ENNReal.ofReal q)],
      ∀ (hs : s ≤ 0) (hA : 0 < A₀) (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q),
      0 < Dcap → 0 < Dobs → Dobs ≤ Dcap →
      0 < η → η ≤ cellA / 16 → η ≤ (1 - cellA) / 16 → Dcap / A₀ < T →
      ∃ Cb > 0, ∃ Ccur > 0, ∃ Cobs > 0,
      ∀ᶠ ξ : ℝ in atTop,
        let ρ := Real.exp (-ξ)
        let hρ := Real.exp_pos (-ξ)
        let h := 2 * ρ ^ 6
        ∀ N : ℕ, 0 < N →
        ∀ S : BoundedEulerParticleSystem
          (finiteBaseCurlL2 (A₀ := A₀) (b := (b : ℝ)) (ρ := ρ) hρ hρ hq hqE
            (P.finiteBaseLp (A₀ := A₀) (b := (b : ℝ)) (ρ := ρ) (q := q) hs hρ hρ) N) T,
        IsFourfoldBoundedEulerParticleSystem S →
        ∀ X : ℝ → FiniteCircularIndex N → LittleContourSpace γ,
        P.ActualCanonicalPrefixTrajectory s A₀ b ρ ρ (1 / 16) T hρ hρ le_rfl S
          (Dcap / ampScale A₀ b N) X →
        (∀ u ∈ Icc (0 : ℝ) Dcap,
          weightedFamilyNorm h N (canonicalPrefixStageDeviation hγ hγ1 A₀ b ρ ρ N 0 X u) ≤ 1) →
        (∀ u ∈ Icc (0 : ℝ) Dcap,
          ‖canonicalPrefixStageDeviation hγ hγ1 A₀ b ρ ρ N 0 X u N‖ ≤ η) →
        ∀ e ∈ Ioc (0 : ℝ) Dcap,
        let entrance := e / ampScale A₀ b N
        let Dparent := (b : ℝ) * Dobs
        let Hparent := entrance + Dparent / ampScale A₀ b (N - 1)
        ∃ Y : ℝ → FiniteCircularIndex (N - 1) → LittleContourSpace γ,
          P.ActualCanonicalPrefixTrajectory s A₀ b ρ ρ (1 / 16) T hρ hρ
            (Nat.sub_le N 1) S Hparent Y ∧
          (∀ u ∈ Icc (0 : ℝ) Dparent,
            weightedFamilyNorm h (N - 1)
              (canonicalPrefixStageDeviation hγ hγ1 A₀ b ρ ρ (N - 1) entrance Y u) ≤ Cobs * h) ∧
          (∀ u ∈ Icc (0 : ℝ) Dparent,
            ‖canonicalPrefixStageDeviation hγ hγ1 A₀ b ρ ρ (N - 1) entrance Y u (N - 1)‖ ≤ Ccur * h) ∧
          (∀ u ∈ Icc (0 : ℝ) Dparent, ∀ z ∈ P.finiteInnerActiveInitialLabels s A₀ b ρ ρ N (N - 1),
            ‖S.forward (physicalTimeFromNormalized (ampScale A₀ b (N - 1)) entrance u) z - torusCenter‖ ≤
              Cb * ρ * radScale ρ ρ (N - 1) * (1 + u)) ∧
          (∀ t ∈ Icc (0 : ℝ) entrance,
            ∀ z ∈ P.finiteInnerActiveInitialLabels s A₀ b ρ ρ N (N - 1),
            ‖S.forward t z - torusCenter‖ ≤ 2 * ρ * radScale ρ ρ (N - 1)) ∧
          ∀ t ∈ Icc (0 : ℝ) entrance,
            let x := canonicalPrefixStageDeviation hγ hγ1 A₀ b ρ ρ (N - 1) 0 Y
              (ampScale A₀ b (N - 1) * t)
            weightedFamilyNorm h (N - 1) x ≤ h ∧ ‖x (N - 1)‖ ≤ h ∧
              (2 ≤ N → ‖x (N - 2)‖ ≤ h ^ 2) := by
  obtain ⟨Kself, hKself, rw, hrw, Ctw, hCtw, hwindowAll⟩ :=
    P.exists_uniform_actual_parent_observation_window
  obtain ⟨Creset, hCreset, hreset⟩ := P.exists_uniform_actualCanonical_crossPrefix_weighted_reset
  obtain ⟨Cmaterial, hCmaterial, hmaterial⟩ := P.exists_uniform_actualPrefix_weighted_materialTube
  refine ⟨Kself, hKself, ?_⟩
  intro b hb hbquarter hslow s A₀ q T Dcap Dobs η _ hs hA hq hqE
    hDcap hDobs hDobsCap hη hηa hηgap htime
  have hbR : 0 < (b : ℝ) := hb
  have hb1 : b < 1 := hbquarter.trans (by norm_num)
  have hT : 0 < T := (div_pos hDcap hA).trans htime
  let L := circularCanonicalCellNormBudget hγ hγ1
  let core := cellA / 2
  let Cu := finiteInnerLabelLittleRowCoefficient (γ : ℝ) (cellA / 2) L
  let Cl := finiteOuterLabelLittleRowCoefficient (γ : ℝ) core L L
  let torusRow := finiteTorusLabelLittleRowCoefficient (γ : ℝ) L
  let Dparent := (b : ℝ) * Dobs
  have hDparent : 0 < Dparent := mul_pos hbR hDobs
  obtain ⟨CgeoWin, Ctc, Cdc, Cr, Kr, Ccur, Cobs, hCgeoWin, hCtc, hCdc, hCr, hKr, hCcur, hCobs,
    hwindow⟩ := hwindowAll b hb hb1 (D := Dparent) (C₀ := 2) (K := 1) (νbar := sigma / 3)
      hDparent (by norm_num) (by norm_num) hη hηa hηgap
  let Cb := radialStageRadiusConstant Cr 2 b
  let Cgeo := CgeoWin + Creset + Cmaterial + 1
  let d := 2 + 4 * Cgeo * A₀ * T
  have hL : 0 < L := circularCanonicalCellNormBudget_pos hγ hγ1
  have hcore : 0 < core := half_pos cellA_pos
  have hcorei (i : Fin 2) : core ≤ 3 * circularContourRadii i / 4 := by
    have hi := (circularContourRadii_bounds i).2.1
    dsimp only [core]
    linarith only [hi, cellA_pos]
  have hCgeo : 0 < Cgeo := by dsimp only [Cgeo]; positivity
  have hCb : 0 < Cb := radialStageRadiusConstant_pos hCr (by norm_num) hbR hb1
  have hcat : 0 < Cgeo * A₀ * T := mul_pos (mul_pos hCgeo hA) hT
  have hd : 0 < d := by dsimp only [d]; nlinarith only [hcat]
  have hcauchy : 0 ≤ cauchyContourNormBudget 5 (γ : ℝ) 1 (cellA / 2) L :=
    (cauchySpatialDerivativeBudget_nonneg 5 (by norm_num : (0 : ℝ) ≤ 1)
      (half_pos cellA_pos) 0).trans (le_max_left _ _)
  have hinterior : 0 ≤ interiorContourNormBudget (γ : ℝ) 1 core L L :=
    (interiorSpatialDerivativeBudget_nonneg (M := 1) (a := core) (by norm_num) hL 0).trans
      (le_max_left _ _)
  have hweight : 0 ≤ circularRadialPerturbationWeight :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (circularContourRadii_bounds i).1.le)
  have hCu : 0 ≤ Cu := by unfold Cu finiteInnerLabelLittleRowCoefficient; positivity
  have hCl : 0 ≤ Cl := by unfold Cl finiteOuterLabelLittleRowCoefficient; positivity
  have htorusRow : 0 ≤ torusRow := finiteTorusLabelLittleRowCoefficient_nonneg hL.le
  have hsmall (C : ℝ) (n : ℕ) (hn : n ≠ 0) (ε : ℝ) (hε : 0 < ε) :
      ∀ᶠ ξ : ℝ in atTop, C * Real.exp (-ξ) ^ n ≤ ε := by
    have ht : Tendsto (fun ξ : ℝ => C * Real.exp (-ξ) ^ n) atTop (𝓝 0) := by
      simpa only [zero_pow hn, mul_zero] using
        (Real.tendsto_exp_neg_atTop_nhds_zero.pow n).const_mul C
    exact (ht.eventually (gt_mem_nhds hε)).mono (fun _ h => h.le)
  have hrate : ∀ᶠ ξ : ℝ in atTop,
      weightedNormPropagationExponent Kself b Cu Cl 2 (3 * Ctw * torusRow)
        (Real.exp (-ξ)) (Real.exp (-ξ)) ≤ sigma / 3 := by
    have hlim := tendsto_weightedNormPropagationExponent_diag Kself b Cu Cl 2 (3 * Ctw * torusRow)
    have hgap : (b : ℝ) * Kself + (b : ℝ) * (Cu / (2 - 1)) < sigma / 3 := by
      have hh : (b : ℝ) * Kself + (b : ℝ) * (Cu / (2 - 1)) < sigma / 4 := hslow
      nlinarith only [hh, sigma_pos]
    exact (hlim.eventually (gt_mem_nhds hgap)).mono (fun _ h => h.le)
  have he := Real.tendsto_exp_neg_atTop_nhds_zero
  have he2 : Tendsto (fun ξ : ℝ => Real.exp (-ξ) ^ 2) atTop (𝓝 0) := by simpa using he.pow 2
  have he8 : Tendsto (fun ξ : ℝ => Real.exp (-ξ) ^ 8) atTop (𝓝 0) := by simpa using he.pow 8
  have hOne : Tendsto (fun _ξ : ℝ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hmden : Tendsto (fun ξ : ℝ => 1 - Real.exp (-ξ) ^ 2 / b) atTop (𝓝 1) := by
    simpa only [zero_div, sub_zero] using hOne.sub (he2.div_const (b : ℝ))
  let m₀ := (eLpNorm cellW 1 volume).toReal
  let M := finiteContourPatchMassBound circularContourStrengths circularContourRadii
  have hmass : Tendsto (fun ξ : ℝ => circularFiniteL1Coefficient b (Real.exp (-ξ))) atTop (𝓝 (m₀ + M)) := by
    have hnum : Tendsto (fun _ξ : ℝ => m₀) atTop (𝓝 m₀) := tendsto_const_nhds
    simpa only [circularFiniteL1Coefficient, div_one] using
      (hnum.div hmden (by norm_num : (1 : ℝ) ≠ 0)).add_const M
  have hrden : Tendsto (fun ξ : ℝ => 1 - (b : ℝ) * Real.exp (-ξ) ^ 2) atTop (𝓝 1) := by
    simpa only [mul_zero, sub_zero] using hOne.sub (he2.const_mul (b : ℝ))
  let radialLimit := (32 / (15 * core ^ 4) * circularRadialPerturbationWeight) * η
  have hradial : Tendsto (fun ξ : ℝ => finiteEulerUniformRadialCoefficient Kr b
      (Real.exp (-ξ)) (Real.exp (-ξ)) core d η) atTop (𝓝 radialLimit) := by
    have hnum : Tendsto (fun _ξ : ℝ => radialLimit) atTop (𝓝 radialLimit) := tendsto_const_nhds
    have hfirst := hnum.div hrden (by norm_num : (1 : ℝ) ≠ 0)
    have hsecond := (hmass.const_mul (Kr * d ^ 4)).mul he8
    simpa only [finiteEulerUniformRadialCoefficient, div_one, mul_zero, add_zero] using hfirst.add hsecond
  have hcubic : ∀ᶠ ξ : ℝ in atTop,
      (b : ℝ) * finiteEulerUniformRadialCoefficient Kr b (Real.exp (-ξ)) (Real.exp (-ξ)) core d η *
        Cb ^ 3 * Real.exp (-ξ) ^ 2 * (1 + Dparent) ^ 3 ≤ Cr / 2 := by
    have ht : Tendsto (fun ξ : ℝ => (b : ℝ) * finiteEulerUniformRadialCoefficient Kr b
        (Real.exp (-ξ)) (Real.exp (-ξ)) core d η * Cb ^ 3 * Real.exp (-ξ) ^ 2 * (1 + Dparent) ^ 3)
        atTop (𝓝 0) := by
      simpa only [mul_zero, zero_mul] using
        (((hradial.const_mul (b : ℝ)).mul_const (Cb ^ 3)).mul he2).mul_const ((1 + Dparent) ^ 3)
    exact (ht.eventually (gt_mem_nhds (half_pos hCr))).mono (fun _ h => h.le)
  refine ⟨Cb, hCb, Ccur, hCcur, Cobs, hCobs, ?_⟩
  filter_upwards [hwindow, hrate, hcubic,
    hsmall 1 1 (by decide) (1 / 2) (by norm_num),
    hsmall 1 1 (by decide) ((b : ℝ) / 2) (half_pos hbR),
    hsmall 1 1 (by decide) (cellA / 256) (div_pos cellA_pos (by norm_num)),
    hsmall 1 2 (by decide) ((b : ℝ) / 2) (half_pos hbR),
    hsmall (5 / 4) 1 (by decide) cellA cellA_pos,
    hsmall 10 1 (by decide) core hcore, hsmall (8 * L) 1 (by decide) core hcore,
    hsmall 2 6 (by decide) 1 (by norm_num),
    hsmall 4 6 (by decide) (min rw η) (lt_min hrw hη),
    hsmall 2 6 (by decide) η hη, hsmall 2 8 (by decide) (1 / 2) (by norm_num),
    hsmall (Ctw * torusRow) 8 (by decide) 1 (by norm_num),
    hsmall d 1 (by decide) (1 / 16) (by norm_num),
    hsmall (5 / 4) 1 (by decide) (1 / 32) (by norm_num),
    hsmall (L + 1) 1 (by decide) (1 / 32) (by norm_num),
    hsmall (‖littleCircularReference hγ hγ1‖ + η) 1 (by decide) (1 / 128) (by norm_num),
    hsmall (2 * (b : ℝ) * 2 * 2 * (Cl + Ctc * torusRow)) 2 (by decide) 1 (by norm_num),
    hsmall (Cb * (1 + Dparent)) 1 (by decide) (core / 2) (half_pos hcore),
    hsmall (Cb * (1 + Dparent)) 1 (by decide) d hd,
    hsmall (Cb * (1 + Dparent)) 2 (by decide) (1 / 16) (by norm_num),
    hsmall (8 * (Cb * (1 + Dparent))) 1 (by decide) core hcore,
    hsmall (max 2 (Cb * (1 + Dparent))) 1 (by decide) (cellA / 128) (div_pos cellA_pos (by norm_num))]
    with ξ hwindowξ hrateξ hcubicξ hρhalf hρbhalf hρsmall hρsq hρcore hsepU hsepL
      hh1 hhboot hhη hζ hCtRw hdR hρchart hgeom hsize houter hinnerCore hinnerChart hchart hsep hbuffer
  simp only [pow_one, one_mul] at hρhalf hρbhalf hρsmall hρsq hρcore hsepU hsepL hdR hρchart hgeom hsize
  simp only [pow_one, one_mul] at hinnerCore hinnerChart hsep hbuffer
  let ρ := Real.exp (-ξ)
  let h := 2 * ρ ^ 6
  have hρ : 0 < ρ := Real.exp_pos (-ξ)
  have hh : 0 < h := by dsimp only [h]; positivity
  have hρ1 : ρ ≤ 1 := hρhalf.trans (by norm_num)
  have hρb : ρ < (b : ℝ) := hρbhalf.trans_lt (half_lt_self hbR)
  have hden : 0 < 1 - ρ / b := sub_pos.mpr ((div_lt_one hbR).mpr hρb)
  have hdenHalf : (1 / 2 : ℝ) ≤ 1 - ρ / b := by
    have hh' : ρ / b ≤ 1 / 2 := (div_le_iff₀ hbR).mpr (by nlinarith only [hρbhalf])
    linarith only [hh']
  have hdiv : Cgeo * A₀ / (1 - ρ / b) ≤ 2 * Cgeo * A₀ := by
    calc
      _ ≤ Cgeo * A₀ / (1 / 2) :=
        div_le_div_of_nonneg_left (mul_nonneg hCgeo.le hA.le) (by norm_num) hdenHalf
      _ = _ := by ring
  have hdrift : 5 / 4 + (Cgeo * A₀ / (1 - ρ / b)) * T < d := by
    have hm := mul_le_mul_of_nonneg_right hdiv hT.le
    dsimp only [d]
    nlinarith only [hm, hcat]
  have hdriftFor (C : ℝ) (hC : C ≤ Cgeo) : 5 / 4 + (C * A₀ / (1 - ρ / b)) * T < d :=
    (add_le_add le_rfl (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hC hA.le) hden.le) hT.le)).trans_lt hdrift
  have hWinC : CgeoWin ≤ Cgeo := by dsimp only [Cgeo]; linarith only [hCreset, hCmaterial]
  have hResetC : Creset ≤ Cgeo := by dsimp only [Cgeo]; linarith only [hCgeoWin, hCmaterial]
  have hMaterialC : Cmaterial ≤ Cgeo := by dsimp only [Cgeo]; linarith only [hCgeoWin, hCreset]
  have hβ : 0 ≤ 3 * (Ctw * torusRow * ρ ^ 8) + weightedInteractionRowFeedback b Cu Cl 2 ρ := by
    have hfb := weightedInteractionRowFeedback_nonneg hbR.le hCu hCl (by norm_num)
      (hζ.trans_lt (by norm_num))
    positivity
  have hν : ((b * Kself : ℝ≥0) : ℝ) +
      (3 * (Ctw * torusRow * ρ ^ 8) + weightedInteractionRowFeedback b Cu Cl 2 ρ) ≤ sigma / 3 := by
    simpa only [weightedNormPropagationExponent, NNReal.coe_mul, mul_assoc, add_assoc] using hrateξ
  have hηquarter : η ≤ cellA / 4 := by linarith only [hηa, cellA_pos]
  have hdRquarter : d * ρ ≤ 1 / 4 := hdR.trans (by norm_num)
  have hρchartStrict : (5 / 4 : ℝ) * ρ < 1 / 16 := hρchart.trans_lt (by norm_num)
  have hsizeStrict : ρ * (‖littleCircularReference hγ hγ1‖ + η) < (1 / 16 : ℝ) / 4 := by
    have hs' : ρ * (‖littleCircularReference hγ hγ1‖ + η) ≤ 1 / 128 := by
      simpa only [mul_comm] using hsize
    exact hs'.trans_lt (by norm_num)
  have hbufferStrict : max 2 (Cb * (1 + Dparent)) * ρ < cellA / 64 :=
    hbuffer.trans_lt (by nlinarith only [cellA_pos])
  dsimp only
  intro N hN S hS X hX hweighted hcur e he
  have hAmp (k : ℕ) : 0 < ampScale A₀ b k := div_pos hA (pow_pos hbR k)
  let entrance := e / ampScale A₀ b N
  let Hparent := entrance + Dparent / ampScale A₀ b (N - 1)
  have hentrance : 0 < entrance := div_pos he.1 (hAmp N)
  have hentranceCap : entrance ≤ Dcap / ampScale A₀ b N :=
    div_le_div_of_nonneg_right he.2 (hAmp N).le
  have hclock : ampScale A₀ b N * entrance = e := by
    dsimp only [entrance]
    field_simp [(hAmp N).ne']
  have hstep : ampScale A₀ b N = ampScale A₀ b (N - 1) / b := by
    simpa only [Nat.sub_add_cancel (show 1 ≤ N by omega)] using
      ampScale_succ_eq_div A₀ b (N - 1)
  have hparentTime : Dparent / ampScale A₀ b (N - 1) = Dobs / ampScale A₀ b N := by
    rw [hstep]
    dsimp only [Dparent]
    field_simp [(hAmp (N - 1)).ne', hbR.ne'] <;> ring
  have hpown : (b : ℝ) ^ N ≤ b := by
    simpa only [pow_one] using pow_le_pow_of_le_one hbR.le hb1.le (show 1 ≤ N by omega)
  have hpow2 : 2 * (b : ℝ) ^ N ≤ 1 := by
    have hbq : (b : ℝ) < 1 / 4 := hbquarter
    linarith only [hpown, hbq]
  have htarget : Hparent < T := by
    calc
      _ = (e + Dobs) / ampScale A₀ b N := by dsimp only [Hparent, entrance]; rw [hparentTime, add_div]
      _ ≤ (2 * Dcap) / ampScale A₀ b N :=
        div_le_div_of_nonneg_right (by linarith only [he.2, hDobsCap]) (hAmp N).le
      _ = (Dcap / A₀) * (2 * (b : ℝ) ^ N) := by
        unfold ampScale
        field_simp [hA.ne', (pow_pos hbR N).ne'] <;> ring
      _ ≤ Dcap / A₀ := mul_le_of_le_one_right (div_nonneg hDcap.le hA.le) hpow2
      _ < T := htime
  have hXshort := hX.mono hentranceCap
  have hweightedShort : ∀ u ∈ Icc (0 : ℝ) (ampScale A₀ b N * entrance),
      weightedFamilyNorm h N (canonicalPrefixStageDeviation hγ hγ1 A₀ b ρ ρ N 0 X u) ≤ 1 := by
    rw [hclock]
    intro u hu
    exact hweighted u ⟨hu.1, hu.2.trans he.2⟩
  have hcurShort : ∀ u ∈ Icc (0 : ℝ) (ampScale A₀ b N * entrance),
      ‖canonicalPrefixStageDeviation hγ hγ1 A₀ b ρ ρ N 0 X u N‖ ≤ η := by
    rw [hclock]
    intro u hu
    exact hcur u ⟨hu.1, hu.2.trans he.2⟩
  have hancientNorm : ‖P.ancient s - littleCircularReference hγ hγ1‖ ≤ η := by
    have ht := hcur 0 ⟨le_rfl, hDcap.le⟩
    rw [← norm_canonicalPrefixAlignedCurrentCell_sub_reference hγ hγ1 A₀ b ρ ρ N 0 0 X,
      P.actualCanonicalPrefix_initial_aligned_deepest hρ hρ N S X hX,
      littleCircularMaterialContours_zero] at ht
    exact ht
  have hancient (i : Fin 2) :
      ‖(P.ancient s i).val - circularReferenceC1 hγ hγ1 i‖ ≤ η :=
    (norm_le_pi_norm (P.ancient s - littleCircularReference hγ hγ1) i).trans hancientNorm
  have hdeeper : ∀ t ∈ Icc (0 : ℝ) entrance,
      ∀ z ∈ P.finiteInnerActiveInitialLabels s A₀ b ρ ρ N N,
      ‖S.forward t z - torusCenter‖ ≤ 2 * radScale ρ ρ N := by
    intro t ht z hz
    rw [P.finiteInnerActiveInitialLabels_deepest] at hz
    exact (Set.notMem_empty z hz).elim
  have hwindow' := hwindowξ (s := s) (A₀ := A₀) (R := ρ) (q := q) (T := T)
    (Hglob := T) (a := 1 / 16) (d := d) (entrance := entrance)
    hs hA hρ hq hqE hρhalf le_rfl hρ1 hρbhalf hρsmall hρsq hρcore hsepU hsepL
    hh1 (by change (2 * ρ ^ 6) * 2 ≤ min rw η; nlinarith only [hhboot])
    (by simpa only [mul_one] using hhη) hζ hβ hν hCtRw
    le_rfl (hdriftFor CgeoWin hWinC) hdR hdR hρchartStrict le_rfl hd
    (by convert hgeom using 1 <;> norm_num) hsizeStrict hentrance hancient
    houter hcubicξ (by simpa only [mul_assoc, mul_comm, mul_left_comm] using hinnerCore)
    (by simpa only [mul_assoc, mul_comm, mul_left_comm] using hinnerChart)
    (by simpa only [pow_two, mul_assoc, mul_comm, mul_left_comm] using hchart)
    (by simpa only [mul_assoc, mul_comm, mul_left_comm] using hsep) hbufferStrict
    N N hN le_rfl htarget S hS X hXshort hweightedShort hcurShort hdeeper
  obtain ⟨Y, hY, hweightedY, hcurY, hparticlesY⟩ := hwindow'
  have hparticlesPast : ∀ t ∈ Icc (0 : ℝ) entrance,
      ∀ z ∈ P.finiteInnerActiveInitialLabels s A₀ b ρ ρ N (N - 1),
      ‖S.forward t z - torusCenter‖ ≤ 2 * ρ * radScale ρ ρ (N - 1) := by
    intro t ht
    let τold := ampScale A₀ b N * t
    have htX : t ∈ Icc (0 : ℝ) (Dcap / ampScale A₀ b N) := ⟨ht.1, ht.2.trans hentranceCap⟩
    have htT : t ∈ Icc (0 : ℝ) T := ⟨ht.1, htX.2.trans (by
      have hp : (b : ℝ) ^ N ≤ 1 := pow_le_one₀ hbR.le hb1.le
      have hAmpN : A₀ ≤ ampScale A₀ b N := by
        apply (le_div_iff₀ (pow_pos hbR N)).mpr
        exact mul_le_of_le_one_right hA.le hp
      exact (div_le_div_of_nonneg_left hDcap.le hA hAmpN).trans htime.le)⟩
    have hτold : τold ∈ Icc (0 : ℝ) Dcap := by
      have hm := mul_le_mul_of_nonneg_left ht.2 (hAmp N).le
      rw [hclock] at hm
      exact ⟨mul_nonneg (hAmp N).le ht.1, hm.trans he.2⟩
    have hclockOld : physicalTimeFromNormalized (ampScale A₀ b N) 0 τold = t := by
      simp only [τold, physicalTimeFromNormalized, zero_add, mul_div_cancel_left₀ t (hAmp N).ne']
    let Z := canonicalPrefixAbsoluteFamily A₀ b ρ ρ N 0 X τold
    let u : ℕ → ℝ := fun l => ampScale A₀ b l * 0 + (b : ℝ) ^ (N - l) * τold
    let φ : ℕ → ℝ := fun l => t * finiteAncestorAngularVelocity A₀ b l
    obtain ⟨G, _hG, _hownq⟩ := hmaterial (core := core) (δ := η) (C₀ := 2) (K := 1)
      hs hA.le hbR hρ hρhalf hρ hρ1 hρb hq hqE le_rfl (hdriftFor Cmaterial hMaterialC)
      hdRquarter (div_nonneg hDcap.le (hAmp N).le) le_rfl S hS X hX t htX
      hηquarter hcorei (by norm_num) hh1 (by norm_num) (by simpa only [mul_one] using hhη)
      Z u φ (hweighted τold hτold) (hcur τold hτold) (by
        intro p
        have heq := congrArg (fun V : Fin 2 → LittleContourSpace γ => (V p.2).val)
          (canonicalPrefixAbsoluteCell_raw (A₀ := A₀) (b := (b : ℝ)) hρ hρ N 0 τold X p.1)
        rw [hclockOld] at heq
        simpa only [Z, canonicalPrefixAbsoluteFamily, dif_pos (Nat.le_of_lt_succ p.1.isLt), φ,
          Pi.smul_apply] using heq.symm)
    exact P.actual_inner_particle_radius_reset hs hρ hρhalf hρ hρ1 hN le_rfl htT G (hdeeper t ht)
  refine ⟨Y, hY, hweightedY, hcurY, hparticlesY, hparticlesPast, ?_⟩
  intro t ht
  let τold := ampScale A₀ b N * t
  let τnew := ampScale A₀ b (N - 1) * t
  have htX : t ∈ Icc (0 : ℝ) (Dcap / ampScale A₀ b N) := ⟨ht.1, ht.2.trans hentranceCap⟩
  have hentranceH : entrance ≤ Hparent := le_add_of_nonneg_right (div_nonneg hDparent.le (hAmp _).le)
  have htY : t ∈ Icc (0 : ℝ) Hparent := ⟨ht.1, ht.2.trans hentranceH⟩
  have hτold : τold ∈ Icc (0 : ℝ) Dcap := by
    have hm := mul_le_mul_of_nonneg_left ht.2 (hAmp N).le
    rw [hclock] at hm
    exact ⟨mul_nonneg (hAmp N).le ht.1, hm.trans he.2⟩
  have hclockOld : physicalTimeFromNormalized (ampScale A₀ b N) 0 τold = t := by
    simp only [τold, physicalTimeFromNormalized, zero_add, mul_div_cancel_left₀ t (hAmp N).ne']
  have hclockNew : physicalTimeFromNormalized (ampScale A₀ b (N - 1)) 0 τnew = t := by
    simp only [τnew, physicalTimeFromNormalized, zero_add, mul_div_cancel_left₀ t (hAmp _).ne']
  have hr := hreset hs hA hbR hρ hρhalf hρ hρ1 hρb hq hqE le_rfl
    (hdriftFor Creset hResetC) hdRquarter N N hN le_rfl S hX hY t htX htY
    0 τold 0 τnew hclockOld hclockNew hh (hweighted τold hτold)
  simpa only [one_mul] using hr

end CircularMaterialTransferProfile
end Euler2D

end
