module

public import RequestProject.Euler.CircularActualDeepestMatchedFamily
public import RequestProject.Euler.CircularControlledLookbackCapture
public import RequestProject.Euler.CircularCanonicalMomentHistory
public import RequestProject.Euler.CircularCanonicalPrefixConstraints
public import RequestProject.Euler.CircularActualCanonicalSectionMatching

/-! At the genuine first co-rotated section, the same finite Euler
trajectory is close to one fixed negative-time section of the original
ancient profile. The canonical section and error coefficient precede
the shrinking scale and every finite cutoff. -/

@[expose] public section

set_option maxHeartbeats 32000000
set_option maxRecDepth 7500

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

attribute [local instance 2000] rigidGaugeLittle_group rigidGaugeLittle_space rigidGaugeFamily_tower
attribute [local instance 2000] captureBlockTangent_group captureBlockTangent_space
  captureBlockTangent_continuousAdd captureBlockEndo_monoid captureBlockTangent_complete
attribute [local instance] LittleContourSpace.complexScalarNormedSpace LittleContourSpace.complexScalarTower
attribute [local instance 2000] valueScalarC1_group valueScalarC1_space
attribute [local instance] ContourC1Space.complexScalarNormedSpace ContourC1Space.complexScalarTower
attribute [local irreducible] contourC1GraphSubmodule holderGraphSubmodule circularCoRotationCLM
  circularConstrainedTangentSubmodule circularConstrainedUnstableProjectionCLM
  circularConstrainedReturnMap circularConstrainedChart circularConstraintProjectionToTangentCLM
  circularBanachField circularBanachDomain

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

def HasActualDeepestMatchedLookbackFamilyAt {q T : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q)
    (b : ℝ≥0) (s : ℝ) (hs : s ≤ 0) (A₀ D δ sCanon ηctrl Lback Henv Chistory Cmatch ξ : ℝ) : Prop :=
  let ρ := Real.exp (-ξ)
  let hρ := Real.exp_pos (-ξ)
  ρ ≤ 1 / 2 ∧ ρ ^ 2 < (b : ℝ) ^ q ∧
  ∀ N : ℕ, D / ampScale A₀ b N < T ∧
    let f := finiteBaseCurlL2 (A₀ := A₀) (b := (b : ℝ)) (ρ := ρ) hρ hρ hq hqE
      (P.finiteBaseLp (A₀ := A₀) (b := (b : ℝ)) (ρ := ρ) (q := q) hs hρ hρ) N
    ∃ S : BoundedEulerParticleSystem f T,
      IsFourfoldBoundedEulerParticleSystem S ∧
      IsWeakEulerSolution T (biotSavartL2 f) (particleVelocity f S.backward S.backward_area) ∧
      (∀ t ∈ Icc (0 : ℝ) T, MeasurePreserving (S.forward t) volume volume ∧
        MeasurePreserving (S.backward t) volume volume) ∧
      ∃ X : ℝ → FiniteCircularIndex N → LittleContourSpace γ,
        P.ActualCanonicalPrefixTrajectory s A₀ b ρ ρ (1 / 16) T hρ hρ le_rfl S
          (D / ampScale A₀ b N) X ∧
        (∀ τ ∈ Icc (0 : ℝ) D,
          weightedFamilyNorm (2 * ρ ^ 6) N
            (canonicalPrefixStageDeviation hγ hγ1 A₀ b ρ ρ N 0 X τ) ≤ 1) ∧
        (∀ τ ∈ Icc (0 : ℝ) D,
          ‖canonicalPrefixStageDeviation hγ hγ1 A₀ b ρ ρ N 0 X τ N‖ ≤ ηctrl) ∧
        (∀ u ∈ Icc (0 : ℝ) D,
          ‖canonicalPrefixAlignedCurrentCell A₀ b ρ ρ N 0 X u - littleCircularMaterialContours hγ hγ1 u‖ ≤
            Henv * ‖circularConstrainedUnstableProjectionCLM hγ hγ1.le
              (circularConstraintProjectionToTangentCLM hγ hγ1.le
                (P.ancient s - littleCircularReference hγ hγ1))‖ * Real.exp (sigma * u)) ∧
        ∃ τ ∈ Ioc (0 : ℝ) D, Lback < τ ∧ ∃ angle : ℝ,
          let y := canonicalPrefixAlignedCurrentCell A₀ b ρ ρ N 0 X
          ‖circularConstrainedUnstableProjectionCLM hγ hγ1.le
            (circularConstraintProjectionToTangentCLM hγ hγ1.le
              (circularCoRotationCLM γ τ (y τ) - littleCircularReference hγ hγ1))‖ = δ ∧
          (∀ u ∈ Ico (0 : ℝ) τ,
            ‖circularConstrainedUnstableProjectionCLM hγ hγ1.le
              (circularConstraintProjectionToTangentCLM hγ hγ1.le
                (circularCoRotationCLM γ u (y u) - littleCircularReference hγ hγ1))‖ < δ) ∧
          (∀ u ∈ Icc (0 : ℝ) τ,
            ‖y u - littleCircularMaterialContours hγ hγ1 u‖ ≤ ηctrl * Real.exp (-sigma * (τ - u))) ∧
          (∀ u ∈ Icc (0 : ℝ) τ,
            let t := physicalTimeFromNormalized (ampScale A₀ b N) 0 u;
            ‖momentN (boxedComplexDensity
              (S.transportedScalar (P.finitePeriodicLabel s A₀ b ρ ρ N N) t)) 4‖ ≤
              ampScale A₀ b N * radScale ρ ρ N ^ 6 * Chistory * ηctrl *
                Real.exp (-sigma * (τ - u))) ∧
          ‖circularCoRotationCLM γ τ (y τ) -
            contourRotationFamilyLittleCLM γ angle
              (circularCoRotationCLM γ sCanon (P.ancient sCanon))‖ ≤ Cmatch * ρ ^ 3

theorem exists_actual_deepest_matched_family_with_prescribed_lookback {Rflow r₀ : ℝ}
    (hRflow : 0 < Rflow) (hr₀ : 0 < r₀)
    {Y : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hY : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) Rflow) period Y)
    (hd : ContDiffAt ℝ 2 (fun W => Y W period) (littleCircularReference hγ hγ1))
    (hfix : Y (littleCircularReference hγ hγ1) period = littleCircularReference hγ hγ1)
    (harea : ∀ W ∈ ball (littleCircularReference hγ hγ1) Rflow, ∀ i,
      littleContourArea γ (Y W period i) = littleContourArea γ (W i))
    {gseq : CircularConstrainedTangentSpace γ → ℕ → CircularConstrainedTangentSpace γ}
    (hg : IsLocalWeightedBackwardGraph
      (banachDoubleReturn (circularConstrainedReturnMap hγ hγ1 (fun W => Y W period)))
      (circularConstrainedUnstableProjectionCLM hγ hγ1.le) circularAncientBackwardWeight r₀ gseq)
    (hsamples : ∃ N : ℕ, ∀ n ≥ N, ∃ α : CircularConstrainedTangentSpace γ,
      circularConstrainedUnstableProjectionCLM hγ hγ1.le α = α ∧ ‖α‖ ≤ r₀ / 2 ∧
      P.ancient (-(n : ℝ) * (period + period)) = circularConstrainedChart hγ hγ1 (gseq α 0))
    {q T : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q) (hT : 0 < T)
    (ηctrl Kextra : ℝ) (hηctrl : 0 < ηctrl) (hKextra : 0 ≤ Kextra) :
    ∃ b : ℝ≥0, 0 < b ∧ b < 1 / 4 ∧
      bilateral P.moment (((b : ℝ) : ℂ) * (sigma + 5 / 4 * I)) ≠ 0 ∧
      (b : ℝ) * Kextra + (b : ℝ) *
        (finiteInnerLabelLittleRowCoefficient (γ : ℝ) (cellA / 2)
          (circularCanonicalCellNormBudget hγ hγ1) / (2 - 1)) < sigma / 4 ∧
      ∃ δ > 0, ∃ sCanon < 0, ‖P.coRotatedAncientGraphBase sCanon‖ = δ ∧ ∃ Henv > 0, ∃ Chistory > 0,
        ∀ Lback : ℝ, ∀ seedMax > 0, ∀ nMin : ℕ, ∃ n ≥ nMin,
          let s := -(n : ℝ) * (period + period);
          ∃ hs : s ≤ 0, ∃ A₀ > 0, ∃ D > 0, ∃ Cmatch > 0,
            ‖circularConstrainedUnstableProjectionCLM hγ hγ1.le
              (circularConstraintProjectionToTangentCLM hγ hγ1.le
                (P.ancient s - littleCircularReference hγ hγ1))‖ < seedMax ∧
            Henv * ‖circularConstrainedUnstableProjectionCLM hγ hγ1.le
              (circularConstraintProjectionToTangentCLM hγ hγ1.le
                (P.ancient s - littleCircularReference hγ hγ1))‖ * Real.exp (sigma * D) ≤ ηctrl ∧
            ∀ᶠ ξ : ℝ in atTop,
              P.HasActualDeepestMatchedLookbackFamilyAt (T := T) hq hqE
                b s hs A₀ D δ sCanon ηctrl Lback Henv Chistory Cmatch ξ := by
  obtain ⟨Cgeo, hCgeo, hconstraints⟩ := P.exists_uniform_actualCanonical_prefix_constraints
  obtain ⟨CgeoMoment, hCgeoMoment, hidentity⟩ :=
    P.exists_uniform_actualCanonical_instantaneous_boxed_moment
  obtain ⟨Cm, hCm, rm, hrm, hboundary⟩ :=
    exists_circularBoundaryFourthMoment_moving_reference_bound hγ hγ1
  obtain ⟨dmatch, hdmatch, _hdmatchr, ε, hε, C, hC, hmatch⟩ :=
    P.exists_actual_same_graph_canonical_section_matching hRflow hr₀ hY
      (hd.differentiableAt (by norm_num)) hfix harea hg hsamples
  let εgeom := min ε (min (cellA / 4) (min (2 * ηctrl) (2 * rm)))
  let δctrl := εgeom / 2
  have hεgeom : 0 < εgeom := lt_min hε (lt_min (div_pos cellA_pos (by norm_num)) (by positivity))
  have hδctrl : 0 < δctrl := half_pos hεgeom
  have hδctrlε : δctrl < ε := (half_lt_self hεgeom).trans_le (min_le_left _ _)
  have hδctrla : δctrl ≤ cellA / 4 :=
    (half_le_self hεgeom.le).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδctrlη : δctrl ≤ ηctrl := by
    have he : εgeom ≤ 2 * ηctrl :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    dsimp only [δctrl]
    linarith only [he]
  have hδctrlrm : δctrl ≤ rm := by
    have he : εgeom ≤ 2 * rm :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    dsimp only [δctrl]
    linarith only [he]
  obtain ⟨b, hb, hbquarter, hnonzero, hbaseextra, δ, hδ, hδd, Henv, hHenv, hfamilies⟩ :=
    P.exists_actual_deepest_envelope_family_with_prescribed_lookback hRflow hr₀ hY hd hfix harea
      hg hsamples hq hqE hT dmatch εgeom Kextra hdmatch hεgeom hKextra
  obtain ⟨sCanon, hsCanon, hcanonδ, hcanonical⟩ := hmatch δ ⟨hδ, hδd⟩
  refine ⟨b, hb, hbquarter, hnonzero, hbaseextra, δ, hδ, sCanon, hsCanon, hcanonδ,
    Henv, hHenv, Cm, hCm, ?_⟩
  intro Lback seedMax hseedMax nMin
  obtain ⟨n, hn, hdata⟩ := hfamilies Lback seedMax hseedMax nMin
  dsimp only at hdata
  obtain ⟨hs, A₀, hA, D, hD, Cerror, hCerror, hseed, hterminalEnvelope, hfamily⟩ := hdata
  let s := -(n : ℝ) * (period + period)
  have hterminalControl : Henv * ‖circularConstrainedUnstableProjectionCLM hγ hγ1.le
      (circularConstraintProjectionToTangentCLM hγ hγ1.le
        (P.ancient s - littleCircularReference hγ hγ1))‖ * Real.exp (sigma * D) ≤ ηctrl :=
    hterminalEnvelope.trans hδctrlη
  have hbR : 0 < (b : ℝ) := hb
  let d := 2 + 4 * Cgeo * A₀ * T + 4 * CgeoMoment * A₀ * T
  have hcat : 0 < Cgeo * A₀ * T := mul_pos (mul_pos hCgeo hA) hT
  have hcatMoment : 0 < CgeoMoment * A₀ * T := mul_pos (mul_pos hCgeoMoment hA) hT
  have hdpos : 0 < d := by dsimp only [d]; nlinarith only [hcat, hcatMoment]
  have hρlim : Tendsto (fun ξ : ℝ => Real.exp (-ξ)) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero
  have hhalf : ∀ᶠ ξ : ℝ in atTop, Real.exp (-ξ) ≤ (b : ℝ) / 2 :=
    (hρlim.eventually (gt_mem_nhds (half_pos hbR))).mono (fun _ h => h.le)
  have hdlim : Tendsto (fun ξ : ℝ => d * Real.exp (-ξ)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hρlim.const_mul d
  have hdriftScale : ∀ᶠ ξ : ℝ in atTop, d * Real.exp (-ξ) ≤ 1 / 4 :=
    (hdlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))).mono
      (fun _ h => h.le)
  have hhlim : Tendsto (fun ξ : ℝ => 2 * Real.exp (-ξ) ^ 6) atTop (𝓝 0) := by
    simpa only [zero_pow (by decide : 6 ≠ 0), mul_zero] using (hρlim.pow 6).const_mul 2
  have hweight : ∀ᶠ ξ : ℝ in atTop, 2 * Real.exp (-ξ) ^ 6 ≤ δctrl :=
    (hhlim.eventually (gt_mem_nhds hδctrl)).mono (fun _ h => h.le)
  refine ⟨n, hn, hs, A₀, hA, D, hD, C * Cerror, mul_pos hC hCerror,
    hseed, hterminalControl, ?_⟩
  filter_upwards [hfamily, hhalf, hdriftScale, hweight] with ξ hfamilyξ hρhalf hdR hhK
  let ρ := Real.exp (-ξ)
  have hρ : 0 < ρ := Real.exp_pos (-ξ)
  change ρ ≤ 1 / 2 ∧ ρ ^ 2 < (b : ℝ) ^ q ∧ _ at hfamilyξ
  obtain ⟨hρmax, hlp, hfinite⟩ := hfamilyξ
  have hρone : ρ ≤ 1 := hρmax.trans (by norm_num)
  have hρb : ρ < (b : ℝ) := hρhalf.trans_lt (half_lt_self hbR)
  have hfrac : ρ / b ≤ 1 / 2 := (div_le_iff₀ hbR).mpr (by nlinarith only [hρhalf])
  have hden : 0 < 1 - ρ / b := sub_pos.mpr ((div_lt_one hbR).mpr hρb)
  have hdenHalf : (1 / 2 : ℝ) ≤ 1 - ρ / b := by linarith only [hfrac]
  have hdiv : Cgeo * A₀ / (1 - ρ / b) ≤ 2 * Cgeo * A₀ := by
    calc
      _ ≤ Cgeo * A₀ / (1 / 2) :=
        div_le_div_of_nonneg_left (mul_nonneg hCgeo.le hA.le) (by norm_num) hdenHalf
      _ = _ := by ring
  have hdrift : 5 / 4 + (Cgeo * A₀ / (1 - ρ / b)) * T < d := by
    have hh := mul_le_mul_of_nonneg_right hdiv hT.le
    dsimp only [d]
    nlinarith only [hh, hcat, hcatMoment]
  have hdivMoment : CgeoMoment * A₀ / (1 - ρ / b) ≤ 2 * CgeoMoment * A₀ := by
    calc
      _ ≤ CgeoMoment * A₀ / (1 / 2) :=
        div_le_div_of_nonneg_left (mul_nonneg hCgeoMoment.le hA.le) (by norm_num) hdenHalf
      _ = _ := by ring
  have hdriftMoment : 5 / 4 + (CgeoMoment * A₀ / (1 - ρ / b)) * T < d := by
    have hh := mul_le_mul_of_nonneg_right hdivMoment hT.le
    dsimp only [d]
    nlinarith only [hh, hcat, hcatMoment]
  have hh1 : 2 * ρ ^ 6 ≤ 1 := hhK.trans (hδctrla.trans (by linarith only [cellA_lt_one]))
  have hcorei (i : Fin 2) : cellA / 2 ≤ 3 * circularContourRadii i / 4 := by
    have hi := (circularContourRadii_bounds i).2.1
    linarith only [hi, cellA_pos]
  change ρ ≤ 1 / 2 ∧ ρ ^ 2 < (b : ℝ) ^ q ∧ _
  refine ⟨hρmax, hlp, ?_⟩
  intro N
  obtain ⟨htimeN, S, hS, hweak, hMP, X, hX, hZ, hforward, hnear, hgraph,
    hafter, hcohit, _hmoving⟩ := hfinite N
  have hAN : 0 < ampScale A₀ b N := by unfold ampScale; positivity
  let y := canonicalPrefixAlignedCurrentCell A₀ b ρ ρ N 0 X
  have hancientNorm : ‖P.ancient s - littleCircularReference hγ hγ1‖ ≤ δctrl := by
    have hh := hnear 0 ⟨le_rfl, hD.le⟩
    rw [P.actualCanonicalPrefix_initial_aligned_deepest hρ hρ N S X hX,
      littleCircularMaterialContours_zero] at hh
    exact hh
  have hancient (i : Fin 2) :
      ‖(P.ancient s i).val - circularReferenceC1 hγ hγ1 i‖ ≤ δctrl :=
    (norm_le_pi_norm (P.ancient s - littleCircularReference hγ hγ1) i).trans hancientNorm
  obtain ⟨τ, hτ, hvalue, hbefore⟩ := hcohit
  have hτD : τ ∈ Icc (0 : ℝ) D := ⟨hτ.1.le, hτ.2⟩
  let t := physicalTimeFromNormalized (ampScale A₀ b N) 0 τ
  have ht : t ∈ Icc (0 : ℝ) (D / ampScale A₀ b N) := by
    change 0 ≤ 0 + τ / ampScale A₀ b N ∧ 0 + τ / ampScale A₀ b N ≤ D / ampScale A₀ b N
    simpa only [zero_add] using
      And.intro (div_nonneg hτ.1.le hAN.le) (div_le_div_of_nonneg_right hτ.2 hAN.le)
  have hcur : ‖canonicalPrefixStageDeviation hγ hγ1 A₀ b ρ ρ N 0 X τ N‖ ≤ δctrl := by
    rw [← norm_canonicalPrefixAlignedCurrentCell_sub_reference hγ hγ1 A₀ b ρ ρ N 0 τ X]
    exact hnear τ hτD
  have hc := hconstraints (core := cellA / 2) (δ := δctrl) (η := δctrl) (C₀ := 2) (K := 1)
    hs hA.le hbR hρ hρmax hρ hρone hρb hq hqE le_rfl hdrift hdR
    (div_nonneg hD.le hAN.le) hδctrla hcorei (by norm_num) hh1 (by norm_num)
    (by simpa only [mul_one] using hhK) hδctrl.le hδctrla hancient
    le_rfl S hS X hX t ht 0 τ rfl (hZ τ hτD) hcur
  let Z := circularCoRotationCLM γ τ (y τ)
  have hZnear : Z ∈ ball (littleCircularReference hγ hγ1) ε := by
    apply mem_ball_iff_norm.mpr
    change ‖circularCoRotationCLM γ τ (y τ) - littleCircularReference hγ hγ1‖ < ε
    rw [norm_circularCoRotationCLM_sub_reference hγ hγ1 τ]
    exact (hnear τ hτD).trans_lt hδctrlε
  have hfourZ := circularCoRotationCLM_fourfold τ (y τ) hc.1
  have hareaZ (i : Fin 2) : littleContourArea γ (Z i) = Real.pi * circularContourRadii i ^ 2 :=
    (circularCoRotationCLM_area τ (y τ) i).trans (hc.2 i)
  obtain ⟨angle, _hchart, herr⟩ := hcanonical Z hZnear hfourZ hareaZ hvalue
  have hnearAll (u : ℝ) (hu : u ∈ Icc (0 : ℝ) D) :
      ‖canonicalPrefixStageDeviation hγ hγ1 A₀ b ρ ρ N 0 X u N‖ ≤ ηctrl := by
    rw [← norm_canonicalPrefixAlignedCurrentCell_sub_reference hγ hγ1 A₀ b ρ ρ N 0 u X]
    exact (hnear u hu).trans hδctrlη
  have hτLong : Lback < τ := hafter τ hτD hvalue
  have hterminalExit : Henv * ‖circularConstrainedUnstableProjectionCLM hγ hγ1.le
      (circularConstraintProjectionToTangentCLM hγ hγ1.le
        (P.ancient s - littleCircularReference hγ hγ1))‖ * Real.exp (sigma * τ) ≤ ηctrl :=
    (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hτ.2 sigma_pos.le))
      (mul_nonneg hHenv.le (norm_nonneg _))).trans hterminalControl
  have hhistory (u : ℝ) (hu : u ∈ Icc (0 : ℝ) τ) :
      ‖y u - littleCircularMaterialContours hγ hγ1 u‖ ≤ ηctrl * Real.exp (-sigma * (τ - u)) := by
    have huD : u ∈ Icc (0 : ℝ) D := ⟨hu.1, hu.2.trans hτ.2⟩
    have heq : Real.exp (sigma * τ) * Real.exp (-sigma * (τ - u)) =
        Real.exp (sigma * u) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      _ ≤ Henv * ‖circularConstrainedUnstableProjectionCLM hγ hγ1.le
          (circularConstraintProjectionToTangentCLM hγ hγ1.le
            (P.ancient s - littleCircularReference hγ hγ1))‖ * Real.exp (sigma * u) := hforward u huD
      _ = (Henv * ‖circularConstrainedUnstableProjectionCLM hγ hγ1.le
          (circularConstraintProjectionToTangentCLM hγ hγ1.le
            (P.ancient s - littleCircularReference hγ hγ1))‖ * Real.exp (sigma * τ)) *
              Real.exp (-sigma * (τ - u)) := by simp only [mul_assoc, heq]
      _ ≤ ηctrl * Real.exp (-sigma * (τ - u)) :=
        mul_le_mul_of_nonneg_right hterminalExit (Real.exp_pos _).le
  have hmomentHistory (u : ℝ) (hu : u ∈ Icc (0 : ℝ) τ) :
      let tu := physicalTimeFromNormalized (ampScale A₀ b N) 0 u;
      ‖momentN (boxedComplexDensity
        (S.transportedScalar (P.finitePeriodicLabel s A₀ b ρ ρ N N) tu)) 4‖ ≤
        ampScale A₀ b N * radScale ρ ρ N ^ 6 * Cm * ηctrl * Real.exp (-sigma * (τ - u)) := by
    let tu := physicalTimeFromNormalized (ampScale A₀ b N) 0 u
    have huD : u ∈ Icc (0 : ℝ) D := ⟨hu.1, hu.2.trans hτ.2⟩
    have htu : tu ∈ Icc (0 : ℝ) (D / ampScale A₀ b N) := by
      change 0 ≤ 0 + u / ampScale A₀ b N ∧
        0 + u / ampScale A₀ b N ≤ D / ampScale A₀ b N
      simpa only [zero_add] using
        And.intro (div_nonneg huD.1 hAN.le) (div_le_div_of_nonneg_right huD.2 hAN.le)
    have hid := hidentity hs hA hbR hρ hρmax hρ hρone hρb hq hqE
      le_rfl hdriftMoment hdR N S le_rfl (div_nonneg hD.le hAN.le) X hX tu htu 0 u rfl
    have hm := hboundary u (y u) ((hnear u huD).trans hδctrlrm)
    have hrad : 0 < radScale ρ ρ N := radScale_pos hρ hρ N
    have hphase : ‖Complex.exp (-(4 * (((tu * finiteAncestorAngularVelocity A₀ b N : ℝ) : ℂ)) * I))‖ = 1 := by
      rw [show -(4 * (((tu * finiteAncestorAngularVelocity A₀ b N : ℝ) : ℂ)) * I) =
        ((-(4 * (tu * finiteAncestorAngularVelocity A₀ b N)) : ℝ) : ℂ) * I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I]
    have hnorm : ‖momentN (boxedComplexDensity
        (S.transportedScalar (P.finitePeriodicLabel s A₀ b ρ ρ N N) tu)) 4‖ =
        ampScale A₀ b N * radScale ρ ρ N ^ 6 * ‖circularBoundaryFourthMoment (y u)‖ := by
      rw [hid, norm_mul, norm_mul, norm_mul, norm_pow, hphase]
      simp only [y, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hAN, abs_of_pos hrad, mul_one]
    change ‖momentN (boxedComplexDensity
      (S.transportedScalar (P.finitePeriodicLabel s A₀ b ρ ρ N N) tu)) 4‖ ≤ _
    rw [hnorm]
    calc
      _ ≤ ampScale A₀ b N * radScale ρ ρ N ^ 6 *
          (Cm * ‖y u - littleCircularMaterialContours hγ hγ1 u‖) :=
        mul_le_mul_of_nonneg_left hm (by positivity)
      _ ≤ ampScale A₀ b N * radScale ρ ρ N ^ 6 *
          (Cm * (ηctrl * Real.exp (-sigma * (τ - u)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hhistory u hu) hCm.le) (by positivity)
      _ = _ := by ring
  refine ⟨htimeN, S, hS, hweak, hMP, X, hX, hZ, hnearAll, hforward,
    τ, hτ, hτLong, angle, hvalue, hbefore, hhistory, hmomentHistory, ?_⟩
  simpa only [mul_assoc] using
    herr.trans (mul_le_mul_of_nonneg_left (hgraph τ hτD) hC.le)

end CircularMaterialTransferProfile
end Euler2D

end

