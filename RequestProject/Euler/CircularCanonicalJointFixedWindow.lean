module

public import RequestProject.Euler.CircularCanonicalStoppedFixedWindow
public import RequestProject.Euler.CircularCanonicalWeightedFixedWindow
public import RequestProject.Euler.CircularCanonicalContinuousControls

/-! The actual fixed-window current and ancestor estimates close
together by a continuous joint first-exit argument. The resulting
O(h) controls do not assume a nonzero growing seed or future bounds. -/

@[expose] public section

set_option maxHeartbeats 32000000
set_option maxRecDepth 7500

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

attribute [local instance 2000] rigidGaugeLittle_group rigidGaugeLittle_space rigidGaugeFamily_tower
attribute [local instance] LittleContourSpace.complexScalarNormedSpace LittleContourSpace.complexScalarTower

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_uniform_actualCanonical_joint_fixed_window_bound :
    let L := circularCanonicalCellNormBudget hγ hγ1
    ∃ Kself : ℝ≥0, 0 < Kself ∧ ∃ rw > 0, ∃ Ctw > 0,
      ∀ b : ℝ≥0, 0 < b → b < 1 →
      ∀ {Cw D C₀ Lseed δ νbar Kboot : ℝ},
      0 ≤ Cw → 0 < D → 2 ≤ C₀ → 0 ≤ Lseed → 0 < δ → δ ≤ cellA / 4 → 0 < Kboot →
      ∃ Cgeo Ctc Cdc Cr Kr Ccur Cobs : ℝ,
      0 < Cgeo ∧ 0 < Ctc ∧ 0 < Cdc ∧ 0 < Cr ∧ 0 < Kr ∧ 0 < Ccur ∧ 0 < Cobs ∧
      let Cb := radialStageRadiusConstant Cr Cw b
      ∀ {core : ℝ}, 0 < core → (∀ i, core ≤ 3 * circularContourRadii i / 4) →
      ∀ᶠ ξ : ℝ in atTop,
      let ρ := Real.exp (-ξ)
      let h := C₀ * ρ ^ 6
      ∀ {s A₀ R q T Hglob a d Dphys entrance Dcap η : ℝ},
      ∀ [Fact (1 ≤ ENNReal.ofReal q)] (hs : s ≤ 0) (hA : 0 < A₀)
        (hR : 0 < R) (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q),
      let Cu := finiteInnerLabelLittleRowCoefficient (γ : ℝ) (cellA / 2) L
      let Cl := finiteOuterLabelLittleRowCoefficient (γ : ℝ) core L L
      let CtRw := Ctw * finiteTorusLabelLittleRowCoefficient (γ : ℝ) L * R ^ 8
      let β := 3 * CtRw + weightedInteractionRowFeedback b Cu Cl C₀ ρ
      R ≤ 1 / 2 → R ≤ ρ → ρ ≤ 1 → ρ ≤ b / 2 → ρ ^ 2 ≤ b / 2 →
      (5 / 4 : ℝ) * ρ ≤ cellA → 10 * ρ ≤ cellA / 2 → 8 * L * ρ ≤ core →
      h ≤ 1 → h * Kboot ≤ min rw δ → C₀ * ρ ^ 8 ≤ 1 / 2 →
      0 ≤ β → ((b * Kself : ℝ≥0) : ℝ) + β ≤ νbar → CtRw ≤ 1 →
      Hglob ≤ T → 5 / 4 + (Cgeo * A₀ / (1 - ρ / b)) * Hglob < d → d * R ≤ 1 / 16 →
      0 < a → a ≤ 1 / 16 → 0 < d → (5 / 4 : ℝ) * R ≤ a → (L + 1) * R ≤ a / 2 →
      0 ≤ Dphys → 0 ≤ entrance → 0 ≤ Dcap → Dcap ≤ D →
      0 ≤ η → η ≤ cellA / 4 → (∀ i, ‖(P.ancient s i).val - circularReferenceC1 hγ hγ1 i‖ ≤ η) →
      (2 * (b : ℝ) * C₀ * Kboot * (Cl + Ctc * finiteTorusLabelLittleRowCoefficient (γ : ℝ) L)) * ρ ^ 2 ≤ 1 →
      b * finiteEulerUniformRadialCoefficient Kr b R ρ core d δ * Cb ^ 3 *
        ρ ^ 2 * (1 + D) ^ 3 ≤ Cr / 2 →
      Cb * ρ * (1 + D) ≤ core / 2 → Cb * ρ * (1 + D) ≤ d →
      Cb * ρ * R * (1 + D) ≤ a → 8 * (Cb * ρ * (1 + D)) ≤ cellA / 2 →
      ∀ (N k : ℕ) (hkN : k ≤ N), entrance + Dcap / ampScale A₀ b k ≤ Dphys →
      ∀ S : BoundedEulerParticleSystem
        (finiteBaseCurlL2 (A₀ := A₀) (b := (b : ℝ)) (ρ := ρ) hR (Real.exp_pos (-ξ)) hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := (b : ℝ)) (ρ := ρ) (q := q) hs hR (Real.exp_pos (-ξ))) N) T,
      IsFourfoldBoundedEulerParticleSystem S →
      ∀ X : ℝ → FiniteCircularIndex k → LittleContourSpace γ,
      IsBanachTimeDomainTrajectoryOn
        (S.actualPartialPhaseField (P.finiteInnerInitialLabel s A₀ b R ρ N k) hγ hγ1
          (finiteCircularReferenceC1 hγ hγ1 R ρ) (finiteCircularInterfaceRadius R ρ)
          (finiteCircularInterfaceRadius_pos hR (Real.exp_pos (-ξ)))
          (lift_finiteCircularReferenceC1 hγ hγ1 R ρ) (finiteCircularInterfaceStrength A₀ b))
        (S.actualPartialPhaseDomain (P.finiteInnerInitialLabel s A₀ b R ρ N k)
          (finiteCircularReferenceC1 hγ hγ1 R ρ) (finiteCircularInterfaceRadius R ρ) a Hglob)
        (fun p => finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N (finiteCircularPrefixIndex hkN p)) Dphys X →
      let x := canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance X
      weightedFamilyNorm h k (x 0) ≤ Lseed * h → ‖x 0 k‖ ≤ Lseed * h →
      (∀ z ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N k,
        ‖S.forward entrance z - torusCenter‖ ≤ Cw * ρ * radScale R ρ k) →
      (∀ τ ∈ Icc (0 : ℝ) Dcap, weightedFamilyNorm h k (x τ) ≤ Cobs * h) ∧
      (∀ τ ∈ Icc (0 : ℝ) Dcap, ‖x τ k‖ ≤ Ccur * h) ∧
      ∀ τ ∈ Icc (0 : ℝ) Dcap, ∀ z ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N k,
        ‖S.forward (physicalTimeFromNormalized (ampScale A₀ b k) entrance τ) z - torusCenter‖ ≤
          Cb * ρ * radScale R ρ k * (1 + τ) := by
  dsimp only
  obtain ⟨Kself, hKself, rw, hrw, Cwgeo, Ctw, Cdw, hCwgeo, hCtw, hCdw, hweighted⟩ :=
    P.exists_uniform_actualCanonical_weighted_fixed_window_bound
  refine ⟨Kself, hKself, rw, hrw, Ctw, hCtw, ?_⟩
  intro b hb hb1 Cw D C₀ Lseed δ νbar Kboot hCw hD hC₀ hLseed hδ hδa hKboot
  have hbR : 0 < (b : ℝ) := hb
  have hbR1 : (b : ℝ) < 1 := hb1
  obtain ⟨Ccgeo, Ctc, Cdc, Cr, Kr, Ccur, hCcgeo, hCtc, hCdc, hCr, hKr, hCcur, hcurrent⟩ :=
    P.exists_uniform_actualCanonical_stopped_fixed_window_bound hbR hbR1 hCw hD hC₀ hLseed hδ hδa
  let L := circularCanonicalCellNormBudget hγ hγ1
  let Cb := radialStageRadiusConstant Cr Cw b
  let Cgeo := max Ccgeo Cwgeo
  let Cu := finiteInnerLabelLittleRowCoefficient (γ : ℝ) (cellA / 2) L
  let Cpoly := finitePrefixUniformDeepCoefficient (γ : ℝ) (cellA / 2) L Cdw Cb b
  let F := ((Cu + 1) / C₀) * Ccur + Cpoly * (1 + D) ^ 4
  let Cobs := (Lseed + F * D) * Real.exp (νbar * D) + 1
  have hCb : 0 < Cb := radialStageRadiusConstant_pos hCr hCw hbR hbR1
  have hL : 0 < L := circularCanonicalCellNormBudget_pos hγ hγ1
  have hcauchy : 0 ≤ cauchyContourNormBudget 5 (γ : ℝ) 1 (cellA / 2) L :=
    (cauchySpatialDerivativeBudget_nonneg 5 (by norm_num : (0 : ℝ) ≤ 1)
      (half_pos cellA_pos) 0).trans (le_max_left _ _)
  have hweight : 0 ≤ circularRadialPerturbationWeight :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (circularContourRadii_bounds i).1.le)
  have hCu : 0 ≤ Cu := by unfold Cu finiteInnerLabelLittleRowCoefficient; positivity
  have hCpoly : 0 ≤ Cpoly := by
    have htor : 0 ≤ torusCorrectionContourBudget (γ : ℝ) L := by unfold torusCorrectionContourBudget; positivity
    unfold Cpoly finitePrefixUniformDeepCoefficient
    positivity [finiteLabelMassBound_nonneg]
  have hF : 0 ≤ F := by dsimp only [F]; positivity
  have hCobs : 0 < Cobs := by dsimp only [Cobs]; positivity
  have hsmall (A : ℝ) {B : ℝ} (hB : 0 < B) :
      ∀ᶠ ξ : ℝ in atTop, A * (C₀ * Real.exp (-ξ) ^ 6) < B := by
    have he : Tendsto (fun ξ : ℝ => A * (C₀ * Real.exp (-ξ) ^ 6)) atTop (𝓝 0) := by
      simpa only [zero_pow (by decide : (6 : ℕ) ≠ 0), mul_zero] using
        ((Real.tendsto_exp_neg_atTop_nhds_zero.pow 6).const_mul C₀).const_mul A
    exact he.eventually (gt_mem_nhds hB)
  refine ⟨Cgeo, Ctc, Cdc, Cr, Kr, Ccur, Cobs, hCcgeo.trans_le (le_max_left _ _), hCtc, hCdc,
    hCr, hKr, hCcur, hCobs, ?_⟩
  intro core hcore hcorei
  filter_upwards [hcurrent, hsmall Cobs hKboot, hsmall Ccur hδ, hsmall Lseed (lt_min hKboot hδ)] with
    ξ hξ hobsSmall hcurSmall hinitSmall
  try dsimp only
  let ρ := Real.exp (-ξ)
  let h := C₀ * ρ ^ 6
  intro s A₀ R q T Hglob a d Dphys entrance Dcap η _ hs hA hR hq hqE
    hRmax hRρ hρ1 hρhalf hhalf hρcore hsepU hsepL hh1 hhK hζ hβ hνup hCtRw
    hglobT hdrift hdR ha ha16 hdpos hRchart hgeom hDphys he hDcap hcapD
    hη hηa hancient houter hcubic hinnerCore hinnerChart hchart hsep N k hkN htimeEnd S hS X hX
    hinitZ hinitCur hstart
  let Cl := finiteOuterLabelLittleRowCoefficient (γ : ℝ) core L L
  let CtRw := Ctw * finiteTorusLabelLittleRowCoefficient (γ : ℝ) L * R ^ 8
  let β := 3 * CtRw + weightedInteractionRowFeedback b Cu Cl C₀ ρ
  let x := canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance X
  have hρ : 0 < ρ := Real.exp_pos _
  have hh : 0 < h := by dsimp only [h]; positivity
  have hρb : ρ < (b : ℝ) := hρhalf.trans_lt (by linarith only [hbR])
  have hden : 0 < 1 - ρ / b := sub_pos.mpr ((div_lt_one hbR).mpr hρb)
  have hAk : 0 < ampScale A₀ b k := by unfold ampScale; positivity
  have hHglob : 0 ≤ Hglob := (hX.mem 0 ⟨le_rfl, hDphys⟩).1.2
  have hdriftFor (C₁ : ℝ) (hC₁ : C₁ ≤ Cgeo) :
      5 / 4 + (C₁ * A₀ / (1 - ρ / b)) * Hglob < d :=
    (add_le_add le_rfl (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hC₁ hA.le) hden.le) hHglob)).trans_lt hdrift
  have hrk : radScale R ρ k ≤ R := mul_le_of_le_one_right hR.le (pow_le_one₀ hρ.le hρ1)
  have hgeomk : (L + 1) * radScale R ρ k ≤ a / 2 :=
    (mul_le_mul_of_nonneg_left hrk (by linarith only [hL])).trans hgeom
  have hsmallρ : ρ ^ 2 < (b : ℝ) := hhalf.trans_lt (by linarith only [hbR])
  have houterb : (b : ℝ) * ρ ^ 2 < 1 :=
    (mul_le_of_le_one_right hbR.le (pow_le_one₀ hρ.le hρ1)).trans_lt hbR1
  have hdenMass : 0 < 1 - ρ ^ 2 / b := sub_pos.mpr ((div_lt_one hbR).mpr hsmallρ)
  have hmass : 0 ≤ circularFiniteL1Coefficient b ρ := by
    unfold circularFiniteL1Coefficient finiteContourPatchMassBound
    exact add_nonneg (div_nonneg ENNReal.toReal_nonneg hdenMass.le)
      (Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) measureReal_nonneg))
  have hcoef : 0 ≤ (b : ℝ) * finiteEulerUniformRadialCoefficient Kr b R ρ core d δ * Cb ^ 3 * ρ ^ 2 := by
    unfold finiteEulerUniformRadialCoefficient
    positivity [sub_pos.mpr houterb]
  have hcubicSub (u : ℝ) (hu : u ∈ Icc (0 : ℝ) Dcap) :
      (b : ℝ) * finiteEulerUniformRadialCoefficient Kr b R ρ core d δ * Cb ^ 3 * ρ ^ 2 * (1 + u) ^ 3 ≤ Cr / 2 :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith only [hu.1])
      (add_le_add le_rfl (hu.2.trans hcapD)) 3) hcoef).trans hcubic
  have hclockSub (u : ℝ) (hu : u ≤ D) : Cb * ρ * (1 + u) ≤ Cb * ρ * (1 + D) :=
    mul_le_mul_of_nonneg_left (add_le_add le_rfl hu) (mul_nonneg hCb.le hρ.le)
  have hchartSub (u : ℝ) (hu : u ≤ D) : Cb * ρ * R * (1 + u) ≤ a :=
    (mul_le_mul_of_nonneg_left (add_le_add le_rfl hu) (by positivity)).trans hchart
  have htimeSub (u : ℝ) (hu : u ≤ Dcap) : entrance + u / ampScale A₀ b k ≤ Dphys :=
    (add_le_add le_rfl (div_le_div_of_nonneg_right hu hAk.le)).trans htimeEnd
  have hcurrentOn (u : ℝ) (hu : u ∈ Icc (0 : ℝ) Dcap)
      (hZ : ∀ τ ∈ Icc (0 : ℝ) u, weightedFamilyNorm h k (x τ) ≤ Kboot)
      (hcur : ∀ τ ∈ Icc (0 : ℝ) u, ‖x τ k‖ ≤ δ) :=
    hξ hs hA hR hq hqE hRmax hRρ hρ1 hρhalf hglobT
      (hdriftFor Ccgeo (le_max_left _ _)) hdR ha ha16 hcore hdpos hDphys he hu.1 (hu.2.trans hcapD)
      hhalf hρcore hcorei hη hηa hancient hKboot.le hh1 (hhK.trans (min_le_right _ _)) hζ hsepL hRchart houter
      (hcubicSub u hu) ((hclockSub u (hu.2.trans hcapD)).trans hinnerCore)
      ((hclockSub u (hu.2.trans hcapD)).trans hinnerChart) (hchartSub u (hu.2.trans hcapD))
      ((mul_le_mul_of_nonneg_left (hclockSub u (hu.2.trans hcapD)) (by norm_num : (0 : ℝ) ≤ 8)).trans hsep)
      N k hkN (htimeSub u hu.2) hgeomk S hS X hX hZ hcur hinitCur hstart
  have hweightedOn (u : ℝ) (hu : u ∈ Icc (0 : ℝ) Dcap)
      (hZ : ∀ τ ∈ Icc (0 : ℝ) u, weightedFamilyNorm h k (x τ) ≤ Kboot)
      (hcur : ∀ τ ∈ Icc (0 : ℝ) u, ‖x τ k‖ ≤ δ) :
      ∀ τ ∈ Icc (0 : ℝ) u, weightedFamilyNorm h k (x τ) ≤ Cobs * h := by
    have hcs := hcurrentOn u hu hZ hcur
    have hw : ∀ τ ∈ Icc (0 : ℝ) u, weightedFamilyNorm h k (x τ) ≤
        (Lseed + F * D) * Real.exp (νbar * D) * h :=
      hweighted b hb hb1.le hcore hcorei hCb.le hC₀ hLseed hKboot.le hCcur.le hD.le hδa
        hs hA hR hρ hq hqE hRmax hρ1 hρb hhalf hρcore hsepU hsepL hh1 hhK hcurSmall.le hζ
        hβ hνup hCtRw hglobT (hdriftFor Cwgeo (le_max_right _ _)) (hdR.trans (by norm_num))
        ha ha16 hRchart hgeom hDphys he hu.1 (hu.2.trans hcapD) (hchartSub u (hu.2.trans hcapD))
        ((mul_le_mul_of_nonneg_left (hclockSub u (hu.2.trans hcapD)) (by norm_num : (0 : ℝ) ≤ 8)).trans hsep)
        N k hkN (htimeSub u hu.2) S hS X hX hZ hinitZ hcs.1 hcs.2
    intro τ hτ
    exact (hw τ hτ).trans (mul_le_mul_of_nonneg_right (by dsimp only [Cobs]; linarith) hh.le)
  have htimes : MapsTo (physicalTimeFromNormalized (ampScale A₀ b k) entrance)
      (Icc (0 : ℝ) Dcap) (Icc (0 : ℝ) Dphys) := by
    intro τ hτ
    exact ⟨add_nonneg he (div_nonneg hτ.1 hAk.le), htimeSub τ hτ.2⟩
  have hcontinuous := continuousOn_canonicalPrefix_joint_controls hγ hγ1 A₀ b R ρ h k entrance hX.continuous htimes
  have hclosed := continuous_joint_bootstrap hDcap hKboot hδ hcontinuous.1 hcontinuous.2
    (fun _ _ => norm_nonneg _) (fun _ _ => norm_nonneg _)
    ⟨hinitZ.trans_lt (hinitSmall.trans_le (min_le_left _ _)),
      hinitCur.trans_lt (hinitSmall.trans_le (min_le_right _ _))⟩
    (by
      intro u hu hhistory
      have hz := fun τ hτ => (hhistory τ hτ).1
      have hq := fun τ hτ => (hhistory τ hτ).2
      have hc := hcurrentOn u hu hz hq
      have hw := hweightedOn u hu hz hq
      exact ⟨(hw u ⟨hu.1, le_rfl⟩).trans_lt hobsSmall,
        (hc.1 u ⟨hu.1, le_rfl⟩).trans_lt hcurSmall⟩)
  have hz := fun τ hτ => (hclosed τ hτ).1.le
  have hq := fun τ hτ => (hclosed τ hτ).2.le
  have hc := hcurrentOn Dcap ⟨hDcap, le_rfl⟩ hz hq
  exact ⟨hweightedOn Dcap ⟨hDcap, le_rfl⟩ hz hq, hc.1, hc.2⟩

end CircularMaterialTransferProfile
end Euler2D

end
