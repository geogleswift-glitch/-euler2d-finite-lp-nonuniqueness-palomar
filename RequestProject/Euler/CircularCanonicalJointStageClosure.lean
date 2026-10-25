module

public import RequestProject.Euler.CircularCanonicalStoppedCapture
public import RequestProject.Euler.CircularCanonicalWeightedStageClosure
public import RequestProject.Euler.CircularCanonicalContinuousControls
public import RequestProject.Euler.CircularCanonicalPrefixMaterialBoundary

/-! The actual current and weighted ancestor controls close together
on the same finite Euler trajectory. Provisional history bounds are
discharged by the joint first-exit argument. -/

@[expose] public section

set_option maxHeartbeats 20000000
set_option maxRecDepth 7000

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

attribute [local instance 2000] rigidGaugeLittle_group rigidGaugeLittle_space rigidGaugeFamily_tower
attribute [local instance 2000] captureBlockTangent_group captureBlockTangent_space
  captureBlockTangent_continuousAdd captureBlockEndo_monoid captureBlockTangent_complete
attribute [local instance] LittleContourSpace.complexScalarNormedSpace LittleContourSpace.complexScalarTower
attribute [local irreducible] circularConstrainedTangentSubmodule circularConstrainedUnstableProjectionCLM
  circularConstrainedReturnMap circularConstrainedChart circularConstraintProjectionToTangentCLM
  circularBanachField circularBanachDomain

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_uniform_actualCanonical_joint_stage_closure {Rflow r₀ : ℝ}
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
      (circularConstrainedUnstableProjectionCLM hγ hγ1.le) circularAncientBackwardWeight r₀ gseq) :
    let L := circularCanonicalCellNormBudget hγ hγ1
    ∃ Kself : ℝ≥0, 0 < Kself ∧ ∃ rw > 0, ∃ Ctw > 0,
      ∀ b : ℝ≥0, 0 < b → b < 1 → ∀ Cw : ℝ, 0 ≤ Cw →
      ∃ Cgeo Ctc Cdc Cr Kr : ℝ,
      0 < Cgeo ∧ 0 < Ctc ∧ 0 < Cdc ∧ 0 < Cr ∧ 0 < Kr ∧
      ∃ ℓ : ℕ, 0 < ℓ ∧ ∃ qc : ℝ, 1 < qc ∧ qc ^ 2 < circularCaptureBlockMultiplier ℓ ∧
      let Tblock := circularCaptureBlockTime ℓ
      let lam := circularCaptureBlockMultiplier ℓ
      let Pu := circularConstrainedUnstableProjectionCLM hγ hγ1.le
      let g := fun v => gseq v 0 - v
      let Cb := radialStageRadiusConstant Cr Cw b
      ∃ C > 0, ∃ dcap > 0, dcap ≤ r₀ / 2 ∧ ∃ E > 0, ∃ F > 0, ∃ rc > 0,
      ∃ κ₀ > 0, ∃ ε₀ > 0, ∃ H > 0,
      ∀ {core C₀ ν₀ νbar Lseed δgeom δcur D₀ Ktarget Kboot : ℝ},
      0 < core → (∀ i, core ≤ 3 * circularContourRadii i / 4) →
      2 ≤ C₀ → 0 < ν₀ → νbar < sigma → 0 ≤ Lseed →
      0 < Ktarget → Ktarget < Kboot → 0 < δgeom → δgeom < δcur →
      δcur ≤ cellA / 4 → δcur ≤ rc →
      (finiteInnerLabelLittleRowCoefficient (γ : ℝ) (cellA / 2) L + 1) * δgeom /
        (C₀ * (sigma - νbar)) ≤ Ktarget / 2 →
      ∀ᶠ ξ : ℝ in atTop,
      let ρ := Real.exp (-ξ)
      let h := C₀ * ρ ^ 6
      ∀ {s A₀ R q T Hglob a d Dphys entrance Dcap η Δ Damp : ℝ},
      ∀ [Fact (1 ≤ ENNReal.ofReal q)] (hs : s ≤ 0) (hA : 0 < A₀)
        (hR : 0 < R) (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q),
      let Cu := finiteInnerLabelLittleRowCoefficient (γ : ℝ) (cellA / 2) L
      let Cl := finiteOuterLabelLittleRowCoefficient (γ : ℝ) core L L
      let CtRw := Ctw * finiteTorusLabelLittleRowCoefficient (γ : ℝ) L * R ^ 8
      let β := 3 * CtRw + weightedInteractionRowFeedback b Cu Cl C₀ ρ
      let κ := Ctc * finiteTorusLabelLittleRowCoefficient (γ : ℝ) L * R ^ 8
      let Bpoly := finiteCurrentPolynomialForcingCoefficient (γ : ℝ) (cellA / 2) L Cb b Cdc + Δ
      R ≤ 1 / 2 → ρ ≤ 1 → ρ ≤ b / 2 → ρ ^ 2 ≤ b / 2 →
      (5 / 4 : ℝ) * ρ ≤ cellA → 10 * ρ ≤ cellA / 2 → 8 * L * ρ ≤ core →
      h ≤ 1 → h * Kboot ≤ min rw δgeom → C₀ * ρ ^ 8 ≤ 1 / 2 →
      0 ≤ β → ν₀ ≤ ((b * Kself : ℝ≥0) : ℝ) + β →
      ((b * Kself : ℝ≥0) : ℝ) + β ≤ νbar → CtRw ≤ 1 →
      Hglob ≤ T → 5 / 4 + (Cgeo * A₀ / (1 - ρ / b)) * Hglob < d → d * R ≤ 1 / 16 →
      0 < a → a ≤ 1 / 16 → 0 < d → (5 / 4 : ℝ) * R ≤ a → (L + 1) * R ≤ a / 2 →
      0 ≤ Dphys → 0 ≤ entrance → 0 ≤ Dcap → Dcap ≤ (6 / sigma) * ξ + D₀ →
      0 ≤ η → η ≤ cellA / 4 → (∀ i, ‖(P.ancient s i).val - circularReferenceC1 hγ hγ1 i‖ ≤ η) →
      0 ≤ Δ →
      (2 * (b : ℝ) * C₀ * Kboot * (Cl + Ctc * finiteTorusLabelLittleRowCoefficient (γ : ℝ) L)) * ρ ^ 2 ≤ Δ →
      b * finiteEulerUniformRadialCoefficient Kr b R ρ core d δcur * Cb ^ 3 *
        ρ ^ 2 * (1 + Dcap) ^ 3 ≤ Cr / 2 →
      Cb * ρ * (1 + Dcap) ≤ core / 2 → Cb * ρ * (1 + Dcap) ≤ d →
      Cb * ρ * R * (1 + Dcap) ≤ a → 8 * (Cb * ρ * (1 + Dcap)) ≤ cellA / 2 →
      κ ≤ κ₀ → 3 * Damp ≤ dcap → qc + 3 * C * Damp ≤ lam → H * Damp ≤ δgeom →
      ∀ (N k Ncap : ℕ) (hkN : k ≤ N),
      0 < Ncap → Dcap ≤ (Ncap : ℝ) * Tblock →
      entrance + Dcap / ampScale A₀ b k ≤ Dphys →
      9 * C * Damp / (lam - 1) + 3 * (E * κ) * (Ncap : ℝ) ≤ 1 / 16 →
      Bpoly * ρ ^ 6 * (1 + (Ncap : ℝ) * Tblock) ^ 4 + κ * (3 * Damp) ≤ ε₀ →
      ∀ S : BoundedEulerParticleSystem
        (finiteBaseCurlL2 (A₀ := A₀) (b := (b : ℝ)) (ρ := ρ) hR (Real.exp_pos (-ξ)) hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := (b : ℝ)) (ρ := ρ) (q := q) hs hR (Real.exp_pos (-ξ))) N) T,
      IsFourfoldBoundedEulerParticleSystem S →
      ∀ X : ℝ → FiniteCircularIndex k → LittleContourSpace γ,
      P.ActualCanonicalPrefixTrajectory s A₀ b R ρ a Hglob hR (Real.exp_pos (-ξ)) hkN S Dphys X →
      let x := canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance X
      let y := canonicalPrefixAlignedCurrentCell A₀ b R ρ k entrance X
      let v := fun n : ℕ => circularConstraintProjectionToTangentCLM hγ hγ1.le
        (y ((n : ℝ) * Tblock) - littleCircularReference hγ hγ1)
      let α := fun n => Pu (v n)
      let w := fun n => (v n - α n) - g (α n)
      weightedFamilyNorm h k (x 0) ≤ Lseed * h → ‖x 0 k‖ < δcur →
      (∀ z ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N k,
        ‖S.forward entrance z - torusCenter‖ ≤ Cw * ρ * radScale R ρ k) →
      0 < ‖α 0‖ → ‖α 0‖ * lam ^ Ncap ≤ Damp →
      ‖w 0‖ ≤ ‖α 0‖ / 32 → F * Bpoly * ρ ^ 6 ≤ ‖α 0‖ / 32 →
      (∀ n ≤ Ncap, (n : ℝ) * Tblock ≤ Dcap →
        (3 / 4 : ℝ) * ‖α 0‖ * lam ^ n ≤ ‖α n‖ ∧
        ‖α n‖ ≤ (5 / 4 : ℝ) * ‖α 0‖ * lam ^ n ∧
        ‖w n‖ ≤ (1 / 8 : ℝ) * ‖α 0‖ * lam ^ n) ∧
      (∀ τ ∈ Icc (0 : ℝ) Dcap, ‖x τ k‖ ≤ H * ‖α 0‖ * Real.exp (sigma * τ)) ∧
      (∀ τ ∈ Icc (0 : ℝ) Dcap, weightedFamilyNorm h k (x τ) ≤ Ktarget) ∧
      ∀ τ ∈ Icc (0 : ℝ) Dcap, ∀ z ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N k,
        ‖S.forward (physicalTimeFromNormalized (ampScale A₀ b k) entrance τ) z - torusCenter‖ ≤
          Cb * ρ * radScale R ρ k * (1 + τ) := by
  obtain ⟨Kself, hKself, rw, hrw, Cwgeo, Ctw, Cdw, hCwgeo, hCtw, hCdw, hweighted⟩ :=
    P.exists_uniform_actualCanonical_weighted_stage_closure
  refine ⟨Kself, hKself, rw, hrw, Ctw, hCtw, ?_⟩
  intro b hb hb1 Cw hCw
  have hbR : 0 < (b : ℝ) := hb
  have hbR1 : (b : ℝ) < 1 := hb1
  obtain ⟨Ccgeo, Ctc, Cdc, Cr, Kr, hCcgeo, hCtc, hCdc, hCr, hKr, ℓ, hℓ, qc, hqc, hqgap,
    C, hC, dcap, hdcap, hdr, E, hE, F, hF, rc, hrc, κ₀, hκ₀, ε₀, hε₀, H, hH, hcapture⟩ :=
    P.exists_uniform_actualCanonical_stopped_capture hbR hbR1 hCw hRflow hr₀ hY hd hfix harea hg
  let Cgeo := max Ccgeo Cwgeo
  let L := circularCanonicalCellNormBudget hγ hγ1
  let Cb := radialStageRadiusConstant Cr Cw b
  have hCb : 0 < Cb := radialStageRadiusConstant_pos hCr hCw hbR hbR1
  refine ⟨Cgeo, Ctc, Cdc, Cr, Kr, hCcgeo.trans_le (le_max_left _ _), hCtc, hCdc, hCr, hKr,
    ℓ, hℓ, qc, hqc, hqgap, C, hC, dcap, hdcap, hdr, E, hE, F, hF, rc, hrc,
    κ₀, hκ₀, ε₀, hε₀, H, hH, ?_⟩
  intro core C₀ ν₀ νbar Lseed δgeom δcur D₀ Ktarget Kboot hcore hcorei hC₀ hν₀ hνbar
    hLseed hKtarget hKtargetBoot hδgeom hδgc hδcura hδcurc hmargin
  have hδcur : 0 < δcur := hδgeom.trans hδgc
  have hKboot : 0 < Kboot := hKtarget.trans hKtargetBoot
  have hδgeoma : δgeom ≤ cellA / 4 := hδgc.le.trans hδcura
  have hstage := hweighted b hb hb1.le (D₀ := D₀) hcore hcorei hCb.le hC₀ hν₀ hνbar hLseed
    hKtarget hKboot.le hδgeoma hmargin
  have hsmallInit : ∀ᶠ ξ : ℝ in atTop, Lseed * (C₀ * Real.exp (-ξ) ^ 6) < Kboot := by
    have he := ((Real.tendsto_exp_neg_atTop_nhds_zero.pow 6).const_mul C₀).const_mul Lseed
    have he' : Tendsto (fun ξ : ℝ => Lseed * (C₀ * Real.exp (-ξ) ^ 6)) atTop (𝓝 0) := by
      simpa only [zero_pow (by decide : (6 : ℕ) ≠ 0), mul_zero] using he
    exact he'.eventually (eventually_lt_nhds hKboot)
  filter_upwards [hstage, hsmallInit] with ξ hξ hinitSmall
  dsimp only
  let ρ := Real.exp (-ξ)
  let h := C₀ * ρ ^ 6
  intro s A₀ R q T Hglob a d Dphys entrance Dcap η Δ Damp _ hs hA hR hq hqE
  let Cu := finiteInnerLabelLittleRowCoefficient (γ : ℝ) (cellA / 2) L
  let Cl := finiteOuterLabelLittleRowCoefficient (γ : ℝ) core L L
  let CtRw := Ctw * finiteTorusLabelLittleRowCoefficient (γ : ℝ) L * R ^ 8
  let β := 3 * CtRw + weightedInteractionRowFeedback b Cu Cl C₀ ρ
  let κ := Ctc * finiteTorusLabelLittleRowCoefficient (γ : ℝ) L * R ^ 8
  let Bpoly := finiteCurrentPolynomialForcingCoefficient (γ : ℝ) (cellA / 2) L Cb b Cdc + Δ
  try dsimp only
  intro hRmax hρ1 hρhalf hhalf hρcore hsepU hsepL hh1 hhK hζ hβ hνlo hνup hCtRw
    hglobT hdrift hdR ha ha16 hdpos hRchart hgeom hDphys he hDcap hlogcap
    hη hηa hancient hΔ houter hcubic hinnerCore hinnerChart hchart hsep
    hκcap hDamp hcomp hHDamp N k Ncap hkN hNcap hcapDuration htimeEnd hsmallCap hpolyCap S hS X hX
  let x := canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance X
  let y := canonicalPrefixAlignedCurrentCell A₀ b R ρ k entrance X
  let v := fun n : ℕ => circularConstraintProjectionToTangentCLM hγ hγ1.le
    (y ((n : ℝ) * circularCaptureBlockTime ℓ) - littleCircularReference hγ hγ1)
  let α := fun n => circularConstrainedUnstableProjectionCLM hγ hγ1.le (v n)
  intro hinitZ hinitCur hstart ha₀ hterminal hw₀ hsource
  have hρ : 0 < ρ := Real.exp_pos _
  have hρb : ρ < (b : ℝ) := hρhalf.trans_lt (by linarith only [hbR])
  have hden : 0 < 1 - ρ / b := sub_pos.mpr ((div_lt_one hbR).mpr hρb)
  have hAk : 0 < ampScale A₀ b k := by unfold ampScale; positivity
  have hHglob : 0 ≤ Hglob := (hX.mem 0 ⟨le_rfl, hDphys⟩).1.2
  have hdriftFor (C₁ : ℝ) (hC₁ : C₁ ≤ Cgeo) :
      5 / 4 + (C₁ * A₀ / (1 - ρ / b)) * Hglob < d :=
    (add_le_add le_rfl (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hC₁ hA.le) hden.le) hHglob)).trans_lt hdrift
  have hrk : radScale R ρ k ≤ R := mul_le_of_le_one_right hR.le (pow_le_one₀ hρ.le hρ1)
  have hL : 0 < L := circularCanonicalCellNormBudget_pos hγ hγ1
  have hgeomk : (L + 1) * radScale R ρ k ≤ a / 2 :=
    (mul_le_mul_of_nonneg_left hrk (by linarith only [hL])).trans hgeom
  have hhKc : h * Kboot ≤ δcur :=
    (hhK.trans (min_le_right _ _)).trans hδgc.le
  have houterb : (b : ℝ) * ρ ^ 2 < 1 :=
    (mul_le_of_le_one_right hbR.le (pow_le_one₀ hρ.le hρ1)).trans_lt hbR1
  have hsmallρ : ρ ^ 2 < (b : ℝ) := hhalf.trans_lt (by linarith only [hbR])
  have hdenMass : 0 < 1 - ρ ^ 2 / b := sub_pos.mpr ((div_lt_one hbR).mpr hsmallρ)
  have hmass : 0 ≤ circularFiniteL1Coefficient b ρ := by
    unfold circularFiniteL1Coefficient finiteContourPatchMassBound
    exact add_nonneg (div_nonneg ENNReal.toReal_nonneg hdenMass.le)
      (Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) measureReal_nonneg))
  have hweight : 0 ≤ circularRadialPerturbationWeight :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (circularContourRadii_bounds i).1.le)
  have hcoef : 0 ≤ (b : ℝ) * finiteEulerUniformRadialCoefficient Kr b R ρ core d δcur * Cb ^ 3 * ρ ^ 2 := by
    unfold finiteEulerUniformRadialCoefficient
    positivity [sub_pos.mpr houterb]
  have hcubicSub (u : ℝ) (hu : u ∈ Icc (0 : ℝ) Dcap) :
      (b : ℝ) * finiteEulerUniformRadialCoefficient Kr b R ρ core d δcur * Cb ^ 3 * ρ ^ 2 * (1 + u) ^ 3 ≤ Cr / 2 :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith only [hu.1])
      (add_le_add le_rfl hu.2) 3) hcoef).trans hcubic
  have hclockSub (u : ℝ) (hu : u ≤ Dcap) : Cb * ρ * (1 + u) ≤ Cb * ρ * (1 + Dcap) :=
    mul_le_mul_of_nonneg_left (add_le_add le_rfl hu) (mul_nonneg hCb.le hρ.le)
  have hchartSub (u : ℝ) (hu : u ∈ Icc (0 : ℝ) Dcap) : Cb * ρ * radScale R ρ k * (1 + u) ≤ a := by
    calc
      _ = (Cb * ρ * (1 + u)) * radScale R ρ k := by ring
      _ ≤ (Cb * ρ * (1 + Dcap)) * R := mul_le_mul (hclockSub u hu.2) hrk
        (radScale_pos hR hρ k).le (by positivity)
      _ ≤ _ := by convert hchart using 1 <;> ring
  have hcaptureOn (u : ℝ) (hu : u ∈ Icc (0 : ℝ) Dcap)
      (hZ : ∀ τ ∈ Icc (0 : ℝ) u, weightedFamilyNorm h k (x τ) ≤ Kboot)
      (hcur : ∀ τ ∈ Icc (0 : ℝ) u, ‖x τ k‖ ≤ δcur) :=
    hcapture hs hA hR hRmax hρ hρ1 hρhalf hq hqE hglobT
      (hdriftFor Ccgeo (le_max_left _ _)) hdR ha ha16 hcore hdpos hDphys he hu.1 hhalf hρcore
      hδcura hδcurc hcorei hη hηa hancient (by linarith only [hC₀]) hKboot.le hΔ hh1 hhKc hζ
      hsepL hRchart houter (hcubicSub u hu) ((hclockSub u hu.2).trans hinnerCore)
      ((hclockSub u hu.2).trans hinnerChart) hκcap hDamp hcomp N k Ncap hkN hNcap
      (hu.2.trans hcapDuration)
      ((add_le_add le_rfl (div_le_div_of_nonneg_right hu.2 hAk.le)).trans htimeEnd)
      hgeomk (hchartSub u hu)
      ((mul_le_mul_of_nonneg_left (hclockSub u hu.2) (by norm_num : (0 : ℝ) ≤ 8)).trans hsep)
      hsmallCap hpolyCap S hS X hX hZ hcur hstart ha₀ hterminal hw₀ hsource
  have hpower (n : ℕ) : circularCaptureBlockMultiplier ℓ ^ n =
      Real.exp (sigma * ((n : ℝ) * circularCaptureBlockTime ℓ)) := by
    rw [circularCaptureBlockMultiplier_eq_exp, ← Real.exp_nat_mul]
    congr 1
    ring
  have hEmax : (H * ‖α 0‖) * Real.exp (sigma * Dcap) ≤ δgeom := by
    have he := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left hcapDuration sigma_pos.le)) (norm_nonneg (α 0))
    rw [← hpower] at he
    have hh := mul_le_mul_of_nonneg_left (he.trans hterminal) hH.le
    have hh' : (H * ‖α 0‖) * Real.exp (sigma * Dcap) ≤ H * Damp := by
      simpa only [mul_assoc] using hh
    exact hh'.trans hHDamp
  have hEmaxSub (u : ℝ) (hu : u ≤ Dcap) :
      (H * ‖α 0‖) * Real.exp (sigma * u) ≤ δgeom :=
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left hu sigma_pos.le)) (mul_nonneg hH.le (norm_nonneg _))).trans hEmax
  have hweightedOn (u : ℝ) (hu : u ∈ Icc (0 : ℝ) Dcap)
      (hZ : ∀ τ ∈ Icc (0 : ℝ) u, weightedFamilyNorm h k (x τ) ≤ Kboot)
      (hcur : ∀ τ ∈ Icc (0 : ℝ) u, ‖x τ k‖ ≤ δcur) := by
    have hcap := hcaptureOn u hu hZ hcur
    exact hξ hs hA hR hρ hq hqE hRmax hρ1 hρb hhalf hρcore hsepU hsepL hh1 hhK hζ
      hβ hνlo hνup hCtRw hglobT (hdriftFor Cwgeo (le_max_right _ _))
      (hdR.trans (by norm_num)) ha ha16 hRchart hgeom hDphys he
      (mul_nonneg hH.le (norm_nonneg (α 0))) hu.1 (hu.2.trans hlogcap) (hEmaxSub u hu.2)
      ((mul_le_mul_of_nonneg_left (add_le_add le_rfl hu.2) (by positivity : 0 ≤ Cb * ρ * R)).trans hchart)
      ((mul_le_mul_of_nonneg_left (hclockSub u hu.2) (by norm_num : (0 : ℝ) ≤ 8)).trans hsep)
      N k hkN ((add_le_add le_rfl (div_le_div_of_nonneg_right hu.2 hAk.le)).trans htimeEnd)
      S hS X hX hZ hinitZ hcap.2.1 hcap.2.2
  have htimes : MapsTo (physicalTimeFromNormalized (ampScale A₀ b k) entrance)
      (Icc (0 : ℝ) Dcap) (Icc (0 : ℝ) Dphys) := by
    intro τ hτ
    exact ⟨add_nonneg he (div_nonneg hτ.1 hAk.le),
      (add_le_add le_rfl (div_le_div_of_nonneg_right hτ.2 hAk.le)).trans htimeEnd⟩
  have hcontinuous := continuousOn_canonicalPrefix_joint_controls hγ hγ1 A₀ b R ρ h k entrance hX.continuous htimes
  have hclosed := continuous_joint_bootstrap hDcap hKboot hδcur hcontinuous.1 hcontinuous.2
    (fun _ _ => norm_nonneg _) (fun _ _ => norm_nonneg _)
    ⟨hinitZ.trans_lt hinitSmall, hinitCur⟩
    (by
      intro u hu hhistory
      have hz := fun τ hτ => (hhistory τ hτ).1
      have hq := fun τ hτ => (hhistory τ hτ).2
      have hcap := hcaptureOn u hu hz hq
      have hw := hweightedOn u hu hz hq
      exact ⟨(hw u ⟨hu.1, le_rfl⟩).trans_lt hKtargetBoot,
        (hcap.2.1 u ⟨hu.1, le_rfl⟩).trans_lt ((hEmaxSub u hu.2).trans_lt hδgc)⟩)
  have hz := fun τ hτ => (hclosed τ hτ).1.le
  have hq := fun τ hτ => (hclosed τ hτ).2.le
  have hcap := hcaptureOn Dcap ⟨hDcap, le_rfl⟩ hz hq
  exact ⟨hcap.1, hcap.2.1, hweightedOn Dcap ⟨hDcap, le_rfl⟩ hz hq, hcap.2.2⟩

end CircularMaterialTransferProfile
end Euler2D

end
