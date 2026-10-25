module

public import RequestProject.Euler.CircularUniformCanonicalJointStageScaleClosure
public import RequestProject.Euler.CircularCanonicalPastFutureExtension
public import RequestProject.Euler.CircularFiniteUniformSupport
public import RequestProject.Euler.CircularCanonicalControlGeometry
public import RequestProject.Euler.CircularCoRotatedCaptureSection

/-! Actual parent capture after a genuine nonzero entrance state.
The SAME Euler system and past material prefix are continued through
the full logarithmic capture horizon. The real particle buffer, joint
current/ancestor control and original co-rotated section are proved. -/

@[expose] public section

set_option maxHeartbeats 64000000
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
attribute [local irreducible] circularConstrainedTangentSubmodule circularConstrainedUnstableProjectionCLM
  circularConstrainedReturnMap circularConstrainedChart circularConstraintProjectionToTangentCLM
  circularBanachField circularBanachDomain

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_uniform_actualParent_capture_scale_trajectory {Rflow r₀ : ℝ}
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
      ∃ Cgeo Ctc Cdc Cr Kr : ℝ,
      0 < Cgeo ∧ 0 < Ctc ∧ 0 < Cdc ∧ 0 < Cr ∧ 0 < Kr ∧
      ∃ ℓ : ℕ, 0 < ℓ ∧ ∃ qc : ℝ, 1 < qc ∧ qc ^ 2 < circularCaptureBlockMultiplier ℓ ∧
      let Tblock := circularCaptureBlockTime ℓ
      let lam := circularCaptureBlockMultiplier ℓ
      let Pu := circularConstrainedUnstableProjectionCLM hγ hγ1.le
      let g := fun v => gseq v 0 - v
      ∃ C > 0, ∃ dcap > 0, dcap ≤ r₀ / 2 ∧ ∃ E > 0, ∃ F > 0, ∃ rc > 0,
      ∃ κ₀ > 0, ∃ ε₀ > 0, ∃ H > 0, ∃ Eg > 0, ∃ Rg > 0,
      ∀ qbar : ℝ, 1 < qbar → qbar ^ 2 < lam → ∃ Fbar > 0,
      ∀ b : ℝ≥0, 0 < b → b < 1 → ∀ Cw : ℝ, 0 ≤ Cw →
      let Cb := radialStageRadiusConstant Cr Cw b
      ∀ {core C₀ ν₀ νbar Lseed δgeom δcur D₀ Ktarget Kboot : ℝ},
      0 < core → (∀ i, core ≤ 3 * circularContourRadii i / 4) →
      2 ≤ C₀ → 0 < ν₀ → νbar < sigma → 0 ≤ Lseed →
      0 < Ktarget → Ktarget < Kboot → 0 < δgeom → δgeom < δcur →
      δcur ≤ cellA / 4 → δcur ≤ rc →
      δgeom ≤ cellA / 16 → δgeom ≤ (1 - cellA) / 16 →
      (finiteInnerLabelLittleRowCoefficient (γ : ℝ) (cellA / 2) L + 1) * δgeom /
        (C₀ * (sigma - νbar)) ≤ Ktarget / 2 →
      ∀ᶠ ξ : ℝ in atTop,
      let ρ := Real.exp (-ξ)
      let h := C₀ * ρ ^ 6
      ∀ {s A₀ R q T Hglob a d entrance Δ Damp cs W0 : ℝ},
      ∀ [Fact (1 ≤ ENNReal.ofReal q)] (hs : s ≤ 0) (hA : 0 < A₀)
        (hR : 0 < R) (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q),
      let Cu := finiteInnerLabelLittleRowCoefficient (γ : ℝ) (cellA / 2) L
      let Cl := finiteOuterLabelLittleRowCoefficient (γ : ℝ) core L L
      let CtRw := Ctw * finiteTorusLabelLittleRowCoefficient (γ : ℝ) L * R ^ 8
      let β := 3 * CtRw + weightedInteractionRowFeedback b Cu Cl C₀ ρ
      let κ := Ctc * finiteTorusLabelLittleRowCoefficient (γ : ℝ) L * R ^ 8
      let Bpoly := finiteCurrentPolynomialForcingCoefficient (γ : ℝ) (cellA / 2) L Cb b Cdc + Δ
      ∀ Ncap : ℕ, 0 < Ncap →
      let Dcap := (Ncap : ℝ) * Tblock
      R ≤ 1 / 2 → ρ ≤ 1 → ρ ≤ b / 2 → ρ ^ 2 ≤ b / 2 → ρ ≤ cellA / 128 →
      (5 / 4 : ℝ) * ρ ≤ cellA → 10 * ρ ≤ cellA / 2 → 8 * L * ρ ≤ core →
      h ≤ 1 → h * Kboot ≤ min rw δgeom → C₀ * ρ ^ 8 ≤ 1 / 2 →
      0 ≤ β → ν₀ ≤ ((b * Kself : ℝ≥0) : ℝ) + β →
      ((b * Kself : ℝ≥0) : ℝ) + β ≤ νbar → CtRw ≤ 1 →
      0 < Hglob → Hglob ≤ T → 5 / 4 + (Cgeo * A₀ / (1 - ρ / b)) * Hglob < d →
      d * R ≤ 1 / 16 → d * R ≤ a →
      0 < a → a ≤ 1 / 16 → 0 < d → (5 / 4 : ℝ) * R < a → (L + 1) * R ≤ a / 2 →
      R * (‖littleCircularReference hγ hγ1‖ + δgeom) < a / 4 →
      0 ≤ entrance → Dcap ≤ (6 / sigma) * ξ + D₀ →
      (∀ i, ‖(P.ancient s i).val - circularReferenceC1 hγ hγ1 i‖ ≤ δgeom) → 0 ≤ Δ →
      (2 * (b : ℝ) * C₀ * Kboot * (Cl + Ctc * finiteTorusLabelLittleRowCoefficient (γ : ℝ) L)) * ρ ^ 2 ≤ Δ →
      b * finiteEulerUniformRadialCoefficient Kr b R ρ core d δcur * Cb ^ 3 *
        ρ ^ 2 * (1 + Dcap) ^ 3 ≤ Cr / 2 →
      Cb * ρ * (1 + Dcap) ≤ core / 2 → Cb * ρ * (1 + Dcap) ≤ d →
      Cb * ρ * R * (1 + Dcap) ≤ a → 8 * (Cb * ρ * (1 + Dcap)) ≤ cellA / 2 →
      Cb * ρ * (1 + Dcap) ≤ cellA / 128 →
      κ ≤ κ₀ → 3 * Damp ≤ dcap → qc + 3 * C * Damp ≤ qbar → H * Damp ≤ δgeom →
      ∀ (N k : ℕ) (hkN : k ≤ N), entrance + Dcap / ampScale A₀ b k < Hglob →
      9 * C * Damp / (lam - 1) + 3 * (E * κ) * (Ncap : ℝ) ≤ 1 / 16 →
      Bpoly * ρ ^ 6 * (1 + (Ncap : ℝ) * Tblock) ^ 4 + κ * (3 * Damp) ≤ ε₀ →
      ∀ S : BoundedEulerParticleSystem
        (finiteBaseCurlL2 (A₀ := A₀) (b := (b : ℝ)) (ρ := ρ) hR (Real.exp_pos (-ξ)) hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := (b : ℝ)) (ρ := ρ) (q := q) hs hR (Real.exp_pos (-ξ))) N) T,
      IsFourfoldBoundedEulerParticleSystem S →
      ∀ Ypast : ℝ → FiniteCircularIndex k → LittleContourSpace γ,
      P.ActualCanonicalPrefixTrajectory s A₀ b R ρ a Hglob hR (Real.exp_pos (-ξ)) hkN S
        entrance Ypast →
      (∀ t ∈ Icc (0 : ℝ) entrance,
        ∃ β : FiniteCircularIndex k → ℝ, ∀ p,
          ‖contourParameterShiftC1 (β p) (Ypast t p).val - finiteCircularReferenceC1 hγ hγ1 R ρ p‖ ≤
            δgeom * radScale R ρ p.1) →
      (∀ t ∈ Icc (0 : ℝ) entrance, ∀ z ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N k,
        ‖S.forward t z - torusCenter‖ ≤ (Cw + 2) * ρ * radScale R ρ k) →
      let xPast := canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance Ypast
      let yPast := canonicalPrefixAlignedCurrentCell A₀ b R ρ k entrance Ypast
      let v₀ := circularConstraintProjectionToTangentCLM hγ hγ1.le
        (yPast 0 - littleCircularReference hγ hγ1)
      let α₀ := Pu v₀
      let w₀ := (v₀ - α₀) - g α₀
      weightedFamilyNorm h k (xPast 0) ≤ Lseed * h → ‖xPast 0 k‖ < δcur →
      (∀ z ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N k,
        ‖S.forward entrance z - torusCenter‖ ≤ Cw * ρ * radScale R ρ k) →
      0 < ‖α₀‖ → ‖α₀‖ * lam ^ Ncap ≤ Damp →
      ‖w₀‖ ≤ ‖α₀‖ / 32 → F * Bpoly * ρ ^ 6 ≤ ‖α₀‖ / 32 →
      0 < cs → 0 ≤ W0 → cs * ρ ^ 6 ≤ ‖α₀‖ → ‖w₀‖ ≤ W0 * ρ ^ 6 →
      ∀ δhit : ℝ, ‖α₀‖ < δhit → δhit ≤ (3 / 4 : ℝ) * ‖α₀‖ * lam ^ Ncap →
      ∃ X : ℝ → FiniteCircularIndex k → LittleContourSpace γ,
        P.ActualCanonicalPrefixTrajectory s A₀ b R ρ a Hglob hR (Real.exp_pos (-ξ)) hkN S
          (entrance + Dcap / ampScale A₀ b k) X ∧
      EqOn X Ypast (Icc (0 : ℝ) entrance) ∧
      let x := canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance X
      let y := canonicalPrefixAlignedCurrentCell A₀ b R ρ k entrance X
      let v := fun n : ℕ => circularConstraintProjectionToTangentCLM hγ hγ1.le
        (y ((n : ℝ) * Tblock) - littleCircularReference hγ hγ1)
      let α := fun n => Pu (v n)
      let w := fun n => (v n - α n) - g (α n)
      (∀ n ≤ Ncap,
        (3 / 4 : ℝ) * ‖α₀‖ * lam ^ n ≤ ‖α n‖ ∧
        ‖α n‖ ≤ (5 / 4 : ℝ) * ‖α₀‖ * lam ^ n ∧
        ‖w n‖ ≤ (1 / 8 : ℝ) * ‖α₀‖ * lam ^ n) ∧
      (∀ τ ∈ Icc (0 : ℝ) Dcap, ‖x τ k‖ ≤ H * ‖α₀‖ * Real.exp (sigma * τ)) ∧
      (∀ τ ∈ Icc (0 : ℝ) Dcap, weightedFamilyNorm h k (x τ) ≤ Ktarget) ∧
      (∀ τ ∈ Icc (0 : ℝ) Dcap, ∀ z ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N k,
        ‖S.forward (physicalTimeFromNormalized (ampScale A₀ b k) entrance τ) z - torusCenter‖ ≤
          Cb * ρ * radScale R ρ k * (1 + τ)) ∧
      (∀ τ ∈ Icc (0 : ℝ) Dcap,
        let vc := circularConstraintProjectionToTangentCLM hγ hγ1.le
          (circularCoRotationCLM γ τ (y τ) - littleCircularReference hγ hγ1)
        ‖vc - gseq (Pu vc) 0‖ ≤ Eg *
          ((W0 + Fbar * Bpoly) * (Damp / cs + 1) * ρ ^ 3 +
            3 * (E * κ) * Damp / (lam - qbar) +
            Bpoly * ρ ^ 6 * (1 + (Ncap : ℝ) * Tblock) ^ 4 + κ * Rg)) ∧
      HasFirstCircularCoRotatedCaptureSection hγ hγ1 y Dcap δhit ∧
      ∃ τ ∈ Ioc (0 : ℝ) Dcap,
        physicalTimeFromNormalized (ampScale A₀ b k) entrance τ ∈
          Ioc entrance (entrance + Dcap / ampScale A₀ b k) ∧
        ‖Pu (circularConstraintProjectionToTangentCLM hγ hγ1.le
          (circularCoRotationCLM γ τ (y τ) - littleCircularReference hγ hγ1))‖ = δhit ∧
        ∀ u ∈ Ico (0 : ℝ) τ,
          ‖Pu (circularConstraintProjectionToTangentCLM hγ hγ1.le
            (circularCoRotationCLM γ u (y u) - littleCircularReference hγ hγ1))‖ < δhit := by
  run_tac do IO.eprintln "parent-capture: entered body"
  obtain ⟨Cp, hCp, hpastExtend⟩ := P.exists_uniform_actualPrefix_past_future_extension
  obtain ⟨Cs, hCs, hsupport⟩ := P.exists_uniform_finiteEuler_support_bound
  obtain ⟨Kself, hKself, rw, hrw, Ctw, hCtw,
    Cj, Ctc, Cdc, Cr, Kr, hCj, hCtc, hCdc, hCr, hKr, ℓ, hℓ, qc, hqc, hqgap,
    C, hC, dcap, hdcap, hdr, E, hE, F, hF, rc, hrc, κ₀, hκ₀, ε₀, hε₀, H, hH,
    Eg, hEg, Rg, hRg, hstageFamily⟩ :=
    P.exists_uniform_actualCanonical_joint_stage_scale_closure_constants hRflow hr₀ hY hd hfix harea hg
  let Cgeo := max Cj (max Cp Cs)
  let L := circularCanonicalCellNormBudget hγ hγ1
  let Tblock := circularCaptureBlockTime ℓ
  let lam := circularCaptureBlockMultiplier ℓ
  refine ⟨Kself, hKself, rw, hrw, Ctw, hCtw,
    Cgeo, Ctc, Cdc, Cr, Kr, hCj.trans_le (le_max_left _ _), hCtc, hCdc, hCr, hKr,
    ℓ, hℓ, qc, hqc, hqgap, C, hC, dcap, hdcap, hdr, E, hE, F, hF, rc, hrc,
    κ₀, hκ₀, ε₀, hε₀, H, hH, Eg, hEg, Rg, hRg, ?_⟩
  intro qbar hqbar hqbarGap
  obtain ⟨Fbar, hFbar, hstageAll⟩ := hstageFamily qbar hqbar hqbarGap
  refine ⟨Fbar, hFbar, ?_⟩
  intro b hb hb1 Cw hCw
  try dsimp only
  have hbR : 0 < (b : ℝ) := hb
  have hbR1 : (b : ℝ) < 1 := hb1
  let Cb := radialStageRadiusConstant Cr Cw b
  have hCb : 0 < Cb := radialStageRadiusConstant_pos hCr hCw hbR hbR1
  intro core C₀ ν₀ νbar Lseed δgeom δcur D₀ Ktarget Kboot hcore hcorei hC₀ hν₀ hνbar
    hLseed hKtarget hKtargetBoot hδgeom hδgc hδcura hδcurc hδgeom16 hδgeomgap hmargin
  have hδgeoma : δgeom ≤ cellA / 4 := hδgc.le.trans hδcura
  have hδcur : 0 < δcur := hδgeom.trans hδgc
  have hξstage := hstageAll b hb hb1 Cw hCw (Lseed := Lseed) (D₀ := D₀)
    hcore hcorei hC₀ hν₀ hνbar hLseed hKtarget hKtargetBoot hδgeom hδgc hδcura hδcurc hmargin
  filter_upwards [hξstage] with ξ hξ
  try dsimp only
  let ρ := Real.exp (-ξ)
  let h := C₀ * ρ ^ 6
  intro s A₀ R q T Hglob a d entrance Δ Damp cs W0 _ hs hA hR hq hqE
  let Cu := finiteInnerLabelLittleRowCoefficient (γ : ℝ) (cellA / 2) L
  let Cl := finiteOuterLabelLittleRowCoefficient (γ : ℝ) core L L
  let CtRw := Ctw * finiteTorusLabelLittleRowCoefficient (γ : ℝ) L * R ^ 8
  let β := 3 * CtRw + weightedInteractionRowFeedback b Cu Cl C₀ ρ
  let κ := Ctc * finiteTorusLabelLittleRowCoefficient (γ : ℝ) L * R ^ 8
  let Bpoly := finiteCurrentPolynomialForcingCoefficient (γ : ℝ) (cellA / 2) L Cb b Cdc + Δ
  try dsimp only
  intro Ncap hNcap
  let Dcap := (Ncap : ℝ) * circularCaptureBlockTime ℓ
  try dsimp only
  intro hRmax hρ1 hρhalf hhalf hρ128 hρcore hsepU hsepL hh1 hhK hζ hβ hνlo hνup hCtRw
    hHglob hglobT hdrift hdR hdRa ha ha16 hdpos hRchart hgeom hsize he hlogcap hancient hΔ houter
    hcubic hinnerCore hinnerChart hchart hsep hbufferSmall hκcap hDamp hcomp hHDamp
    N k hkN hHcap hsmallCap hpolyCap S hS Ypast hYpast hpastGeom hpastParticles
  let xPast := canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance Ypast
  let yPast := canonicalPrefixAlignedCurrentCell A₀ b R ρ k entrance Ypast
  let v₀ := circularConstraintProjectionToTangentCLM hγ hγ1.le
    (yPast 0 - littleCircularReference hγ hγ1)
  let α₀ := circularConstrainedUnstableProjectionCLM hγ hγ1.le v₀
  try dsimp only
  intro hinitZ hinitCur hstart ha₀ hterminal hw₀ hsource hcs hW0 hseedLow hwScale
    δhit hhitStart hhitEnd
  run_tac do IO.eprintln "parent-capture: introduced true past and seed"
  have hρ : 0 < ρ := Real.exp_pos _
  have hρb : ρ < (b : ℝ) := hρhalf.trans_lt (by linarith only [hbR])
  have hden : 0 < 1 - ρ / b := sub_pos.mpr ((div_lt_one hbR).mpr hρb)
  have hAk : 0 < ampScale A₀ b k := by unfold ampScale; positivity
  have hrk : 0 < radScale R ρ k := radScale_pos hR hρ k
  have hDcap : 0 < Dcap := mul_pos (Nat.cast_pos.mpr hNcap) (circularCaptureBlockTime_pos hℓ)
  let Hcap := entrance + Dcap / ampScale A₀ b k
  have heHcap : entrance < Hcap := lt_add_of_pos_right entrance (div_pos hDcap hAk)
  have hHcapPos : 0 < Hcap := he.trans_lt heHcap
  have hscale : ampScale A₀ b k * (Hcap - entrance) = Dcap := by
    dsimp only [Hcap]
    field_simp [hAk.ne'] <;> ring
  have hdriftFor (C₁ : ℝ) (hC₁ : C₁ ≤ Cgeo) :
      5 / 4 + (C₁ * A₀ / (1 - ρ / b)) * Hglob < d :=
    (add_le_add le_rfl (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hC₁ hA.le) hden.le) hHglob.le)).trans_lt hdrift
  have hglobal := hsupport (s := s) (A₀ := A₀) (b := (b : ℝ)) (R := R) (ρ := ρ)
    (q := q) (T := T) (H := Hglob) (c := d) hs hA.le hbR hR hRmax hρ hρ1 hρb hq hqE
    hHglob.le hglobT (hdriftFor Cs ((le_max_right Cp Cs).trans (le_max_right Cj (max Cp Cs))))
    (hdR.trans_lt (by norm_num)) N S
  have hsupportA : ∀ t ∈ Icc (0 : ℝ) Hglob, ∀ z ∈ torusBox, a < ‖z - torusCenter‖ →
      S.transportedScalar (P.finiteInitialPeriodicDensity s A₀ b R ρ N) t z = 0 := by
    intro t ht z hz hn
    exact hglobal t ht z hz (hdRa.trans_lt hn)
  let ai₀ := Cb * ρ * radScale R ρ k * (1 + Dcap)
  let ai := cellA * radScale R ρ k / 64
  obtain ⟨hai₀, hbuffer, hai1, hinterfaceBuffer⟩ :=
    canonicalPrefix_capture_particle_buffer hR hRmax hρ hρ1 hCb.le hDcap.le hbufferSmall k
  have hCwCb : Cw + 2 ≤ Cb := by
    dsimp only [Cb, radialStageRadiusConstant]
    have hh : 0 ≤ 4 * Cr / ((b : ℝ) * (1 - b)) := by positivity [sub_pos.mpr hbR1]
    linarith only [hh]
  have hCwDuration : Cw + 2 ≤ Cb * (1 + Dcap) := by
    nlinarith only [hCwCb, mul_nonneg hCb.le hDcap.le]
  have hpastBuffer : ∀ t ∈ Icc (0 : ℝ) entrance,
      ∀ z ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N k,
        ‖S.forward t z - torusCenter‖ ≤ ai₀ := by
    intro t ht z hz
    refine (hpastParticles t ht z hz).trans ?_
    convert mul_le_mul_of_nonneg_right hCwDuration (mul_nonneg hρ.le hrk.le) using 1
      <;> dsimp only [ai₀] <;> ring
  have hpower (n : ℕ) : circularCaptureBlockMultiplier ℓ ^ n =
      Real.exp (sigma * ((n : ℝ) * circularCaptureBlockTime ℓ)) := by
    rw [circularCaptureBlockMultiplier_eq_exp, ← Real.exp_nat_mul]
    congr 1
    ring
  have hEmax : (H * ‖α₀‖) * Real.exp (sigma * Dcap) ≤ δgeom := by
    rw [← hpower]
    have hh' : (H * ‖α₀‖) * circularCaptureBlockMultiplier ℓ ^ Ncap ≤ H * Damp := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hterminal hH.le
    exact hh'.trans hHDamp
  have hEmaxSub (u : ℝ) (hu : u ≤ Dcap) :
      (H * ‖α₀‖) * Real.exp (sigma * u) ≤ δgeom :=
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left hu sigma_pos.le)) (mul_nonneg hH.le (norm_nonneg _))).trans hEmax
  have hh : 0 < h := mul_pos (by linarith only [hC₀]) (pow_pos hρ _)
  have hhKT : h * Ktarget ≤ δgeom :=
    (mul_le_mul_of_nonneg_left hKtargetBoot.le hh.le).trans (hhK.trans (min_le_right _ _))
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
      (b : ℝ) * finiteEulerUniformRadialCoefficient Kr b R ρ core d δcur * Cb ^ 3 *
        ρ ^ 2 * (1 + u) ^ 3 ≤ Cr / 2 :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith only [hu.1])
      (add_le_add le_rfl hu.2) 3) hcoef).trans hcubic
  have hclockSub (u : ℝ) (hu : u ≤ Dcap) : Cb * ρ * (1 + u) ≤ Cb * ρ * (1 + Dcap) :=
    mul_le_mul_of_nonneg_left (add_le_add le_rfl hu) (mul_nonneg hCb.le hρ.le)
  have hchartSub (u : ℝ) (hu : u ≤ Dcap) : Cb * ρ * R * (1 + u) ≤ a := by
    calc
      _ = (Cb * ρ * (1 + u)) * R := by ring
      _ ≤ (Cb * ρ * (1 + Dcap)) * R := mul_le_mul_of_nonneg_right (hclockSub u hu) hR.le
      _ = Cb * ρ * R * (1 + Dcap) := by ring
      _ ≤ _ := hchart
  have hcontrol (D : ℝ) (heD : entrance < D) (hDH : D ≤ Hcap)
      (X : ℝ → FiniteCircularIndex k → LittleContourSpace γ)
      (hX : P.ActualCanonicalPrefixTrajectory s A₀ b R ρ a Hglob hR hρ hkN S D X)
      (hXY : EqOn X Ypast (Icc (0 : ℝ) entrance)) :
      let x := canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance X
      let y := canonicalPrefixAlignedCurrentCell A₀ b R ρ k entrance X
      let v := fun n : ℕ => circularConstraintProjectionToTangentCLM hγ hγ1.le
        (y ((n : ℝ) * circularCaptureBlockTime ℓ) - littleCircularReference hγ hγ1)
      let α := fun n => circularConstrainedUnstableProjectionCLM hγ hγ1.le (v n)
      let w := fun n => (v n - α n) - (gseq (α n) 0 - α n)
      (∀ n ≤ Ncap, (n : ℝ) * circularCaptureBlockTime ℓ ≤ ampScale A₀ b k * (D - entrance) →
        (3 / 4 : ℝ) * ‖α₀‖ * circularCaptureBlockMultiplier ℓ ^ n ≤ ‖α n‖ ∧
        ‖α n‖ ≤ (5 / 4 : ℝ) * ‖α₀‖ * circularCaptureBlockMultiplier ℓ ^ n ∧
        ‖w n‖ ≤ (1 / 8 : ℝ) * ‖α₀‖ * circularCaptureBlockMultiplier ℓ ^ n) ∧
      (∀ τ ∈ Icc (0 : ℝ) (ampScale A₀ b k * (D - entrance)),
        ‖x τ k‖ ≤ H * ‖α₀‖ * Real.exp (sigma * τ)) ∧
      (∀ τ ∈ Icc (0 : ℝ) (ampScale A₀ b k * (D - entrance)), weightedFamilyNorm h k (x τ) ≤ Ktarget) ∧
      (∀ τ ∈ Icc (0 : ℝ) (ampScale A₀ b k * (D - entrance)),
        ∀ z ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N k,
        ‖S.forward (physicalTimeFromNormalized (ampScale A₀ b k) entrance τ) z - torusCenter‖ ≤
          Cb * ρ * radScale R ρ k * (1 + τ)) ∧
      ∀ τ ∈ Icc (0 : ℝ) (ampScale A₀ b k * (D - entrance)),
        let vc := circularConstraintProjectionToTangentCLM hγ hγ1.le
          (circularCoRotationCLM γ τ (y τ) - littleCircularReference hγ hγ1)
        ‖vc - gseq (circularConstrainedUnstableProjectionCLM hγ hγ1.le vc) 0‖ ≤ Eg *
          ((W0 + Fbar * Bpoly) * (Damp / cs + 1) * ρ ^ 3 +
            3 * (E * κ) * Damp / (lam - qbar) +
            Bpoly * ρ ^ 6 * (1 + (Ncap : ℝ) * Tblock) ^ 4 + κ * Rg) := by
    let u := ampScale A₀ b k * (D - entrance)
    have hu : u ∈ Icc (0 : ℝ) Dcap :=
      ⟨mul_nonneg hAk.le (sub_nonneg.mpr heD.le),
        (mul_le_mul_of_nonneg_left (sub_le_sub_right hDH entrance) hAk.le).trans_eq hscale⟩
    have htimeEnd : entrance + u / ampScale A₀ b k ≤ D := by
      dsimp only [u]
      rw [mul_div_cancel_left₀ _ hAk.ne']
      linarith
    have hentry : X entrance = Ypast entrance := hXY ⟨he, le_rfl⟩
    have hy₀ := canonicalPrefixAlignedCurrentCell_zero_congr A₀ b R ρ k entrance hentry
    dsimp only [ρ] at hy₀
    have hx₀ := canonicalPrefixStageDeviation_zero_congr hγ hγ1 A₀ b R ρ k entrance hentry
    have hz₀ : weightedFamilyNorm h k
        (canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance X 0) ≤ Lseed * h := by
      rw [hx₀]
      exact hinitZ
    have hcur₀ : ‖canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance X 0 k‖ < δcur := by
      rw [hx₀]
      exact hinitCur
    have hcap := hξ (s := s) (A₀ := A₀) (R := R) (q := q) (T := T)
      (Hglob := Hglob) (a := a) (d := d) (Dphys := D) (entrance := entrance)
      (Dcap := u) (η := δgeom) (Δ := Δ) (Damp := Damp) (cs := cs) (W0 := W0)
      hs hA hR hq hqE hRmax hρ1 hρhalf hhalf hρcore hsepU hsepL hh1 hhK hζ
      hβ hνlo hνup hCtRw hglobT (hdriftFor Cj (le_max_left _ _)) hdR ha ha16 hdpos hRchart.le hgeom
      (he.trans heD.le) he hu.1 (hu.2.trans hlogcap) hδgeom.le hδgeoma hancient hΔ houter
      (hcubicSub u hu) ((hclockSub u hu.2).trans hinnerCore) ((hclockSub u hu.2).trans hinnerChart)
      (hchartSub u hu.2)
      ((mul_le_mul_of_nonneg_left (hclockSub u hu.2) (by norm_num : (0 : ℝ) ≤ 8)).trans hsep)
      hκcap hDamp hcomp hHDamp N k Ncap hkN hNcap hu.2 htimeEnd hsmallCap hpolyCap
      S hS X hX hz₀ hcur₀ hstart
    have hcap' := hcap
      (by simpa only [Nat.cast_zero, zero_mul, ρ, hy₀] using ha₀)
      (by simpa only [Nat.cast_zero, zero_mul, ρ, hy₀] using hterminal)
      (by simpa only [Nat.cast_zero, zero_mul, ρ, hy₀] using hw₀)
      (by simpa only [Nat.cast_zero, zero_mul, ρ, hy₀] using hsource) hcs hW0
      (by simpa only [Nat.cast_zero, zero_mul, ρ, hy₀] using hseedLow)
      (by simpa only [Nat.cast_zero, zero_mul, ρ, hy₀] using hwScale)
    simpa only [Nat.cast_zero, zero_mul, ρ, hy₀] using hcap'
  run_tac do IO.eprintln "parent-capture: proved all provisional future controls"
  obtain ⟨X, hX, hXY⟩ := hpastExtend (s := s) (A₀ := A₀) (b := (b : ℝ))
    (R := R) (ρ := ρ) (q := q) (T := T) (Hcap := Hcap) (Hglob := Hglob)
    (a := a) (ai₀ := ai₀) (ai := ai) (η := δgeom) (c := d) (entrance := entrance)
    hs hA.le hbR hR hRmax hρ hρ128 hρb hq hqE hHcapPos hHcap hglobT
    (hdriftFor Cp ((le_max_left Cp Cs).trans (le_max_right Cj (max Cp Cs))))
    (hdR.trans (by norm_num)) hRchart ha16 hai₀ hbuffer hai1 hδgeom.le hδgeom16 hδgeomgap
    hsize hancient he heHcap.le hkN S hS hsupportA hinterfaceBuffer Ypast hYpast hpastGeom hpastBuffer
    (by
      intro D heD hDH X hX hXY t ht
      have hc := hcontrol D heD hDH X hX hXY
      let τ := ampScale A₀ b k * (t - entrance)
      have hτ : τ ∈ Icc (0 : ℝ) (ampScale A₀ b k * (D - entrance)) :=
        ⟨mul_nonneg hAk.le (sub_nonneg.mpr ht.1),
          mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 entrance) hAk.le⟩
      have hτcap : τ ≤ Dcap := hτ.2.trans
        ((mul_le_mul_of_nonneg_left (sub_le_sub_right hDH entrance) hAk.le).trans_eq hscale)
      have htime : physicalTimeFromNormalized (ampScale A₀ b k) entrance τ = t := by
        dsimp only [physicalTimeFromNormalized, τ]
        rw [mul_div_cancel_left₀ _ hAk.ne']
        ring
      have htube := canonicalPrefix_material_tube_of_joint_controls hγ hγ1 A₀ b hR hρ k entrance τ X
        hh hh1 hKtarget.le hhKT (hc.2.2.1 τ hτ) ((hc.2.1 τ hτ).trans (hEmaxSub τ hτcap))
      rw [htime] at htube
      refine ⟨htube, ?_⟩
      intro z hz
      have hp := hc.2.2.2.1 τ hτ z hz
      rw [htime] at hp
      exact hp.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hτcap)
        (by positivity : 0 ≤ Cb * ρ * radScale R ρ k)))
  run_tac do IO.eprintln "parent-capture: extended SAME actual material prefix"
  have hc := hcontrol Hcap heHcap le_rfl X hX hXY
  rw [hscale] at hc
  let y := canonicalPrefixAlignedCurrentCell A₀ b R ρ k entrance X
  let v := fun n : ℕ => circularConstraintProjectionToTangentCLM hγ hγ1.le
    (y ((n : ℝ) * circularCaptureBlockTime ℓ) - littleCircularReference hγ hγ1)
  let α := fun n => circularConstrainedUnstableProjectionCLM hγ hγ1.le (v n)
  let w := fun n => (v n - α n) - (gseq (α n) 0 - α n)
  have hgrid : ∀ n ≤ Ncap,
      (3 / 4 : ℝ) * ‖α₀‖ * circularCaptureBlockMultiplier ℓ ^ n ≤ ‖α n‖ ∧
      ‖α n‖ ≤ (5 / 4 : ℝ) * ‖α₀‖ * circularCaptureBlockMultiplier ℓ ^ n ∧
      ‖w n‖ ≤ (1 / 8 : ℝ) * ‖α₀‖ * circularCaptureBlockMultiplier ℓ ^ n := by
    intro n hn
    exact hc.1 n hn (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hn) (circularCaptureBlockTime_pos hℓ).le)
  have htimes : MapsTo (physicalTimeFromNormalized (ampScale A₀ b k) entrance)
      (Icc (0 : ℝ) Dcap) (Icc (0 : ℝ) Hcap) := by
    intro τ hτ
    exact ⟨add_nonneg he (div_nonneg hτ.1 hAk.le),
      add_le_add le_rfl (div_le_div_of_nonneg_right hτ.2 hAk.le)⟩
  have hyc : ContinuousOn y (Icc (0 : ℝ) Dcap) := by
    exact (contourParameterShiftFamilyCLM γ
      (circularRetardedMaterialShift 0 (ampScale A₀ b k * entrance))).continuous.comp_continuousOn
      (continuousOn_canonicalPrefixAbsoluteCell A₀ b R ρ k entrance hX.continuous htimes (Fin.last k))
  have hy₀ := canonicalPrefixAlignedCurrentCell_zero_congr A₀ b R ρ k entrance
    (hXY ⟨he, le_rfl⟩)
  dsimp only [ρ] at hy₀
  have hcoSection : HasFirstCircularCoRotatedCaptureSection hγ hγ1 y Dcap δhit := by
    exact exists_first_circularCoRotated_capture_section hγ hγ1 Ncap ℓ y hDcap.le hyc
      (by simpa only [y, ρ, hy₀] using hhitStart) (hhitEnd.trans (hgrid Ncap le_rfl).1)
  run_tac do IO.eprintln "parent-capture: obtained original first co-rotated section"
  refine ⟨X, hX, hXY, hgrid, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2, hcoSection, ?_⟩
  obtain ⟨τ, hτ, hvalue, hfirst⟩ := hcoSection
  refine ⟨τ, hτ, ?_, hvalue, hfirst⟩
  exact ⟨lt_add_of_pos_right entrance (div_pos hτ.1 hAk),
    add_le_add le_rfl (div_le_div_of_nonneg_right hτ.2 hAk.le)⟩

end CircularMaterialTransferProfile
end Euler2D

end
