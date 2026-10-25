module

public import RequestProject.Euler.CircularCanonicalJointStageScaleClosure
public import RequestProject.Euler.CircularDeepestCaptureInitialState
public import RequestProject.Euler.CircularFinitePrefixEventContinuation
public import RequestProject.Euler.CircularFiniteUniformSupport
public import RequestProject.Euler.CircularCanonicalControlGeometry
public import RequestProject.Euler.ContinuousCaptureSection
public import RequestProject.Euler.CircularCoRotatedCaptureSection

/-! Construct the actual deepest-prefix trajectory through its full
capture horizon, then take a genuine first projected section. Each
provisional stopping interval is controlled before continuation. -/

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

theorem exists_uniform_actualDeepest_capture_scale_trajectory {Rflow r₀ : ℝ}
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
      ∀ b : ℝ≥0, 0 < b → b < 1 →
      ∃ Cgeo Ctc Cdc Cr Kr : ℝ,
      0 < Cgeo ∧ 0 < Ctc ∧ 0 < Cdc ∧ 0 < Cr ∧ 0 < Kr ∧
      ∃ ℓ : ℕ, 0 < ℓ ∧ ∃ qc : ℝ, 1 < qc ∧ qc ^ 2 < circularCaptureBlockMultiplier ℓ ∧
      let Tblock := circularCaptureBlockTime ℓ
      let lam := circularCaptureBlockMultiplier ℓ
      let Pu := circularConstrainedUnstableProjectionCLM hγ hγ1.le
      let g := fun v => gseq v 0 - v
      let Cb := radialStageRadiusConstant Cr 0 b
      ∃ C > 0, ∃ dcap > 0, dcap ≤ r₀ / 2 ∧ ∃ E > 0, ∃ F > 0, ∃ rc > 0,
      ∃ κ₀ > 0, ∃ ε₀ > 0, ∃ H > 0, ∃ Eg > 0, ∃ Rg > 0,
      ∀ qbar : ℝ, 1 < qbar → qbar ^ 2 < lam → ∃ Fbar > 0,
      ∀ {core C₀ ν₀ νbar δgeom δcur D₀ Ktarget Kboot : ℝ},
      0 < core → (∀ i, core ≤ 3 * circularContourRadii i / 4) →
      2 ≤ C₀ → 0 < ν₀ → νbar < sigma →
      0 < Ktarget → Ktarget < Kboot → 0 < δgeom → δgeom < δcur →
      δcur ≤ cellA / 4 → δcur ≤ rc →
      δgeom ≤ cellA / 16 → δgeom ≤ (1 - cellA) / 16 →
      (finiteInnerLabelLittleRowCoefficient (γ : ℝ) (cellA / 2) L + 1) * δgeom /
        (C₀ * (sigma - νbar)) ≤ Ktarget / 2 →
      ∀ᶠ ξ : ℝ in atTop,
      let ρ := Real.exp (-ξ)
      let h := C₀ * ρ ^ 6
      ∀ {s A₀ R q T Hglob a d Δ Damp cs W0 : ℝ},
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
      Dcap ≤ (6 / sigma) * ξ + D₀ →
      (∀ i, ‖(P.ancient s i).val - circularReferenceC1 hγ hγ1 i‖ ≤ δgeom) → 0 ≤ Δ →
      (2 * (b : ℝ) * C₀ * Kboot * (Cl + Ctc * finiteTorusLabelLittleRowCoefficient (γ : ℝ) L)) * ρ ^ 2 ≤ Δ →
      b * finiteEulerUniformRadialCoefficient Kr b R ρ core d δcur * Cb ^ 3 *
        ρ ^ 2 * (1 + Dcap) ^ 3 ≤ Cr / 2 →
      Cb * ρ * (1 + Dcap) ≤ core / 2 → Cb * ρ * (1 + Dcap) ≤ d →
      Cb * ρ * R * (1 + Dcap) ≤ a → 8 * (Cb * ρ * (1 + Dcap)) ≤ cellA / 2 →
      κ ≤ κ₀ → 3 * Damp ≤ dcap → qc + 3 * C * Damp ≤ qbar → H * Damp ≤ δgeom →
      ∀ N : ℕ, Dcap / ampScale A₀ b N < Hglob →
      9 * C * Damp / (lam - 1) + 3 * (E * κ) * (Ncap : ℝ) ≤ 1 / 16 →
      Bpoly * ρ ^ 6 * (1 + (Ncap : ℝ) * Tblock) ^ 4 + κ * (3 * Damp) ≤ ε₀ →
      ∀ S : BoundedEulerParticleSystem
        (finiteBaseCurlL2 (A₀ := A₀) (b := (b : ℝ)) (ρ := ρ) hR (Real.exp_pos (-ξ)) hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := (b : ℝ)) (ρ := ρ) (q := q) hs hR (Real.exp_pos (-ξ))) N) T,
      IsFourfoldBoundedEulerParticleSystem S →
      let v₀ := circularConstraintProjectionToTangentCLM hγ hγ1.le
        (P.ancient s - littleCircularReference hγ hγ1)
      let α₀ := Pu v₀
      let w₀ := (v₀ - α₀) - g α₀
      0 < ‖α₀‖ → ‖α₀‖ * lam ^ Ncap ≤ Damp →
      ‖w₀‖ ≤ ‖α₀‖ / 32 → F * Bpoly * ρ ^ 6 ≤ ‖α₀‖ / 32 →
      0 < cs → 0 ≤ W0 → cs * ρ ^ 6 ≤ ‖α₀‖ → ‖w₀‖ ≤ W0 * ρ ^ 6 →
      ∀ δhit : ℝ, ‖α₀‖ < δhit → δhit ≤ (3 / 4 : ℝ) * ‖α₀‖ * lam ^ Ncap →
      ∃ X : ℝ → FiniteCircularIndex N → LittleContourSpace γ,
        P.ActualCanonicalPrefixTrajectory s A₀ b R ρ a Hglob hR (Real.exp_pos (-ξ)) le_rfl S
          (Dcap / ampScale A₀ b N) X ∧
      let x := canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ N 0 X
      let y := canonicalPrefixAlignedCurrentCell A₀ b R ρ N 0 X
      let v := fun n : ℕ => circularConstraintProjectionToTangentCLM hγ hγ1.le
        (y ((n : ℝ) * Tblock) - littleCircularReference hγ hγ1)
      let α := fun n => Pu (v n)
      let w := fun n => (v n - α n) - g (α n)
      (∀ n ≤ Ncap,
        (3 / 4 : ℝ) * ‖α₀‖ * lam ^ n ≤ ‖α n‖ ∧
        ‖α n‖ ≤ (5 / 4 : ℝ) * ‖α₀‖ * lam ^ n ∧
        ‖w n‖ ≤ (1 / 8 : ℝ) * ‖α₀‖ * lam ^ n) ∧
      (∀ τ ∈ Icc (0 : ℝ) Dcap, ‖x τ N‖ ≤ H * ‖α₀‖ * Real.exp (sigma * τ)) ∧
      (∀ τ ∈ Icc (0 : ℝ) Dcap, weightedFamilyNorm h N (x τ) ≤ Ktarget) ∧
      (∀ τ ∈ Icc (0 : ℝ) Dcap,
        let vc := circularConstraintProjectionToTangentCLM hγ hγ1.le
          (circularCoRotationCLM γ τ (y τ) - littleCircularReference hγ hγ1)
        ‖vc - gseq (Pu vc) 0‖ ≤ Eg *
          ((W0 + Fbar * Bpoly) * (Damp / cs + 1) * ρ ^ 3 +
            3 * (E * κ) * Damp / (lam - qbar) +
            Bpoly * ρ ^ 6 * (1 + (Ncap : ℝ) * Tblock) ^ 4 + κ * Rg)) ∧
      HasFirstCircularCoRotatedCaptureSection hγ hγ1 y Dcap δhit ∧
      ∃ τ ∈ Ioc (0 : ℝ) Dcap, τ / ampScale A₀ b N ∈ Ioc (0 : ℝ) (Dcap / ampScale A₀ b N) ∧
        ‖Pu (circularConstraintProjectionToTangentCLM hγ hγ1.le
          (y τ - littleCircularMaterialContours hγ hγ1 τ))‖ = δhit ∧
        ∀ u ∈ Ico (0 : ℝ) τ,
          ‖Pu (circularConstraintProjectionToTangentCLM hγ hγ1.le
            (y u - littleCircularMaterialContours hγ hγ1 u))‖ < δhit := by
  run_tac do IO.eprintln "capture-scale: entered body"
  obtain ⟨Ce, hCe, hextend⟩ := P.exists_uniform_actualPrefix_trajectory_or_event
  obtain ⟨Cs, hCs, hsupport⟩ := P.exists_uniform_finiteEuler_support_bound
  have hJoint := P.exists_uniform_actualCanonical_joint_stage_scale_closure (Rflow := Rflow) (r₀ := r₀)
      (Y := Y) (gseq := gseq) hRflow hr₀ hY hd hfix harea hg
  obtain ⟨Kself, hKself, rw, hrw, Ctw, hCtw, hstages⟩ := hJoint
  run_tac do IO.eprintln "capture-scale: selected joint constants"
  refine ⟨Kself, hKself, rw, hrw, Ctw, hCtw, ?_⟩
  intro b hb hb1
  have hbR : 0 < (b : ℝ) := hb
  have hbR1 : (b : ℝ) < 1 := hb1
  have hStage := hstages b hb hb1 0 le_rfl
  obtain ⟨Cj, Ctc, Cdc, Cr, Kr, hCj, hCtc, hCdc, hCr, hKr, ℓ, hℓ, qc, hqc, hqgap,
    C, hC, dcap, hdcap, hdr, E, hE, F, hF, rc, hrc, κ₀, hκ₀, ε₀, hε₀, H, hH,
    Eg, hEg, Rg, hRg, hstageFamily⟩ :=
    hStage
  let Cgeo := max Cj (max Ce Cs)
  let L := circularCanonicalCellNormBudget hγ hγ1
  let Tblock := circularCaptureBlockTime ℓ
  let lam := circularCaptureBlockMultiplier ℓ
  let Cb := radialStageRadiusConstant Cr 0 b
  have hCb : 0 < Cb := radialStageRadiusConstant_pos hCr le_rfl hbR hbR1
  refine ⟨Cgeo, Ctc, Cdc, Cr, Kr, hCj.trans_le (le_max_left _ _), hCtc, hCdc, hCr, hKr,
    ℓ, hℓ, qc, hqc, hqgap, C, hC, dcap, hdcap, hdr, E, hE, F, hF, rc, hrc,
    κ₀, hκ₀, ε₀, hε₀, H, hH, Eg, hEg, Rg, hRg, ?_⟩
  intro qbar hqbar hqbarGap
  obtain ⟨Fbar, hFbar, hstage⟩ := hstageFamily qbar hqbar hqbarGap
  run_tac do IO.eprintln "capture-scale: selected sharp rate"
  refine ⟨Fbar, hFbar, ?_⟩
  intro core C₀ ν₀ νbar δgeom δcur D₀ Ktarget Kboot hcore hcorei hC₀ hν₀ hνbar
    hKtarget hKtargetBoot hδgeom hδgc hδcura hδcurc hδgeom16 hδgeomgap hmargin
  have hδgeoma : δgeom ≤ cellA / 4 := hδgc.le.trans hδcura
  have hδcur : 0 < δcur := hδgeom.trans hδgc
  have hξstage := hstage (Lseed := 0) (D₀ := D₀) hcore hcorei hC₀ hν₀ hνbar le_rfl
    hKtarget hKtargetBoot hδgeom hδgc hδcura hδcurc hmargin
  filter_upwards [hξstage] with ξ hξ
  run_tac do IO.eprintln "capture-scale: selected small-scale stage"
  try dsimp only
  let ρ := Real.exp (-ξ)
  let h := C₀ * ρ ^ 6
  intro s A₀ R q T Hglob a d Δ Damp cs W0 _ hs hA hR hq hqE
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
    hHglob hglobT hdrift hdR hdRa ha ha16 hdpos hRchart hgeom hsize hlogcap hancient hΔ houter
    hcubic hinnerCore hinnerChart hchart hsep hκcap hDamp hcomp hHDamp N hHcap
    hsmallCap hpolyCap S hS
  let v₀ := circularConstraintProjectionToTangentCLM hγ hγ1.le (P.ancient s - littleCircularReference hγ hγ1)
  let α₀ := circularConstrainedUnstableProjectionCLM hγ hγ1.le v₀
  try dsimp only
  intro ha₀ hterminal hw₀ hsource hcs hW0 hseedLow hwScale δhit hhitStart hhitEnd
  run_tac do IO.eprintln "capture-scale: introduced initial hypotheses"
  have hρ : 0 < ρ := Real.exp_pos _
  have hρb : ρ < (b : ℝ) := hρhalf.trans_lt (by linarith only [hbR])
  have hden : 0 < 1 - ρ / b := sub_pos.mpr ((div_lt_one hbR).mpr hρb)
  have hAN : 0 < ampScale A₀ b N := by unfold ampScale; positivity
  have hDcap : 0 < Dcap := mul_pos (Nat.cast_pos.mpr hNcap) (circularCaptureBlockTime_pos hℓ)
  let Hcap := Dcap / ampScale A₀ b N
  have hHcapPos : 0 < Hcap := div_pos hDcap hAN
  have hscale : ampScale A₀ b N * Hcap = Dcap := by
    dsimp only [Hcap]
    field_simp [hAN.ne']
  have hdriftFor (C₁ : ℝ) (hC₁ : C₁ ≤ Cgeo) :
      5 / 4 + (C₁ * A₀ / (1 - ρ / b)) * Hglob < d :=
    (add_le_add le_rfl (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hC₁ hA.le) hden.le) hHglob.le)).trans_lt hdrift
  have hglobal := hsupport (s := s) (A₀ := A₀) (b := (b : ℝ)) (R := R) (ρ := Real.exp (-ξ))
    (q := q) (T := T) (H := Hglob) (c := d) hs hA.le hbR hR hRmax hρ hρ1 hρb hq hqE hHglob.le hglobT
    (hdriftFor Cs ((le_max_right Ce Cs).trans (le_max_right Cj (max Ce Cs))))
    (hdR.trans_lt (by norm_num)) N S
  have hsupportA : ∀ t ∈ Icc (0 : ℝ) Hglob, ∀ z ∈ torusBox, a < ‖z - torusCenter‖ →
      S.transportedScalar (P.finiteInitialPeriodicDensity s A₀ b R ρ N) t z = 0 := by
    intro t ht z hz hn
    exact hglobal t ht z hz (hdRa.trans_lt hn)
  obtain ⟨ai, hai, hai1, hbuffer⟩ := exists_deepest_prefix_particle_buffer hR hRmax hρ hρ1 N
  have hinner (t : ℝ) : ∀ z ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N N,
      ‖S.forward t z - torusCenter‖ ≤ 0 := by
    intro z hz
    rw [P.finiteInnerActiveInitialLabels_deepest] at hz
    exact False.elim (Set.notMem_empty z hz)
  have hAncientNorm : ‖P.ancient s - littleCircularReference hγ hγ1‖ ≤ δgeom :=
    P.norm_ancient_sub_reference_le hδgeom.le hancient
  have hpower (n : ℕ) : circularCaptureBlockMultiplier ℓ ^ n =
      Real.exp (sigma * ((n : ℝ) * circularCaptureBlockTime ℓ)) := by
    rw [circularCaptureBlockMultiplier_eq_exp, ← Real.exp_nat_mul]
    congr 1
    ring
  have hEmax : (H * ‖α₀‖) * Real.exp (sigma * Dcap) ≤ δgeom := by
    rw [← hpower]
    have hbound : (H * ‖α₀‖) * circularCaptureBlockMultiplier ℓ ^ Ncap ≤ H * Damp := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hterminal hH.le
    exact hbound.trans hHDamp
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
      (b : ℝ) * finiteEulerUniformRadialCoefficient Kr b R ρ core d δcur * Cb ^ 3 * ρ ^ 2 * (1 + u) ^ 3 ≤ Cr / 2 :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith only [hu.1])
      (add_le_add le_rfl hu.2) 3) hcoef).trans hcubic
  have hclockSub (u : ℝ) (hu : u ≤ Dcap) : Cb * ρ * (1 + u) ≤ Cb * ρ * (1 + Dcap) :=
    mul_le_mul_of_nonneg_left (add_le_add le_rfl hu) (mul_nonneg hCb.le hρ.le)
  have hchartSub (u : ℝ) (hu : u ≤ Dcap) : Cb * ρ * R * (1 + u) ≤ a := by
    calc
      _ = (Cb * ρ * (1 + u)) * R := by ring
      _ ≤ (Cb * ρ * (1 + Dcap)) * R := mul_le_mul_of_nonneg_right (hclockSub u hu) hR.le
      _ = Cb * ρ * R * (1 + Dcap) := by ring
      _ ≤ a := hchart
  have hcontrol (D : ℝ) (hD : 0 < D) (hDH : D ≤ Hcap)
      (X : ℝ → FiniteCircularIndex N → LittleContourSpace γ)
      (hX : P.ActualCanonicalPrefixTrajectory s A₀ b R ρ a Hglob hR hρ le_rfl S D X) :
      let x := canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ N 0 X
      let y := canonicalPrefixAlignedCurrentCell A₀ b R ρ N 0 X
      let v := fun n : ℕ => circularConstraintProjectionToTangentCLM hγ hγ1.le
        (y ((n : ℝ) * circularCaptureBlockTime ℓ) - littleCircularReference hγ hγ1)
      let α := fun n => circularConstrainedUnstableProjectionCLM hγ hγ1.le (v n)
      let w := fun n => (v n - α n) - (gseq (α n) 0 - α n)
      (∀ n ≤ Ncap, (n : ℝ) * circularCaptureBlockTime ℓ ≤ ampScale A₀ b N * D →
        (3 / 4 : ℝ) * ‖α₀‖ * circularCaptureBlockMultiplier ℓ ^ n ≤ ‖α n‖ ∧
        ‖α n‖ ≤ (5 / 4 : ℝ) * ‖α₀‖ * circularCaptureBlockMultiplier ℓ ^ n ∧
        ‖w n‖ ≤ (1 / 8 : ℝ) * ‖α₀‖ * circularCaptureBlockMultiplier ℓ ^ n) ∧
      (∀ τ ∈ Icc (0 : ℝ) (ampScale A₀ b N * D), ‖x τ N‖ ≤ H * ‖α₀‖ * Real.exp (sigma * τ)) ∧
      (∀ τ ∈ Icc (0 : ℝ) (ampScale A₀ b N * D), weightedFamilyNorm h N (x τ) ≤ Ktarget) ∧
      (∀ τ ∈ Icc (0 : ℝ) (ampScale A₀ b N * D), ∀ z ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N N,
        ‖S.forward (physicalTimeFromNormalized (ampScale A₀ b N) 0 τ) z - torusCenter‖ ≤
          Cb * ρ * radScale R ρ N * (1 + τ)) ∧
      ∀ τ ∈ Icc (0 : ℝ) (ampScale A₀ b N * D),
        let vc := circularConstraintProjectionToTangentCLM hγ hγ1.le
          (circularCoRotationCLM γ τ (y τ) - littleCircularReference hγ hγ1)
        ‖vc - gseq (circularConstrainedUnstableProjectionCLM hγ hγ1.le vc) 0‖ ≤ Eg *
          ((W0 + Fbar * Bpoly) * (Damp / cs + 1) * ρ ^ 3 +
            3 * (E * κ) * Damp / (lam - qbar) +
            Bpoly * ρ ^ 6 * (1 + (Ncap : ℝ) * Tblock) ^ 4 + κ * Rg) := by
    let u := ampScale A₀ b N * D
    have hu : u ∈ Icc (0 : ℝ) Dcap :=
      ⟨mul_nonneg hAN.le hD.le, (mul_le_mul_of_nonneg_left hDH hAN.le).trans_eq hscale⟩
    have htimeEnd : (0 : ℝ) + u / ampScale A₀ b N ≤ D := by
      dsimp only [u]
      rw [zero_add, mul_div_cancel_left₀ D hAN.ne']
    have hy₀ := P.actualCanonicalPrefix_initial_aligned_deepest hR hρ N S X hX
    dsimp only [ρ] at hy₀
    have hz₀ : weightedFamilyNorm h N (canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ N 0 X 0) ≤ 0 * h := by
      rw [P.actualCanonicalPrefix_initial_weighted_zero hR hρ le_rfl S X hX h, zero_mul]
    have hcur₀ : ‖canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ N 0 X 0 N‖ < δcur := by
      rw [P.actualCanonicalPrefix_initial_deepest_deviation hR hρ N S X hX]
      exact hAncientNorm.trans_lt hδgc
    have hcap := hξ (s := s) (A₀ := A₀) (R := R) (q := q) (T := T)
      (Hglob := Hglob) (a := a) (d := d) (Dphys := D) (entrance := 0)
      (Dcap := u) (η := δgeom) (Δ := Δ) (Damp := Damp) (cs := cs) (W0 := W0)
      hs hA hR hq hqE hRmax hρ1 hρhalf hhalf hρcore hsepU hsepL hh1 hhK hζ
      hβ hνlo hνup hCtRw hglobT (hdriftFor Cj (le_max_left _ _)) hdR ha ha16 hdpos hRchart.le hgeom
      hD.le le_rfl hu.1 (hu.2.trans hlogcap) hδgeom.le hδgeoma hancient hΔ houter
      (hcubicSub u hu) ((hclockSub u hu.2).trans hinnerCore) ((hclockSub u hu.2).trans hinnerChart)
      (hchartSub u hu.2)
      ((mul_le_mul_of_nonneg_left (hclockSub u hu.2) (by norm_num : (0 : ℝ) ≤ 8)).trans hsep)
      hκcap hDamp hcomp hHDamp N N Ncap le_rfl hNcap hu.2 htimeEnd hsmallCap hpolyCap
      S hS X hX hz₀ hcur₀ (by simpa only [zero_mul] using hinner 0)
    have hcap' := hcap
      (by simpa only [Nat.cast_zero, zero_mul, hy₀] using ha₀)
      (by simpa only [Nat.cast_zero, zero_mul, hy₀] using hterminal)
      (by simpa only [Nat.cast_zero, zero_mul, hy₀] using hw₀)
      (by simpa only [Nat.cast_zero, zero_mul, hy₀] using hsource) hcs hW0
      (by simpa only [Nat.cast_zero, zero_mul, hy₀] using hseedLow)
      (by simpa only [Nat.cast_zero, zero_mul, hy₀] using hwScale)
    simpa only [Nat.cast_zero, zero_mul, hy₀] using hcap'
  run_tac do IO.eprintln "capture-scale: proved stopped controls"
  have hexists := hextend (s := s) (A₀ := A₀) (b := (b : ℝ)) (R := R) (ρ := ρ) (q := q)
    (T := T) (Hcap := Hcap) (Hglob := Hglob) (a := a) (ai₀ := 0) (ai := ai) (η := δgeom) (c := d)
    (N := N) (k := N)
    hs hA.le hbR hR hRmax hρ hρ128 hρb hq hqE hHcapPos hHcap hglobT
    (hdriftFor Ce ((le_max_left Ce Cs).trans (le_max_right Cj (max Ce Cs))))
    (hdR.trans (by norm_num)) hRchart ha16 le_rfl hai hai1 hδgeom.le hδgeom16 hδgeomgap
    hsize hancient le_rfl S hS hsupportA hbuffer
  try dsimp only at hexists
  have hpath :
      (∃ X : ℝ → FiniteCircularIndex N → LittleContourSpace γ,
        P.ActualCanonicalPrefixTrajectory s A₀ b R ρ a Hglob hR hρ le_rfl S Hcap X) ∨
      ∃ t ∈ Icc (0 : ℝ) Hcap, ∃ X : ℝ → FiniteCircularIndex N → LittleContourSpace γ,
        P.ActualCanonicalPrefixTrajectory s A₀ b R ρ a Hglob hR hρ le_rfl S t X ∧ False :=
    hexists (fun _ _ => False) (by
    intro D hD hDH X hX _ t ht
    have hc := hcontrol D hD hDH X hX
    let τ := ampScale A₀ b N * t
    have hτ : τ ∈ Icc (0 : ℝ) (ampScale A₀ b N * D) :=
      ⟨mul_nonneg hAN.le ht.1, mul_le_mul_of_nonneg_left ht.2 hAN.le⟩
    have hτcap : τ ≤ Dcap := hτ.2.trans ((mul_le_mul_of_nonneg_left hDH hAN.le).trans_eq hscale)
    have htime : physicalTimeFromNormalized (ampScale A₀ b N) 0 τ = t := by
      dsimp only [physicalTimeFromNormalized, τ]
      rw [zero_add, mul_div_cancel_left₀ t hAN.ne']
    have htube := canonicalPrefix_material_tube_of_joint_controls hγ hγ1 A₀ b hR hρ N 0 τ X
      hh hh1 hKtarget.le hhKT (hc.2.2.1 τ hτ) ((hc.2.1 τ hτ).trans (hEmaxSub τ hτcap))
    rw [htime] at htube
    exact ⟨htube, hinner t⟩)
  obtain ⟨X, hX⟩ : ∃ X : ℝ → FiniteCircularIndex N → LittleContourSpace γ,
      P.ActualCanonicalPrefixTrajectory s A₀ b R ρ a Hglob hR hρ le_rfl S Hcap X := by
    rcases hpath with hx | ⟨t, ht, X, hX, hf⟩
    · exact hx
    · exact False.elim hf
  have hc := hcontrol Hcap hHcapPos le_rfl X hX
  run_tac do IO.eprintln "capture-scale: obtained actual path"
  rw [hscale] at hc
  let y := canonicalPrefixAlignedCurrentCell A₀ b R ρ N 0 X
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
  have hcoSection : HasFirstCircularCoRotatedCaptureSection hγ hγ1 y Dcap δhit := by
    obtain ⟨τ, hτ, _, hvalue, hfirst⟩ := P.exists_first_actualDeepest_coRotated_section
      hA hbR hR hρ N Ncap ℓ hℓ S X hX le_rfl hhitStart
      (hhitEnd.trans (hgrid Ncap le_rfl).1)
    exact ⟨τ, hτ, hvalue, hfirst⟩
  refine ⟨X, hX, hgrid, hc.2.1, hc.2.2.1, hc.2.2.2.2, hcoSection, ?_⟩
  let z := fun τ : ℝ => circularConstrainedUnstableProjectionCLM hγ hγ1.le
    (circularConstraintProjectionToTangentCLM hγ hγ1.le
      (canonicalPrefixAlignedCurrentCell A₀ b R ρ N 0 X τ - littleCircularMaterialContours hγ hγ1 τ))
  have htimes : MapsTo (physicalTimeFromNormalized (ampScale A₀ b N) 0)
      (Icc (0 : ℝ) Dcap) (Icc (0 : ℝ) Hcap) := by
    intro τ hτ
    exact ⟨by simpa only [physicalTimeFromNormalized, zero_add] using div_nonneg hτ.1 hAN.le,
      by simpa only [physicalTimeFromNormalized, zero_add] using div_le_div_of_nonneg_right hτ.2 hAN.le⟩
  have hyc : ContinuousOn (canonicalPrefixAlignedCurrentCell A₀ b R ρ N 0 X) (Icc (0 : ℝ) Dcap) := by
    have hyEq : canonicalPrefixAlignedCurrentCell A₀ b R ρ N 0 X =
        (fun τ => canonicalPrefixAbsoluteCell A₀ b R ρ N 0 X τ (Fin.last N)) :=
      funext (fun τ => canonicalPrefixAlignedCurrentCell_zero_entrance A₀ b R ρ N X τ)
    rw [hyEq]
    exact continuousOn_canonicalPrefixAbsoluteCell A₀ b R ρ N 0 hX.continuous htimes (Fin.last N)
  have hzc : ContinuousOn z (Icc (0 : ℝ) Dcap) :=
    (circularConstrainedUnstableProjectionCLM hγ hγ1.le).continuous.comp_continuousOn
      ((circularConstraintProjectionToTangentCLM hγ hγ1.le).continuous.comp_continuousOn
        (hyc.sub (contDiff_littleCircularMaterialContours hγ hγ1).continuous.continuousOn))
  have hz₀ : z 0 = α₀ := by
    dsimp only [z]
    rw [P.actualCanonicalPrefix_initial_aligned_deepest hR hρ N S X hX,
      littleCircularMaterialContours_zero]
  have hperiod : Function.Periodic (littleCircularMaterialContours hγ hγ1) (circularCaptureBlockTime ℓ) :=
    (periodic_littleCircularMaterialContours hγ hγ1).nat_mul (2 * ℓ)
  have href : littleCircularMaterialContours hγ hγ1 Dcap = littleCircularReference hγ hγ1 :=
    (hperiod.nat_mul_eq Ncap).trans (littleCircularMaterialContours_zero hγ hγ1)
  have hend : δhit ≤ ‖z Dcap‖ := by
    dsimp only [z]
    rw [href]
    exact hhitEnd.trans (hgrid Ncap le_rfl).1
  obtain ⟨τ, hτ, hhit, hfirst⟩ := exists_first_continuous_norm_section hDcap.le z hzc
    (by rw [hz₀]; exact hhitStart) hend
  exact ⟨τ, hτ, ⟨div_pos hτ.1 hAN, div_le_div_of_nonneg_right hτ.2 hAN.le⟩, hhit, hfirst⟩

end CircularMaterialTransferProfile
end Euler2D

end
