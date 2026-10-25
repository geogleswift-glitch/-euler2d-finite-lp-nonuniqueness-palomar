module

public import RequestProject.Euler.CircularParentCaptureScaleTrajectory
public import RequestProject.Euler.CircularCoupledParentCaptureEntrance
public import RequestProject.Euler.CircularParentCaptureLogarithmicCount
public import RequestProject.Euler.CircularCoupledParentCaptureScaleChoice
public import RequestProject.Euler.CircularCapturePhysicalScaleBaseTimeBudget
public import RequestProject.Euler.CircularActualDeepestScaleCapturedFamily

/-! Actual capture on the SAME Euler system after its genuine warmup.
The capture count comes from the real entrance seed, all physical budgets
are discharged at R=rho^10 and A0=cA*(1+xi), and the entire actual past is
retained. Capture constants are selected before the transfer ratio and
the future particle entry coefficient. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 64000000
set_option maxRecDepth 10000

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
  circularBanachField circularBanachDomain finiteBaseCurlL2 CircularMaterialTransferProfile.finiteBaseLp

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

def HasActualParentCaptureExtension
    (gseq : CircularConstrainedTangentSpace γ → ℕ → CircularConstrainedTangentSpace γ)
    {s A₀ b R ρ T : ℝ} (hR : 0 < R) (hρ : 0 < ρ)
    {N k : ℕ} (hkN : k ≤ N) {f : Lp ℝ 2 μT}
    (S : BoundedEulerParticleSystem f T) (entrance : ℝ)
    (Ypast : ℝ → FiniteCircularIndex k → LittleContourSpace γ)
    (ℓ : ℕ) (δ ηcur Hcap Cb D₀ Cgraph ξ : ℝ) : Prop :=
  let yPast := canonicalPrefixAlignedCurrentCell A₀ b R ρ k entrance Ypast
  let α₀ := circularConstrainedUnstableProjectionCLM hγ hγ1.le
    (circularConstraintProjectionToTangentCLM hγ hγ1.le (yPast 0 - littleCircularReference hγ hγ1))
  ∃ Ncap : ℕ, 0 < Ncap ∧
    let Dcap := (Ncap : ℝ) * circularCaptureBlockTime ℓ
    Dcap ≤ (6 / sigma) * ξ + D₀ ∧
    ‖α₀‖ * circularCaptureBlockMultiplier ℓ ^ Ncap < (4 * circularCaptureBlockMultiplier ℓ / 3) * δ ∧
    entrance + Dcap / ampScale A₀ b k < T / 2 ∧
    ∃ X : ℝ → FiniteCircularIndex k → LittleContourSpace γ,
      P.ActualCanonicalPrefixTrajectory s A₀ b R ρ (1 / 16) T hR hρ hkN S
        (entrance + Dcap / ampScale A₀ b k) X ∧
      EqOn X Ypast (Icc (0 : ℝ) entrance) ∧
      let x := canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance X
      let y := canonicalPrefixAlignedCurrentCell A₀ b R ρ k entrance X
      let v := fun n : ℕ => circularConstraintProjectionToTangentCLM hγ hγ1.le
        (y ((n : ℝ) * circularCaptureBlockTime ℓ) - littleCircularReference hγ hγ1)
      let α := fun n => circularConstrainedUnstableProjectionCLM hγ hγ1.le (v n)
      let w := fun n => v n - gseq (α n) 0
      (∀ n ≤ Ncap,
        (3 / 4 : ℝ) * ‖α₀‖ * circularCaptureBlockMultiplier ℓ ^ n ≤ ‖α n‖ ∧
        ‖α n‖ ≤ (5 / 4 : ℝ) * ‖α₀‖ * circularCaptureBlockMultiplier ℓ ^ n ∧
        ‖w n‖ ≤ (1 / 8 : ℝ) * ‖α₀‖ * circularCaptureBlockMultiplier ℓ ^ n) ∧
      (∀ u ∈ Icc (0 : ℝ) Dcap, ‖x u k‖ ≤ Hcap * ‖α₀‖ * Real.exp (sigma * u)) ∧
      (∀ u ∈ Icc (0 : ℝ) Dcap, ‖x u k‖ ≤ ηcur) ∧
      (∀ u ∈ Icc (0 : ℝ) Dcap, ‖x u k‖ ≤ ηcur * Real.exp (-sigma * (Dcap - u))) ∧
      (∀ u ∈ Icc (0 : ℝ) Dcap, weightedFamilyNorm (2 * ρ ^ 6) k (x u) ≤ 1) ∧
      (∀ u ∈ Icc (0 : ℝ) Dcap, ∀ z ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N k,
        ‖S.forward (physicalTimeFromNormalized (ampScale A₀ b k) entrance u) z - torusCenter‖ ≤
          Cb * ρ * radScale R ρ k * (1 + u)) ∧
      (∀ u ∈ Icc (0 : ℝ) Dcap,
        let vc := circularConstraintProjectionToTangentCLM hγ hγ1.le
          (circularCoRotationCLM γ u (y u) - littleCircularReference hγ hγ1)
        ‖vc - gseq (circularConstrainedUnstableProjectionCLM hγ hγ1.le vc) 0‖ ≤ Cgraph * ρ ^ 3) ∧
      HasFirstCircularCoRotatedCaptureSection hγ hγ1 y Dcap δ ∧
      ∃ u ∈ Ioc (0 : ℝ) Dcap,
        physicalTimeFromNormalized (ampScale A₀ b k) entrance u ∈
          Ioc entrance (entrance + Dcap / ampScale A₀ b k) ∧
        ‖circularConstrainedUnstableProjectionCLM hγ hγ1.le
          (circularConstraintProjectionToTangentCLM hγ hγ1.le
            (circularCoRotationCLM γ u (y u) - littleCircularReference hγ hγ1))‖ = δ ∧
        ∀ t ∈ Ico (0 : ℝ) u,
          ‖circularConstrainedUnstableProjectionCLM hγ hγ1.le
            (circularConstraintProjectionToTangentCLM hγ hγ1.le
              (circularCoRotationCLM γ t (y t) - littleCircularReference hγ hγ1))‖ < δ

theorem exists_uniform_actualCoupled_parent_capture_of_warmup {Rflow r₀ : ℝ}
    (hRflow : 0 < Rflow) (hr₀ : 0 < r₀)
    {Xflow : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hflow : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) Rflow) period Xflow)
    (hd : ContDiffAt ℝ 2 (fun W => Xflow W period) (littleCircularReference hγ hγ1))
    (hfix : Xflow (littleCircularReference hγ hγ1) period = littleCircularReference hγ hγ1)
    (harea : ∀ W ∈ ball (littleCircularReference hγ hγ1) Rflow, ∀ i,
      littleContourArea γ (Xflow W period i) = littleContourArea γ (W i))
    {gseq : CircularConstrainedTangentSpace γ → ℕ → CircularConstrainedTangentSpace γ}
    (hg : IsLocalWeightedBackwardGraph
      (banachDoubleReturn (circularConstrainedReturnMap hγ hγ1 (fun W => Xflow W period)))
      (circularConstrainedUnstableProjectionCLM hγ hγ1.le) circularAncientBackwardWeight r₀ gseq) :
    ∃ Kself : ℝ≥0, 0 < Kself ∧ ∃ Cr > 0, ∃ Cd > 0, ∃ F > 0,
    ∃ η > 0, η ≤ cellA / 16 ∧ η ≤ (1 - cellA) / 16 ∧
    ∃ δmax > 0, ∃ ℓ : ℕ, 0 < ℓ ∧ ∃ Hcap > 0,
    ∀ b : ℝ≥0, 0 < b → b < 1 / 4 →
    (b : ℝ) * Kself + (b : ℝ) *
      (finiteInnerLabelLittleRowCoefficient (γ : ℝ) (cellA / 2)
        (circularCanonicalCellNormBudget hγ hγ1) / (2 - 1)) < sigma / 4 →
    ∀ Cpre Dpre Kw Kcur κ δ : ℝ,
    0 ≤ Cpre → 0 ≤ Dpre → 0 ≤ Kw → 0 ≤ Kcur → 0 < κ →
    0 < δ → δ < δmax →
    let Cw := Cpre * (1 + Dpre)
    let Cb := radialStageRadiusConstant Cr Cw b
    let Bpoly := finiteCurrentPolynomialForcingCoefficient (γ : ℝ) (cellA / 2)
      (circularCanonicalCellNormBudget hγ hγ1) Cb b Cd + 1
    F * Bpoly ≤ (κ * ‖circularConstrainedUnstableEmbeddingCLM hγ hγ1.le 1‖) / 32 →
    ∃ D₀ > 0, ∃ Cgraph > 0,
    ∀ Dbase Lentry Dentry : ℝ, 0 ≤ Dbase → 0 ≤ Lentry → 0 ≤ Dentry →
    ∀ {s q T : ℝ}, ∀ [Fact (1 ≤ ENNReal.ofReal q)],
    ∀ (hs : s ≤ 0) (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q),
    0 < T → (∀ i, ‖(P.ancient s i).val - circularReferenceC1 hγ hγ1 i‖ ≤ η) →
    ∃ cA > 0, Dbase / cA < T ∧ ∀ᶠ ξ : ℝ in atTop,
      let ρ := Real.exp (-ξ)
      let hρ := Real.exp_pos (-ξ)
      let R := ρ ^ 10
      let hR := pow_pos hρ 10
      let A₀ := cA * (1 + ξ)
      let h := 2 * ρ ^ 6
      ∀ N k : ℕ, ∀ hkN : k ≤ N,
      ∀ S : BoundedEulerParticleSystem
        (finiteBaseCurlL2 (A₀ := A₀) (b := (b : ℝ)) (ρ := ρ) hR hρ hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := (b : ℝ)) (ρ := ρ) (q := q) hs hR hρ) N) T,
      IsFourfoldBoundedEulerParticleSystem S →
      ∀ {H : ℝ}, 0 ≤ H → ∀ Y : ℝ → FiniteCircularIndex k → LittleContourSpace γ,
      P.ActualCanonicalPrefixTrajectory s A₀ b R ρ (1 / 16) T hR hρ hkN S H Y →
      ∀ entrance : ℝ, 0 ≤ entrance →
      let e := entrance + Dpre / ampScale A₀ b k
      e ≤ H → ampScale A₀ b k * e ≤ Lentry * ξ + Dentry →
      (∀ t ∈ Icc (0 : ℝ) entrance,
        let x := canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k 0 Y (ampScale A₀ b k * t)
        weightedFamilyNorm h k x ≤ h ∧ ‖x k‖ ≤ h) →
      (∀ u ∈ Icc (0 : ℝ) Dpre,
        weightedFamilyNorm h k (canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance Y u) ≤ Kw * h) →
      (∀ u ∈ Icc (0 : ℝ) Dpre,
        ‖canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance Y u k‖ ≤ Kcur * h) →
      (∀ t ∈ Icc (0 : ℝ) entrance, ∀ z ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N k,
        ‖S.forward t z - torusCenter‖ ≤ 2 * ρ * radScale R ρ k) →
      (∀ u ∈ Icc (0 : ℝ) Dpre, ∀ z ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N k,
        ‖S.forward (physicalTimeFromNormalized (ampScale A₀ b k) entrance u) z - torusCenter‖ ≤
          Cpre * ρ * radScale R ρ k * (1 + u)) →
      κ * ρ ^ 6 ≤ ‖canonicalPrefixMaterialGrowingCoordinate hγ hγ1 A₀ b R ρ k Y (ampScale A₀ b k * e)‖ →
      (let v := circularConstraintProjectionToTangentCLM hγ hγ1.le
          (canonicalPrefixAlignedCurrentCell A₀ b R ρ k e Y 0 - littleCircularReference hγ hγ1)
       let α := circularConstrainedUnstableProjectionCLM hγ hγ1.le v
       ‖v - gseq α 0‖ ≤ ‖α‖ / 32) →
      P.HasActualParentCaptureExtension gseq (s := s) (A₀ := A₀) (b := (b : ℝ))
        hR hρ hkN S e Y ℓ δ η Hcap Cb D₀ Cgraph ξ := by
  obtain ⟨Kself, hKself, rw, hrw, Ctw, hCtw, Cgeo, Ctc, Cdc, Cr, Kr,
    hCgeo, hCtc, hCdc, hCr, hKr, ℓ, hℓ, qc, hqc, hqgap,
    C, hC, dcap, hdcap, hdr, E, hE, F, hF, rc, hrc, κ₀, hκ₀, ε₀, hε₀,
    Hcap, hHcap, Eg, hEg, Rg, hRg, hcaptureFamily⟩ :=
    P.exists_uniform_actualParent_capture_scale_trajectory hRflow hr₀ hflow hd hfix harea hg
  let L := circularCanonicalCellNormBudget hγ hγ1
  let core := cellA / 2
  let Cu := finiteInnerLabelLittleRowCoefficient (γ : ℝ) (cellA / 2) L
  let Cl := finiteOuterLabelLittleRowCoefficient (γ : ℝ) core L L
  let torusRow := finiteTorusLabelLittleRowCoefficient (γ : ℝ) L
  have hL : 0 < L := circularCanonicalCellNormBudget_pos hγ hγ1
  have hcore : 0 < core := half_pos cellA_pos
  have hcorei (i : Fin 2) : core ≤ 3 * circularContourRadii i / 4 := by
    have hi := (circularContourRadii_bounds i).2.1
    dsimp only [core]
    linarith only [hi, cellA_pos]
  have hcauchyRow : 0 ≤ cauchyContourNormBudget 5 (γ : ℝ) 1 (cellA / 2) L :=
    (cauchySpatialDerivativeBudget_nonneg 5 (by norm_num : (0 : ℝ) ≤ 1)
      (half_pos cellA_pos) 0).trans (le_max_left _ _)
  have hradialWeight : 0 ≤ circularRadialPerturbationWeight :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (circularContourRadii_bounds i).1.le)
  have hCu : 0 ≤ Cu := by unfold Cu finiteInnerLabelLittleRowCoefficient; positivity
  have hCl : 0 ≤ Cl := by
    have hi : 0 ≤ interiorContourNormBudget (γ : ℝ) 1 core L L :=
      (interiorSpatialDerivativeBudget_nonneg (M := 1) (a := core) (by norm_num) hL 0).trans
        (le_max_left _ _)
    unfold Cl finiteOuterLabelLittleRowCoefficient
    positivity
  have htorusRow : 0 ≤ torusRow := finiteTorusLabelLittleRowCoefficient_nonneg hL.le
  obtain ⟨qbar, hqcbar, hqbar, hqbarGap⟩ := exists_capture_larger_slow_rate hqc hqgap
  obtain ⟨Fbar, hFbar, hcaptureAll⟩ := hcaptureFamily qbar hqbar hqbarGap
  let lam := circularCaptureBlockMultiplier ℓ
  let Tblock := circularCaptureBlockTime ℓ
  have hlam : 1 < lam := by nlinarith only [hqc, hqgap]
  have hqbarLam : qbar < lam := by nlinarith only [hqbar, hqbarGap, sq_nonneg (qbar - 1)]
  have hTblock : 0 < Tblock := circularCaptureBlockTime_pos hℓ
  let δcur := min rc (cellA / 4)
  have hδcur : 0 < δcur := lt_min hrc (div_pos cellA_pos (by norm_num))
  have hσgap : 0 < sigma - sigma / 3 := by linarith only [sigma_pos]
  have hCu1 : 0 < Cu + 1 := by linarith only [hCu]
  let η := min (δcur / 2) (min (cellA / 16)
    (min ((1 - cellA) / 16) ((sigma - sigma / 3) / (Cu + 1))))
  have hη : 0 < η := lt_min (half_pos hδcur)
    (lt_min (div_pos cellA_pos (by norm_num))
      (lt_min (div_pos (sub_pos.mpr cellA_lt_one) (by norm_num)) (div_pos hσgap hCu1)))
  have hηδ : η < δcur := (min_le_left _ _).trans_lt (half_lt_self hδcur)
  have hη16 : η ≤ cellA / 16 := (min_le_right _ _).trans (min_le_left _ _)
  have hηgap : η ≤ (1 - cellA) / 16 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hηsmall : η ≤ (sigma - sigma / 3) / (Cu + 1) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hmargin : (Cu + 1) * η / (2 * (sigma - sigma / 3)) ≤ (1 : ℝ) / 2 := by
    have hh := (le_div_iff₀ hCu1).mp hηsmall
    apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hσgap)).mpr
    nlinarith only [hh]
  let Damp := min (dcap / 3) (min ((qbar - qc) / (3 * C))
    (min (η / Hcap) ((lam - 1) / (288 * C))))
  have hDamp : 0 < Damp := lt_min (div_pos hdcap (by norm_num))
    (lt_min (div_pos (sub_pos.mpr hqcbar) (by positivity))
      (lt_min (div_pos hη hHcap) (div_pos (sub_pos.mpr hlam) (by positivity))))
  have hDcap : 3 * Damp ≤ dcap := by
    have hh : Damp ≤ dcap / 3 := min_le_left _ _
    linarith only [hh]
  have hDlam : qc + 3 * C * Damp ≤ qbar := by
    have hh := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 3) hC)).mp
      ((min_le_right _ _).trans (min_le_left _ _) : Damp ≤ (qbar - qc) / (3 * C))
    nlinarith only [hh]
  have hDgeom : Hcap * Damp ≤ η := by
    have hh : Damp ≤ η / Hcap := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    simpa only [mul_comm] using (le_div_iff₀ hHcap).mp hh
  have hDcapture : 9 * C * Damp / (lam - 1) < 1 / 16 := by
    have hh : Damp ≤ (lam - 1) / (288 * C) :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    have hh' := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 288) hC)).mp hh
    apply (div_lt_iff₀ (sub_pos.mpr hlam)).mpr
    nlinarith only [hh', hlam]
  let δmax := 3 * Damp / (8 * lam)
  have hδmax : 0 < δmax := div_pos (by positivity) (by linarith only [hlam])
  refine ⟨Kself, hKself, Cr, hCr, Cdc, hCdc, F, hF, η, hη, hη16, hηgap,
    δmax, hδmax, ℓ, hℓ, Hcap, hHcap, ?_⟩
  intro b hb hbquarter hslow Cpre Dpre Kw Kcur κ δ
    hCpre hDpre hKw hKcur hκ hδ hδcap
  dsimp only
  let Cw := Cpre * (1 + Dpre)
  let Cb := radialStageRadiusConstant Cr Cw b
  let Bpoly := finiteCurrentPolynomialForcingCoefficient (γ : ℝ) (cellA / 2) L Cb b Cdc + 1
  intro hsource
  have hbR : 0 < (b : ℝ) := hb
  have hb1 : b < 1 := hbquarter.trans (by norm_num)
  have hCw : 0 ≤ Cw := mul_nonneg hCpre (by linarith only [hDpre])
  have hCb : 0 < Cb := radialStageRadiusConstant_pos hCr hCw hbR hb1
  have hcauchy : 0 ≤ cauchyContourNormBudget 5 (γ : ℝ) 1 (cellA / 2) L :=
    (cauchySpatialDerivativeBudget_nonneg 5 (by norm_num : (0 : ℝ) ≤ 1)
      (half_pos cellA_pos) 0).trans (le_max_left _ _)
  have htor : 0 ≤ torusCorrectionContourBudget (γ : ℝ) L := by
    unfold torusCorrectionContourBudget
    positivity
  have hBpoly : 0 < Bpoly := by
    unfold Bpoly finiteCurrentPolynomialForcingCoefficient
    positivity [finiteLabelMassBound_nonneg]
  let cs := κ * ‖circularConstrainedUnstableEmbeddingCLM hγ hγ1.le 1‖
  have hcs : 0 < cs := mul_pos hκ (norm_circularConstrainedUnstableEmbedding_one_pos hγ hγ1.le)
  obtain ⟨Cseed, hCseed, hentranceAll⟩ :=
    P.exists_eventually_actualFinite_coupled_parent_capture_entrance hbR hKw hKcur
  obtain ⟨D₀, hD₀, hcount⟩ := exists_parentCapture_first_crossing_logarithmic_count hℓ hδ hcs
  obtain ⟨Cgraph, hCgraph, herror⟩ := exists_eventually_circularCapture_scale_error_rhoThree_budget
    (W0 := Cseed) (Fbar := Fbar) (Bpoly := Bpoly) (Damp := Damp) (cs := cs)
    (E := E) (lam := lam) (qbar := qbar) (Rg := Rg) (Ktor := Ctc * torusRow)
    (L := 6 / sigma) (D₀ := D₀) hEg hCseed.le hFbar.le hBpoly.le hDamp.le hcs hE.le hqbarLam
    hRg.le (mul_nonneg hCtc.le htorusRow)
  have hbK : 0 < (b : ℝ) * Kself := mul_pos hbR (NNReal.coe_pos.mpr hKself)
  have hηa : η ≤ cellA / 4 := hη16.trans (by linarith only [cellA_pos])
  have hCapture := hcaptureAll b hb hb1 Cw hCw
    (core := core) (C₀ := 2) (ν₀ := (b : ℝ) * Kself / 2) (νbar := sigma / 3)
    (Lseed := Kw) (δgeom := η) (δcur := δcur) (D₀ := D₀) (Ktarget := 1) (Kboot := 2)
    hcore hcorei (by norm_num) (half_pos hbK) (by linarith only [sigma_pos])
    hKw (by norm_num) (by norm_num) hη hηδ (min_le_right _ _) (min_le_left _ _)
    hη16 hηgap hmargin
  have hξgap := eventually_circularCapture_selected_ratio_gap
    (K := (Kself : ℝ)) (b := (b : ℝ)) (Cup := Cu) (Cdown := Cl) (C₀ := 2)
    (Ctorus := 3 * Ctw * torusRow) hbR hCu hCl (by norm_num) (by positivity) hslow
  have hseedLimit : Tendsto (fun ξ : ℝ => Cseed * Real.exp (-ξ) ^ 6) atTop (𝓝 0) := by
    simpa only [zero_pow (by decide : (6 : ℕ) ≠ 0), mul_zero] using
      (Real.tendsto_exp_neg_atTop_nhds_zero.pow 6).const_mul Cseed
  have hcurLimit : Tendsto (fun ξ : ℝ => (2 * Kcur) * Real.exp (-ξ) ^ 6) atTop (𝓝 0) := by
    simpa only [zero_pow (by decide : (6 : ℕ) ≠ 0), mul_zero] using
      (Real.tendsto_exp_neg_atTop_nhds_zero.pow 6).const_mul (2 * Kcur)
  refine ⟨D₀, hD₀, Cgraph, hCgraph, ?_⟩
  intro Dbase Lentry Dentry hDbase hLentry hDentry s q T _ hs hq hqE hT hancient
  obtain ⟨cA, hcA, hTimeBase, hphysical⟩ :=
    exists_eventually_circularCapture_physical_scale_budget_with_base_time
      (b := (b : ℝ)) (a := 1 / 16) (Cgeo := Cgeo) (Lclock := Lentry + 6 / sigma)
      (Dclock := Dentry + D₀) (Dbase := Dbase) (Lnorm := L)
      (Znorm := ‖littleCircularReference hγ hγ1‖) (η := η)
      hT hbR hb1.le (by norm_num) hCgeo
      (add_nonneg hLentry (div_nonneg (by norm_num) sigma_pos.le))
      (add_nonneg hDentry hD₀.le) hDbase hL.le (norm_nonneg _) hη.le
  let p : DeepestCaptureScaleData :=
    { b := b, L := L, core := core, rw := rw, Kboot := 2, δgeom := η, δcur := δcur,
      Cb := Cb, Cr := Cr, Kr := Kr, d := 0, Cgeo := Cgeo, A₀ := cA, T := T,
      torusW := Ctw * torusRow, torusC := Ctc * torusRow, Cl := Cl, C := C, E := E,
      lam := lam, Damp := Damp, κ₀ := κ₀, ε₀ := ε₀, Bpoly := Bpoly, F := F,
      seed := cs, referenceNorm := ‖littleCircularReference hγ hγ1‖, q := q,
      Ncap := 0, blockTime := Tblock }
  have hp : p.CoupledAdmissible :=
    ⟨hbR, hcore, hrw, hη, hCr, hcA, hCgeo.le, hT.le, hκ₀, hε₀, hcs, hDcapture⟩
  have hbudgets := p.eventually_coupled_logarithmic_parent_budget hp hCb.le hBpoly.le hE.le
    (mul_nonneg hCtc.le htorusRow) hTblock (6 / sigma) D₀
  have hEntrance := hentranceAll (δgeom := η) hs hcA hq hqE hT.le hη.le hηa hη hancient
  refine ⟨cA, hcA, hTimeBase, ?_⟩
  filter_upwards [hbudgets, hCapture, hξgap, hEntrance, hphysical, herror,
    hseedLimit.eventually (gt_mem_nhds hδ), hcurLimit.eventually (gt_mem_nhds hδcur)]
      with ξ hbudgetξ hcaptureξ hgapξ hEntranceξ hphysicalξ herrorξ hseedSmall hcurSmall
  let ρ := Real.exp (-ξ)
  let R := ρ ^ 10
  let A₀ := cA * (1 + ξ)
  let h := 2 * ρ ^ 6
  let d := 2 + 4 * Cgeo * A₀ * T
  have hρ : 0 < ρ := Real.exp_pos (-ξ)
  have hR : 0 < R := pow_pos hρ 10
  obtain ⟨hξ, _hρpos, hρ1, hρbhalf, _hRpos, hRρ, hRhalf, hA, hdpos,
    hdrift, hdR, hdRa, hRchart, hgeom, hsize, htimeAll⟩ := hphysicalξ
  try dsimp only
  intro N k hkN S hS H hH Y hY entrance hentrance hEnd hclockBound
    hpast hweighted hcur hparticlesPast hparticlesWindow hGrowing hcone
  let e := entrance + Dpre / ampScale A₀ b k
  let yPast := canonicalPrefixAlignedCurrentCell A₀ b R ρ k e Y
  let v₀ := circularConstraintProjectionToTangentCLM hγ hγ1.le
    (yPast 0 - littleCircularReference hγ hγ1)
  let α₀ := circularConstrainedUnstableProjectionCLM hγ hγ1.le v₀
  have hAmp : 0 < ampScale A₀ b k := div_pos hA (pow_pos hbR k)
  have he : 0 ≤ e := add_nonneg hentrance (div_nonneg hDpre hAmp.le)
  obtain ⟨hYpast, hPastGeometry, hPastParticles, hEntryWeighted, hEntryCurrent,
    hEntryParticles, hcell, hfour, hareaY, hchartY, hαrange, hvUpper, hαUpper,
    hcoord, hLower⟩ := hEntranceξ N k hkN S hS hH Y hY entrance Dpre Cpre
      hentrance hDpre hCpre hEnd hpast hweighted hcur hparticlesPast hparticlesWindow
  obtain ⟨hαpos, hαlower⟩ := hLower κ hκ hGrowing
  have hαδ : ‖α₀‖ < δ := hαUpper.trans_lt hseedSmall
  obtain ⟨Ncap, hNcap, hcross, hterminal, hDlog⟩ := hcount ξ ‖α₀‖ hαpos hαlower hαδ
  let Dcap := (Ncap : ℝ) * Tblock
  have hDcapPos : 0 < Dcap := mul_pos (Nat.cast_pos.mpr hNcap) hTblock
  obtain ⟨hbudget, hbuffer⟩ := hbudgetξ Ncap hDlog
  have hterminalDamp : ‖α₀‖ * lam ^ Ncap ≤ Damp := by
    have hh := (lt_div_iff₀ (by linarith only [hlam] : 0 < 8 * lam)).mp hδcap
    dsimp only [δmax] at hδcap
    have hscaled : (4 * lam / 3) * δ < Damp := by
      have hmult := (lt_div_iff₀ (by linarith only [hlam] : 0 < 8 * lam)).mp hδcap
      nlinarith only [hmult, hDamp]
    exact hterminal.le.trans hscaled.le
  have hTotal : 0 ≤ ampScale A₀ b k * e + Dcap :=
    add_nonneg (mul_nonneg hAmp.le he) hDcapPos.le
  have hTotalBound : ampScale A₀ b k * e + Dcap ≤ (Lentry + 6 / sigma) * ξ + (Dentry + D₀) := by
    linarith only [hclockBound, hDlog]
  have htimeHalf : e + Dcap / ampScale A₀ b k < T / 2 := by
    have ht := htimeAll (ampScale A₀ b k * e + Dcap) hTotal hTotalBound k
    have heq : (ampScale A₀ b k * e + Dcap) / ampScale A₀ b k =
        e + Dcap / ampScale A₀ b k := by
      rw [add_div, mul_div_cancel_left₀ e hAmp.ne']
    rw [heq] at ht
    exact ht
  have htime : e + Dcap / ampScale A₀ b k < T := htimeHalf.trans (half_lt_self hT)
  have hβ : 0 ≤ 3 * (Ctw * torusRow * R ^ 8) + weightedInteractionRowFeedback b Cu Cl 2 ρ := by
    have hfb := weightedInteractionRowFeedback_nonneg (NNReal.coe_nonneg b) hCu hCl (by norm_num) hgapξ.1
    positivity
  have hrate := hgapξ.2 R hR.le hRρ
  have hrateEq : weightedNormPropagationExponent Kself b Cu Cl 2 (3 * Ctw * torusRow) R ρ =
      ((b * Kself : ℝ≥0) : ℝ) + (3 * (Ctw * torusRow * R ^ 8) + weightedInteractionRowFeedback b Cu Cl 2 ρ) := by
    simp only [weightedNormPropagationExponent, NNReal.coe_mul]
    ring
  rw [hrateEq] at hrate
  have hrateLo : (b : ℝ) * Kself / 2 ≤ ((b * Kself : ℝ≥0) : ℝ) +
      (3 * (Ctw * torusRow * R ^ 8) + weightedInteractionRowFeedback b Cu Cl 2 ρ) := by
    change (b : ℝ) * Kself / 2 ≤ _
    linarith only [hrate.1, hbK]
  have hwEq : (v₀ - α₀) - (gseq α₀ 0 - α₀) = v₀ - gseq α₀ 0 := by module
  have hw₀ : ‖(v₀ - α₀) - (gseq α₀ 0 - α₀)‖ ≤ ‖α₀‖ / 32 := by rw [hwEq]; exact hcone
  have hwScale : ‖(v₀ - α₀) - (gseq α₀ 0 - α₀)‖ ≤ Cseed * ρ ^ 6 :=
    hw₀.trans ((div_le_self (norm_nonneg _) (by norm_num)).trans hαUpper)
  have hSource : F * Bpoly * ρ ^ 6 ≤ ‖α₀‖ / 32 := by
    have hsource' : F * Bpoly ≤ cs / 32 := hsource
    calc
      _ ≤ (cs / 32) * ρ ^ 6 := mul_le_mul_of_nonneg_right hsource' (pow_nonneg hρ.le 6)
      _ = (cs * ρ ^ 6) / 32 := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hαlower (by norm_num)
  have hEntryCur : ‖canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k e Y 0 k‖ < δcur := by
    have hh : Kcur * h < δcur := by
      simpa only [h, mul_assoc, mul_left_comm, mul_comm] using hcurSmall
    exact hEntryCurrent.trans_lt hh
  have hActual := hcaptureξ (s := s) (A₀ := A₀) (R := R) (q := q) (T := T)
    (Hglob := T) (a := 1 / 16) (d := d) (entrance := e) (Δ := 1)
    (Damp := Damp) (cs := cs) (W0 := Cseed) hs hA hR hq hqE Ncap hNcap
    hRhalf hbudget.one hbudget.bhalf hbudget.sq_bhalf hbudget.initial_sep hbudget.initial_core
    hbudget.upper_sep hbudget.lower_sep hbudget.weight hbudget.weighted_bootstrap hbudget.row
    hβ hrateLo hrate.2 hbudget.torus hT le_rfl hdrift hdR hdRa (by norm_num) le_rfl hdpos
    hRchart hgeom hsize he hDlog hancient (by norm_num) hbudget.outer_source hbudget.radial
    hbudget.particle_core hbudget.particle_outer hbudget.particle_box hbudget.particle_sep hbuffer
    hbudget.kappa hDcap hDlam hDgeom N k hkN htime hbudget.capture hbudget.forcing
    S hS Y hYpast hPastGeometry hPastParticles hEntryWeighted hEntryCur hEntryParticles
    hαpos hterminalDamp hw₀ hSource hcs hCseed.le hαlower hwScale δ hαδ hcross
  obtain ⟨X, hX, hEq, hgrids, henv, hweight, hparticle, hgraph, hfirst, hhit⟩ := hActual
  have hclockExp : Real.exp (sigma * Dcap) = lam ^ Ncap := by
    have heq : lam = Real.exp (sigma * Tblock) := circularCaptureBlockMultiplier_eq_exp ℓ
    rw [heq, ← Real.exp_nat_mul]
    congr 1
    dsimp only [Dcap]
    ring
  have hterminalEnv : Hcap * ‖α₀‖ * Real.exp (sigma * Dcap) ≤ η := by
    calc
      _ = Hcap * (‖α₀‖ * lam ^ Ncap) := by rw [hclockExp]; ring
      _ ≤ Hcap * Damp := mul_le_mul_of_nonneg_left hterminalDamp hHcap.le
      _ ≤ _ := hDgeom
  have hbackward (u : ℝ) (hu : u ∈ Icc (0 : ℝ) Dcap) :
      ‖canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k e X u k‖ ≤
        η * Real.exp (-sigma * (Dcap - u)) := by
    have hfactor : Real.exp (sigma * u) =
        Real.exp (sigma * Dcap) * Real.exp (-sigma * (Dcap - u)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      _ ≤ Hcap * ‖α₀‖ * Real.exp (sigma * u) := henv u hu
      _ = (Hcap * ‖α₀‖ * Real.exp (sigma * Dcap)) * Real.exp (-sigma * (Dcap - u)) := by
        rw [hfactor]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hterminalEnv (Real.exp_pos _).le
  have hnear (u : ℝ) (hu : u ∈ Icc (0 : ℝ) Dcap) :
      ‖canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k e X u k‖ ≤ η := by
    have hh : Real.exp (-sigma * (Dcap - u)) ≤ 1 := by
      have hn : -sigma * (Dcap - u) ≤ 0 := by
        nlinarith only [mul_nonneg sigma_pos.le (sub_nonneg.mpr hu.2)]
      simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hn
    exact (hbackward u hu).trans ((mul_le_mul_of_nonneg_left hh hη.le).trans_eq (mul_one η))
  change P.HasActualParentCaptureExtension gseq (s := s) (A₀ := A₀) (b := (b : ℝ))
    hR hρ hkN S e Y ℓ δ η Hcap Cb D₀ Cgraph ξ
  dsimp only [HasActualParentCaptureExtension]
  refine ⟨Ncap, hNcap, hDlog, hterminal, htimeHalf, X, hX, hEq, ?_, henv, hnear, hbackward,
    hweight, hparticle, ?_, hfirst, hhit⟩
  · intro n hn
    have hg := hgrids n hn
    refine ⟨hg.1, hg.2.1, ?_⟩
    convert hg.2.2 using 1 <;> congr 1 <;> module
  · intro u hu
    exact (hgraph u hu).trans (herrorξ R Dcap hR.le hRρ hDcapPos.le hDlog)

end CircularMaterialTransferProfile
end Euler2D

end
