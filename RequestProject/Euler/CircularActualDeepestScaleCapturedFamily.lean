module

public import RequestProject.Euler.CircularDeepestCaptureScaleTrajectory
public import RequestProject.Euler.CircularAncientCaptureEntrance
public import RequestProject.Euler.CircularWeightedNormParameters
public import RequestProject.Euler.CircularFiniteEulerPlanarArea
public import RequestProject.Euler.DeepestCaptureScaleChoice
public import RequestProject.Euler.CircularFlattenedMaterialTransferProfile

/-! Choose all parameters and the original ancient entrance before the
shrinking scale or the cutoff. The resulting original finite Euler
systems have actual deepest trajectories and a fixed positive first
projected section. This is the base stage, not a parent-stage cascade. -/

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
attribute [local irreducible] contourC1GraphSubmodule
attribute [local irreducible] circularConstrainedTangentSubmodule circularConstrainedUnstableProjectionCLM
  circularConstrainedReturnMap circularConstrainedChart circularConstraintProjectionToTangentCLM
  circularBanachField circularBanachDomain

 theorem exists_capture_larger_slow_rate {q lam : ℝ} (hq : 1 < q) (hgap : q ^ 2 < lam) :
    ∃ qbar : ℝ, q < qbar ∧ 1 < qbar ∧ qbar ^ 2 < lam := by
  have hcont : Continuous (fun e : ℝ => (q + e) ^ 2) := by fun_prop
  have hnear : ∀ᶠ e : ℝ in 𝓝 0, (q + e) ^ 2 < lam :=
    hcont.continuousAt.eventually (eventually_lt_nhds (by simpa only [add_zero] using hgap))
  obtain ⟨r, hr, hspec⟩ := Metric.eventually_nhds_iff.mp hnear
  refine ⟨q + r / 2, by linarith only [hr], by linarith only [hq, hr], ?_⟩
  apply hspec
  rw [dist_zero_right, Real.norm_of_nonneg (by positivity)]
  linarith only [hr]

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

def HasActualDeepestScaleCapturedFamilyAt {q T : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q)
    (b : ℝ≥0) (s : ℝ) (hs : s ≤ 0) (A₀ D δ εgeom : ℝ) (gseq : CircularConstrainedTangentSpace γ → ℕ → CircularConstrainedTangentSpace γ)
    (Cerror ξ : ℝ) : Prop :=
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
          ‖canonicalPrefixAlignedCurrentCell A₀ b ρ ρ N 0 X τ - littleCircularMaterialContours hγ hγ1 τ‖ ≤ εgeom / 2) ∧
        (∀ τ ∈ Icc (0 : ℝ) D,
          let vc := circularConstraintProjectionToTangentCLM hγ hγ1.le
            (circularCoRotationCLM γ τ (canonicalPrefixAlignedCurrentCell A₀ b ρ ρ N 0 X τ) -
              littleCircularReference hγ hγ1)
          ‖vc - gseq (circularConstrainedUnstableProjectionCLM hγ hγ1.le vc) 0‖ ≤ Cerror * ρ ^ 3) ∧
        HasFirstCircularCoRotatedCaptureSection hγ hγ1
          (canonicalPrefixAlignedCurrentCell A₀ b ρ ρ N 0 X) D δ ∧
        ∃ τ ∈ Ioc (0 : ℝ) D,
          τ / ampScale A₀ b N ∈ Ioc (0 : ℝ) (D / ampScale A₀ b N) ∧
          ‖circularConstrainedUnstableProjectionCLM hγ hγ1.le
            (circularConstraintProjectionToTangentCLM hγ hγ1.le
              (canonicalPrefixAlignedCurrentCell A₀ b ρ ρ N 0 X τ -
                littleCircularMaterialContours hγ hγ1 τ))‖ = δ ∧
          ∀ u ∈ Ico (0 : ℝ) τ,
            ‖circularConstrainedUnstableProjectionCLM hγ hγ1.le
              (circularConstraintProjectionToTangentCLM hγ hγ1.le
                (canonicalPrefixAlignedCurrentCell A₀ b ρ ρ N 0 X u -
                  littleCircularMaterialContours hγ hγ1 u))‖ < δ

theorem exists_actual_deepest_scale_captured_family_of_samples {Rflow r₀ : ℝ}
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
    (δmax εgeom : ℝ) (hδmax : 0 < δmax) (hεgeom : 0 < εgeom) :
    ∃ b : ℝ≥0, 0 < b ∧ b < 1 / 4 ∧
      bilateral P.moment (((b : ℝ) : ℂ) * (sigma + 5 / 4 * I)) ≠ 0 ∧
      ∃ s : ℝ, ∃ hs : s ≤ 0, ∃ A₀ > 0, ∃ D > 0, ∃ δ > 0, δ < δmax ∧ ∃ Cerror > 0,
        ∀ᶠ ξ : ℝ in atTop,
          P.HasActualDeepestScaleCapturedFamilyAt (T := T) hq hqE b s hs A₀ D δ εgeom gseq Cerror ξ := by
  have hCapture := P.exists_uniform_actualDeepest_capture_scale_trajectory (Rflow := Rflow) (r₀ := r₀)
    (Y := Y) (gseq := gseq) hRflow hr₀ hY hd hfix harea hg
  obtain ⟨Kself, hKself, rw, hrw, Ctw, hCtw, hstages⟩ := hCapture
  let L := circularCanonicalCellNormBudget hγ hγ1
  let core := cellA / 2
  let Cu := finiteInnerLabelLittleRowCoefficient (γ : ℝ) (cellA / 2) L
  let Cl := finiteOuterLabelLittleRowCoefficient (γ : ℝ) core L L
  let torusRow := finiteTorusLabelLittleRowCoefficient (γ : ℝ) L
  have hL : 0 < L := circularCanonicalCellNormBudget_pos hγ hγ1
  have hcore : 0 < core := half_pos cellA_pos
  have hcorei : ∀ i, core ≤ 3 * circularContourRadii i / 4 := by
    intro i
    have hi := (circularContourRadii_bounds i).2.1
    dsimp only [core]
    linarith only [hi, cellA_pos]
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
  obtain ⟨br, hbr, hnonzero, hbK, hbasegap, hgap⟩ :=
    P.exists_nonzeroTransfer_weightedNorm_gap (K := (Kself : ℝ)) (Cup := Cu) (Cdown := Cl)
      (C₀ := 2) (NNReal.coe_pos.mpr hKself) hCu hCl (by norm_num)
  let b : ℝ≥0 := NNReal.mk br hbr.1.le
  have hb : 0 < b := hbr.1
  have hbquarter : b < 1 / 4 := hbr.2
  have hb1 : b < 1 := hbquarter.trans (by norm_num)
  have hStage := hstages b hb hb1
  obtain ⟨Cgeo, Ctc, Cdc, Cr, Kr, hCgeo, hCtc, hCdc, hCr, hKr, ℓ, hℓ, qc, hqc, hqgap,
    C, hC, dcap, hdcap, hdr, E, hE, F, hF, rc, hrc, κ₀, hκ₀, ε₀, hε₀, H, hH,
    Eg, hEg, Rg, hRg, hstageFamily⟩ := hStage
  obtain ⟨qbar, hqcbar, hqbar, hqbarGap⟩ := exists_capture_larger_slow_rate hqc hqgap
  obtain ⟨Fbar, hFbar, hstage⟩ := hstageFamily qbar hqbar hqbarGap
  have hqbarLam : qbar < circularCaptureBlockMultiplier ℓ := by
    nlinarith only [hqbar, hqbarGap, sq_nonneg (qbar - 1)]
  let lam := circularCaptureBlockMultiplier ℓ
  let Tblock := circularCaptureBlockTime ℓ
  let Cb := radialStageRadiusConstant Cr 0 b
  have hlam : 1 < lam := by nlinarith only [hqc, hqgap]
  have hqclam : qc < lam := by nlinarith only [hqc, hqgap]
  have hTblock : 0 < Tblock := circularCaptureBlockTime_pos hℓ
  let δcur := min rc (cellA / 4)
  have hδcur : 0 < δcur := lt_min hrc (div_pos cellA_pos (by norm_num))
  have hσgap : 0 < sigma - sigma / 3 := by linarith only [sigma_pos]
  have hCu1 : 0 < Cu + 1 := by linarith only [hCu]
  let δgeom := min (δcur / 2) (min (cellA / 16)
    (min ((1 - cellA) / 16) ((sigma - sigma / 3) / (Cu + 1))))
  have hδgeom : 0 < δgeom := lt_min (half_pos hδcur)
    (lt_min (div_pos cellA_pos (by norm_num))
      (lt_min (div_pos (sub_pos.mpr cellA_lt_one) (by norm_num)) (div_pos hσgap hCu1)))
  have hδgc : δgeom < δcur := (min_le_left _ _).trans_lt (by linarith only [hδcur])
  have hδgeom16 : δgeom ≤ cellA / 16 := (min_le_right _ _).trans (min_le_left _ _)
  have hδgeomgap : δgeom ≤ (1 - cellA) / 16 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδsmall : δgeom ≤ (sigma - sigma / 3) / (Cu + 1) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hmargin : (Cu + 1) * δgeom / (2 * (sigma - sigma / 3)) ≤ (1 : ℝ) / 2 := by
    have hprod := (le_div_iff₀ hCu1).mp hδsmall
    apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hσgap)).mpr
    nlinarith only [hprod]
  let Damp := min (dcap / 3) (min ((qbar - qc) / (3 * C))
    (min (δgeom / H) (min ((lam - 1) / (288 * C)) (min δmax (εgeom / (2 * H))))))
  have hDamp : 0 < Damp := lt_min (div_pos hdcap (by norm_num))
    (lt_min (div_pos (sub_pos.mpr hqcbar) (by positivity))
      (lt_min (div_pos hδgeom hH) (lt_min (div_pos (sub_pos.mpr hlam) (by positivity))
        (lt_min hδmax (div_pos hεgeom (by positivity))))))
  have hDampRest : Damp ≤ min ((lam - 1) / (288 * C)) (min δmax (εgeom / (2 * H))) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hDampMax : Damp ≤ δmax :=
    hDampRest.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hDampGeom : H * Damp ≤ εgeom / 2 := by
    have hh := hDampRest.trans ((min_le_right _ _).trans (min_le_right _ _))
    have hm := (le_div_iff₀ (show 0 < 2 * H by positivity)).mp hh
    nlinarith only [hm]
  have hDcap : 3 * Damp ≤ dcap := by
    have hh : Damp ≤ dcap / 3 := min_le_left _ _
    linarith only [hh]
  have hDlam : qc + 3 * C * Damp ≤ qbar := by
    have hh : Damp ≤ (qbar - qc) / (3 * C) := (min_le_right _ _).trans (min_le_left _ _)
    have hh' := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 3) hC)).mp hh
    nlinarith only [hh']
  have hDgeom : H * Damp ≤ δgeom := by
    have hh : Damp ≤ δgeom / H :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    simpa only [mul_comm] using (le_div_iff₀ hH).mp hh
  have hDcapture : 9 * C * Damp / (lam - 1) < 1 / 16 := by
    have hh : Damp ≤ (lam - 1) / (288 * C) :=
      hDampRest.trans (min_le_left _ _)
    have hh' := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 288) hC)).mp hh
    apply (div_lt_iff₀ (sub_pos.mpr hlam)).mpr
    nlinarith only [hh', hlam]
  have hEntry := P.exists_actual_ancient_capture_entrance (x := gseq) hg hsamples hlam hDamp hδgeom
  obtain ⟨δhit, hδhit, n, hentry⟩ := hEntry
  dsimp only at hentry
  let s := -(n : ℝ) * (period + period)
  let v₀ := circularConstraintProjectionToTangentCLM hγ hγ1.le
    (P.ancient s - littleCircularReference hγ hγ1)
  let α₀ := circularConstrainedUnstableProjectionCLM hγ hγ1.le v₀
  obtain ⟨hs, hgeom, hα, hαδ, hαr, hv, hw, Ncap, hNcap, hcross, hterminal, hlog, hsource⟩ := hentry
  have hδhitMax : δhit < δmax := by nlinarith only [hcross, hterminal, hDampMax, hDamp]
  let D := (Ncap : ℝ) * Tblock
  have hD : 0 < D := mul_pos (Nat.cast_pos.mpr hNcap) hTblock
  let A₀ := 2 * (D + 1) / T
  have hA : 0 < A₀ := div_pos (by linarith only [hD]) hT
  let d := 2 + 2 * Cgeo * A₀ * T
  have hcat : 0 < Cgeo * A₀ * T := mul_pos (mul_pos hCgeo hA) hT
  have hdpos : 0 < d := by dsimp only [d]; linarith only [hcat]
  have hdrift : 5 / 4 + Cgeo * A₀ * T < d := by dsimp only [d]; linarith only [hcat]
  have htime (N : ℕ) : D / ampScale A₀ b N < T := by
    have hpow : (b : ℝ) ^ N ≤ 1 := pow_le_one₀ (NNReal.coe_nonneg b) (NNReal.coe_le_coe.mpr hb1.le)
    have hAmp : A₀ ≤ ampScale A₀ b N := by
      apply (le_div_iff₀ (pow_pos (NNReal.coe_pos.mpr hb) N)).mpr
      exact mul_le_of_le_one_right hA.le hpow
    have hAmpPos : 0 < ampScale A₀ b N := hA.trans_le hAmp
    apply (div_lt_iff₀ hAmpPos).mpr
    have hAT : A₀ * T = 2 * (D + 1) := by dsimp only [A₀]; field_simp
    have hh := mul_le_mul_of_nonneg_right hAmp hT.le
    nlinarith only [hAT, hh, hD]
  let Bpoly := finiteCurrentPolynomialForcingCoefficient (γ : ℝ) (cellA / 2) L Cb b Cdc + 1
  have hCb : 0 < Cb := radialStageRadiusConstant_pos hCr le_rfl (NNReal.coe_pos.mpr hb)
    (NNReal.coe_lt_coe.mpr hb1)
  have htor : 0 ≤ torusCorrectionContourBudget (γ : ℝ) L := by
    unfold torusCorrectionContourBudget
    positivity
  have hBpoly : 0 ≤ Bpoly := by
    unfold Bpoly finiteCurrentPolynomialForcingCoefficient
    positivity [finiteLabelMassBound_nonneg]
  let Ktor := Ctc * torusRow
  let K1 := Fbar * Bpoly * (Damp / ‖α₀‖ + 1)
  let K2 := 3 * E * Ktor * Damp / (lam - qbar)
  let K3 := Bpoly * (1 + D) ^ 4
  let K4 := Ktor * Rg
  have hKtor : 0 ≤ Ktor := mul_nonneg hCtc.le htorusRow
  have hdenQ : 0 < lam - qbar := sub_pos.mpr hqbarLam
  have hK1 : 0 ≤ K1 := by dsimp only [K1]; positivity
  have hK2 : 0 ≤ K2 := by dsimp only [K2]; positivity
  have hK3 : 0 ≤ K3 := by dsimp only [K3]; positivity
  have hK4 : 0 ≤ K4 := by dsimp only [K4]; positivity
  let Cerror := Eg * (K1 + K2 + K3 + K4) + 1
  have hCerror : 0 < Cerror := by dsimp only [Cerror]; positivity
  let p : DeepestCaptureScaleData :=
    { b := b, L := L, core := core, rw := rw, Kboot := 2, δgeom := δgeom, δcur := δcur,
      Cb := Cb, Cr := Cr, Kr := Kr, d := d, Cgeo := Cgeo, A₀ := A₀, T := T,
      torusW := Ctw * torusRow, torusC := Ctc * torusRow, Cl := Cl, C := C, E := E,
      lam := lam, Damp := Damp, κ₀ := κ₀, ε₀ := ε₀, Bpoly := Bpoly, F := F,
      seed := ‖α₀‖, referenceNorm := ‖littleCircularReference hγ hγ1‖, q := q,
      Ncap := Ncap, blockTime := Tblock }
  have hp : p.Admissible :=
    ⟨NNReal.coe_pos.mpr hb, hcore, hrw, hδgeom, hCr, hdpos, hκ₀, hε₀, hα, hdrift, hDcapture⟩
  have hξbudget := p.eventually_budget hp
  have hξstage := hstage (core := core) (C₀ := 2) (ν₀ := (b : ℝ) * Kself / 2)
    (νbar := sigma / 3) (δgeom := δgeom) (δcur := δcur) (D₀ := D)
    (Ktarget := 1) (Kboot := 2) hcore hcorei (by norm_num)
    (half_pos hbK) (by linarith only [sigma_pos]) (by norm_num) (by norm_num)
    hδgeom hδgc (min_le_right _ _) (min_le_left _ _) hδgeom16 hδgeomgap hmargin
  have hξgap := hgap (3 * Ctw * torusRow) (by positivity)
  refine ⟨b, hb, hbquarter, hnonzero, s, hs, A₀, hA, D, hD, δhit, hδhit, hδhitMax,
    Cerror, hCerror, ?_⟩
  filter_upwards [hξbudget, hξstage, hξgap] with ξ hbudget hstageξ hgapξ
  try dsimp only at hstageξ
  let ρ := Real.exp (-ξ)
  have hρ : 0 < ρ := Real.exp_pos (-ξ)
  have hbudget' : p.Budget ξ := hbudget
  have hβ : 0 ≤ 3 * (Ctw * torusRow * ρ ^ 8) +
      weightedInteractionRowFeedback b Cu Cl 2 ρ := by
    have hfb := weightedInteractionRowFeedback_nonneg (NNReal.coe_nonneg b) hCu hCl
      (by norm_num : (1 : ℝ) < 2) hgapξ.1
    positivity
  have hrate := hgapξ.2 ρ hρ.le le_rfl
  have hrateEq : weightedNormPropagationExponent Kself br Cu Cl 2 (3 * Ctw * torusRow) ρ ρ =
      ((b * Kself : ℝ≥0) : ℝ) +
        (3 * (Ctw * torusRow * ρ ^ 8) + weightedInteractionRowFeedback b Cu Cl 2 ρ) := by
    simp only [weightedNormPropagationExponent, NNReal.coe_mul]
    change br * (Kself : ℝ) + (3 * Ctw * torusRow) * ρ ^ 8 +
      weightedInteractionRowFeedback br Cu Cl 2 ρ = br * (Kself : ℝ) +
        (3 * (Ctw * torusRow * ρ ^ 8) + weightedInteractionRowFeedback br Cu Cl 2 ρ)
    ring
  rw [hrateEq] at hrate
  have hrateLo : (b : ℝ) * Kself / 2 ≤ ((b * Kself : ℝ≥0) : ℝ) +
      (3 * (Ctw * torusRow * ρ ^ 8) + weightedInteractionRowFeedback b Cu Cl 2 ρ) := by
    change br * Kself / 2 ≤ _
    linarith only [hrate.1, hbK]
  change ρ ≤ 1 / 2 ∧ ρ ^ 2 < (b : ℝ) ^ q ∧ _
  refine ⟨hbudget'.half, hbudget'.lp_ratio, ?_⟩
  intro N
  refine ⟨htime N, ?_⟩
  have hEuler := P.exists_finiteBase_fourfoldEuler_with_planar_area
    (s := s) (A₀ := A₀) (b := (b : ℝ)) (R := ρ) (ρ := ρ) (q := q) (T := T)
    hs hρ hbudget'.half hρ hbudget'.one hq hqE hT.le N
  obtain ⟨S, hS, hweak, hareaS⟩ := hEuler
  have hwsmall : ‖(v₀ - α₀) - (gseq α₀ 0 - α₀)‖ ≤ ‖α₀‖ / 32 := by
    rw [hw, norm_zero]
    exact div_nonneg (norm_nonneg _) (by norm_num)
  have haHalf : (1 / 16 : ℝ) / 2 = 1 / 32 := by norm_num
  have haFourth : (1 / 16 : ℝ) / 4 = 1 / 64 := by norm_num
  have hseedLow : ‖α₀‖ * ρ ^ 6 ≤ ‖α₀‖ :=
    mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ hρ.le hbudget'.one)
  have hwScale : ‖(v₀ - α₀) - (gseq α₀ 0 - α₀)‖ ≤ (0 : ℝ) * ρ ^ 6 := by
    rw [hw, norm_zero, zero_mul]
  have hActual := hstageξ (s := s) (A₀ := A₀) (R := ρ) (q := q) (T := T)
    (Hglob := T) (a := 1 / 16) (d := d) (Δ := 1) (Damp := Damp) (cs := ‖α₀‖) (W0 := 0)
    hs hA hρ hq hqE Ncap hNcap
    hbudget'.half hbudget'.one hbudget'.bhalf hbudget'.sq_bhalf hbudget'.initial_sep
    hbudget'.initial_core hbudget'.upper_sep hbudget'.lower_sep hbudget'.weight
    hbudget'.weighted_bootstrap hbudget'.row hβ hrateLo hrate.2 hbudget'.torus
    hT le_rfl hbudget'.drift hbudget'.radius hbudget'.radius (by norm_num) le_rfl hdpos
    hbudget'.initial_chart (by simpa only [haHalf] using hbudget'.geometry)
    (by simpa only [haFourth] using hbudget'.domain) hbudget'.logarithmic
    hgeom (by norm_num) hbudget'.outer_source hbudget'.radial hbudget'.particle_core
    hbudget'.particle_outer hbudget'.particle_box hbudget'.particle_sep hbudget'.kappa
    hDcap hDlam hDgeom N (htime N) hbudget'.capture hbudget'.forcing S hS
    hα hterminal hwsmall
    hbudget'.source hα (by norm_num) hseedLow hwScale δhit hαδ hcross.le
  obtain ⟨X, hX, hsamplesX, henvelope, hweighted, hgraph, hcohit, hhit⟩ := hActual
  have hclock : Real.exp (sigma * D) = lam ^ Ncap := by
    rw [show lam = Real.exp (sigma * Tblock) from circularCaptureBlockMultiplier_eq_exp ℓ,
      ← Real.exp_nat_mul]
    congr 1
    dsimp only [D]
    ring
  have hnear (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) D) :
      ‖canonicalPrefixAlignedCurrentCell A₀ b ρ ρ N 0 X τ - littleCircularMaterialContours hγ hγ1 τ‖ ≤ εgeom / 2 := by
    rw [norm_canonicalPrefixAlignedCurrentCell_sub_reference hγ hγ1 A₀ b ρ ρ N 0 τ X]
    have he : H * ‖α₀‖ * Real.exp (sigma * τ) ≤ H * ‖α₀‖ * Real.exp (sigma * D) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hτ.2 sigma_pos.le))
        (mul_nonneg hH.le (norm_nonneg _))
    have hm : H * ‖α₀‖ * Real.exp (sigma * D) ≤ H * Damp := by
      rw [hclock]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hterminal hH.le
    exact (henvelope τ hτ).trans (he.trans (hm.trans hDampGeom))
  have hgraphBound (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) D) :
      let vc := circularConstraintProjectionToTangentCLM hγ hγ1.le
        (circularCoRotationCLM γ τ (canonicalPrefixAlignedCurrentCell A₀ b ρ ρ N 0 X τ) -
          littleCircularReference hγ hγ1)
      ‖vc - gseq (circularConstrainedUnstableProjectionCLM hγ hγ1.le vc) 0‖ ≤ Cerror * ρ ^ 3 := by
    have hraw := hgraph τ hτ
    have hρ8 : ρ ^ 8 ≤ ρ ^ 3 := pow_le_pow_of_le_one hρ.le hbudget'.one (by decide)
    have hρ6 : ρ ^ 6 ≤ ρ ^ 3 := pow_le_pow_of_le_one hρ.le hbudget'.one (by decide)
    have hm2 := mul_le_mul_of_nonneg_left hρ8 hK2
    have hm3 := mul_le_mul_of_nonneg_left hρ6 hK3
    have hm4 := mul_le_mul_of_nonneg_left hρ8 hK4
    have hbound : Eg *
        (((0 : ℝ) + Fbar * Bpoly) * (Damp / ‖α₀‖ + 1) * ρ ^ 3 +
          3 * (E * (Ktor * ρ ^ 8)) * Damp / (lam - qbar) +
          Bpoly * ρ ^ 6 * (1 + D) ^ 4 + (Ktor * ρ ^ 8) * Rg) ≤ Cerror * ρ ^ 3 := by
      calc
        _ = Eg * (K1 * ρ ^ 3 + K2 * ρ ^ 8 + K3 * ρ ^ 6 + K4 * ρ ^ 8) := by
          dsimp only [K1, K2, K3, K4]
          ring
        _ ≤ Eg * ((K1 + K2 + K3 + K4) * ρ ^ 3) :=
          mul_le_mul_of_nonneg_left (by nlinarith only [hm2, hm3, hm4]) hEg.le
        _ ≤ Cerror * ρ ^ 3 := by
          have hh : Eg * (K1 + K2 + K3 + K4) ≤ Cerror := by dsimp only [Cerror]; linarith
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hh (pow_nonneg hρ.le 3)
    exact hraw.trans hbound
  exact ⟨S, hS, hweak, hareaS, X, hX, hweighted, hnear, hgraphBound, hcohit, hhit⟩

end CircularMaterialTransferProfile
end Euler2D

end
