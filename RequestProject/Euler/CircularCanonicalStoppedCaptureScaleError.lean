module

public import RequestProject.Euler.CircularCanonicalAlignedCurrentDynamics
public import RequestProject.Euler.CircularCanonicalInnerParticles
public import RequestProject.Euler.CircularStoppedCaptureScaleError

/-! Stopped capture on one actual finite Euler trajectory. Both the
inner particle fence and the forcing used in capture are consequences
of its weighted/current history. -/

@[expose] public section

set_option maxHeartbeats 32000000
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

theorem exists_uniform_actualCanonical_stopped_capture_scale_error {b Cw Rflow r₀ : ℝ}
    (hb : 0 < b) (hb1 : b < 1) (hCw : 0 ≤ Cw) (hRflow : 0 < Rflow) (hr₀ : 0 < r₀)
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
    ∃ Cgeo Ct Cd Cr Kr : ℝ, 0 < Cgeo ∧ 0 < Ct ∧ 0 < Cd ∧ 0 < Cr ∧ 0 < Kr ∧
    ∃ ℓ : ℕ, 0 < ℓ ∧ ∃ qc : ℝ, 1 < qc ∧ qc ^ 2 < circularCaptureBlockMultiplier ℓ ∧
      let Tblock := circularCaptureBlockTime ℓ
      let lam := circularCaptureBlockMultiplier ℓ
      let Pu := circularConstrainedUnstableProjectionCLM hγ hγ1.le
      let g := fun v => gseq v 0 - v
      let Cb := radialStageRadiusConstant Cr Cw b
      ∃ C > 0, ∃ dcap > 0, dcap ≤ r₀ / 2 ∧ ∃ E > 0, ∃ F > 0, ∃ r > 0,
      ∃ κ₀ > 0, ∃ ε₀ > 0, ∃ H > 0, ∃ Eg > 0, ∃ Rg > 0,
      ∀ qbar : ℝ, 1 < qbar → qbar ^ 2 < lam → ∃ Fbar > 0,
      ∀ {s A₀ R ρ q T Hglob a c d δ Dphys entrance Dcap η C₀ K Δ Damp cs W0 : ℝ},
      ∀ [Fact (1 ≤ ENNReal.ofReal q)] (hs : s ≤ 0) (hA : 0 < A₀)
        (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
        (hρhalf : ρ ≤ b / 2) (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q),
      let κ := Ct * finiteTorusLabelLittleRowCoefficient (γ : ℝ) L * R ^ 8
      let Bpoly := finiteCurrentPolynomialForcingCoefficient (γ : ℝ) (cellA / 2) L Cb b Cd + Δ
      Hglob ≤ T → 5 / 4 + (Cgeo * A₀ / (1 - ρ / b)) * Hglob < d → d * R ≤ 1 / 16 →
      0 < a → a ≤ 1 / 16 → 0 < c → 0 < d → 0 ≤ Dphys → 0 ≤ entrance → 0 ≤ Dcap →
      ρ ^ 2 ≤ b / 2 → (5 / 4 : ℝ) * ρ ≤ cellA →
      δ ≤ cellA / 4 → δ ≤ r → (∀ i, c ≤ 3 * circularContourRadii i / 4) →
      0 ≤ η → η ≤ cellA / 4 → (∀ i, ‖(P.ancient s i).val - circularReferenceC1 hγ hγ1 i‖ ≤ η) →
      1 ≤ C₀ → 0 ≤ K → 0 ≤ Δ → C₀ * ρ ^ 6 ≤ 1 → C₀ * ρ ^ 6 * K ≤ δ → C₀ * ρ ^ 8 ≤ 1 / 2 →
      8 * L * ρ ≤ c → (5 / 4 : ℝ) * R ≤ a →
      (2 * b * C₀ * K * (finiteOuterLabelLittleRowCoefficient (γ : ℝ) c L L +
        Ct * finiteTorusLabelLittleRowCoefficient (γ : ℝ) L)) * ρ ^ 2 ≤ Δ →
      b * finiteEulerUniformRadialCoefficient Kr b R ρ c d δ * Cb ^ 3 *
        ρ ^ 2 * (1 + Dcap) ^ 3 ≤ Cr / 2 →
      Cb * ρ * (1 + Dcap) ≤ c / 2 → Cb * ρ * (1 + Dcap) ≤ d →
      κ ≤ κ₀ → 3 * Damp ≤ dcap → qc + 3 * C * Damp ≤ qbar →
      ∀ (N k Ncap : ℕ) (hkN : k ≤ N),
      0 < Ncap → Dcap ≤ (Ncap : ℝ) * Tblock →
      entrance + Dcap / ampScale A₀ b k ≤ Dphys →
      (L + 1) * radScale R ρ k ≤ a / 2 →
      Cb * ρ * radScale R ρ k * (1 + Dcap) ≤ a → 8 * (Cb * ρ * (1 + Dcap)) ≤ cellA / 2 →
      9 * C * Damp / (lam - 1) + 3 * (E * κ) * (Ncap : ℝ) ≤ 1 / 16 →
      Bpoly * ρ ^ 6 * (1 + (Ncap : ℝ) * Tblock) ^ 4 + κ * (3 * Damp) ≤ ε₀ →
      ∀ S : BoundedEulerParticleSystem
        (finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N) T,
      IsFourfoldBoundedEulerParticleSystem S →
      ∀ X : ℝ → FiniteCircularIndex k → LittleContourSpace γ,
      IsBanachTimeDomainTrajectoryOn
        (S.actualPartialPhaseField (P.finiteInnerInitialLabel s A₀ b R ρ N k) hγ hγ1
          (finiteCircularReferenceC1 hγ hγ1 R ρ) (finiteCircularInterfaceRadius R ρ)
          (finiteCircularInterfaceRadius_pos hR hρ) (lift_finiteCircularReferenceC1 hγ hγ1 R ρ)
          (finiteCircularInterfaceStrength A₀ b))
        (S.actualPartialPhaseDomain (P.finiteInnerInitialLabel s A₀ b R ρ N k)
          (finiteCircularReferenceC1 hγ hγ1 R ρ) (finiteCircularInterfaceRadius R ρ) a Hglob)
        (fun p => finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N (finiteCircularPrefixIndex hkN p)) Dphys X →
      let x := canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance X
      let y := canonicalPrefixAlignedCurrentCell A₀ b R ρ k entrance X
      let v := fun n : ℕ => circularConstraintProjectionToTangentCLM hγ hγ1.le
        (y ((n : ℝ) * Tblock) - littleCircularReference hγ hγ1)
      let α := fun n => Pu (v n)
      let w := fun n => (v n - α n) - g (α n)
      (∀ τ ∈ Icc (0 : ℝ) Dcap, weightedFamilyNorm (C₀ * ρ ^ 6) k (x τ) ≤ K) →
      (∀ τ ∈ Icc (0 : ℝ) Dcap, ‖x τ k‖ ≤ δ) →
      (∀ z ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N k,
        ‖S.forward entrance z - torusCenter‖ ≤ Cw * ρ * radScale R ρ k) →
      0 < ‖α 0‖ → ‖α 0‖ * lam ^ Ncap ≤ Damp →
      ‖w 0‖ ≤ ‖α 0‖ / 32 → F * Bpoly * ρ ^ 6 ≤ ‖α 0‖ / 32 →
      0 < cs → 0 ≤ W0 → cs * ρ ^ 6 ≤ ‖α 0‖ → ‖w 0‖ ≤ W0 * ρ ^ 6 →
      (∀ n ≤ Ncap, (n : ℝ) * Tblock ≤ Dcap →
        (3 / 4 : ℝ) * ‖α 0‖ * lam ^ n ≤ ‖α n‖ ∧
        ‖α n‖ ≤ (5 / 4 : ℝ) * ‖α 0‖ * lam ^ n ∧
        ‖w n‖ ≤ (1 / 8 : ℝ) * ‖α 0‖ * lam ^ n) ∧
      (∀ τ ∈ Icc (0 : ℝ) Dcap, ‖x τ k‖ ≤ H * ‖α 0‖ * Real.exp (sigma * τ)) ∧
      (∀ τ ∈ Icc (0 : ℝ) Dcap, ∀ z ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N k,
        ‖S.forward (physicalTimeFromNormalized (ampScale A₀ b k) entrance τ) z - torusCenter‖ ≤
          Cb * ρ * radScale R ρ k * (1 + τ)) ∧
      ∀ τ ∈ Icc (0 : ℝ) Dcap,
        let vc := circularConstraintProjectionToTangentCLM hγ hγ1.le
          (circularCoRotationCLM γ τ (y τ) - littleCircularReference hγ hγ1)
        ‖vc - gseq (Pu vc) 0‖ ≤ Eg *
          ((W0 + Fbar * Bpoly) * (Damp / cs + 1) * ρ ^ 3 +
            3 * (E * κ) * Damp / (lam - qbar) +
            Bpoly * ρ ^ 6 * (1 + (Ncap : ℝ) * Tblock) ^ 4 + κ * Rg) := by
  obtain ⟨Cp, Cr, Kr, hCp, hCr, hKr, hparticles⟩ :=
    P.exists_uniform_actualCanonical_inner_particle_confinement hb hb1 hCw
  obtain ⟨Cdyn, Ct, Cd, εchart, hCdyn, hCt, hCd, hεchart, hdynamics⟩ :=
    P.exists_uniform_actualCanonical_alignedCurrent_dynamics
  obtain ⟨ℓ, hℓ, qc, hqc, hqgap, C, hC, dcap, hdcap, hdr, E, hE, F, hF,
    r, hr, κ₀, hκ₀, ε₀, hε₀, H, hH, Eg, hEg, Rg, hRg, hcaptureFamily⟩ :=
    exists_circular_stopped_capture_scale_error_constants hγ hγ1 hRflow hr₀ hεchart hY hd hfix harea hg
  let Cgeo := max Cp Cdyn
  refine ⟨Cgeo, Ct, Cd, Cr, Kr, hCp.trans_le (le_max_left _ _), hCt, hCd, hCr, hKr,
    ℓ, hℓ, qc, hqc, hqgap, C, hC, dcap, hdcap, hdr, E, hE, F, hF, r, hr, κ₀, hκ₀, ε₀, hε₀, H, hH,
    Eg, hEg, Rg, hRg, ?_⟩
  intro qbar hqbar hqbarGap
  obtain ⟨Fbar, hFbar, hcapture⟩ := hcaptureFamily qbar hqbar hqbarGap
  refine ⟨Fbar, hFbar, ?_⟩
  intro s A₀ R ρ q T Hglob a c d δ Dphys entrance Dcap η C₀ K Δ Damp cs W0 _
    hs hA hR hRmax hρ hρ1 hρhalf hq hqE
  let L := circularCanonicalCellNormBudget hγ hγ1
  let Cb := radialStageRadiusConstant Cr Cw b
  let κ := Ct * finiteTorusLabelLittleRowCoefficient (γ : ℝ) L * R ^ 8
  let Bpoly := finiteCurrentPolynomialForcingCoefficient (γ : ℝ) (cellA / 2) L Cb b Cd + Δ
  try dsimp only
  intro hglobT hdrift hdR ha ha16 hc hdpos hDphys he hDcap hhalf hρcore hδ hδr hcore
    hη hηa hancient hC₀ hK hΔ hh1 hhK hζ hsepL hRchart hsmall hcubic hinnerCore hinnerChart
    hκcap hDamp hcomp N k Ncap hkN hNcap hcapDuration htimeEnd hgeom hchartCap hsepCap
    hsmallCap hpolyCap S hS X hX
  let x := canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance X
  let y := canonicalPrefixAlignedCurrentCell A₀ b R ρ k entrance X
  intro hZ hcur hstart ha₀ hterminal hw₀ hweighted hcs hW0 hseedLow hwScale
  have hρb : ρ < b := hρhalf.trans_lt (by linarith only [hb])
  have hden : 0 < 1 - ρ / b := sub_pos.mpr ((div_lt_one hb).mpr hρb)
  have hHglob : 0 ≤ Hglob := (hX.mem 0 ⟨le_rfl, hDphys⟩).1.2
  have hdriftFor (C₁ : ℝ) (hC₁ : C₁ ≤ Cgeo) :
      5 / 4 + (C₁ * A₀ / (1 - ρ / b)) * Hglob < d :=
    (add_le_add le_rfl (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hC₁ hA.le) hden.le) hHglob)).trans_lt hdrift
  have hCb : 0 < Cb := radialStageRadiusConstant_pos hCr hCw hb hb1
  have hpactual := hparticles hs hA hR hRmax hρ hρ1 hρhalf hq hqE
    hglobT (hdriftFor Cp (le_max_left _ _)) hdR hc hdpos hDphys he hDcap hhalf hδ hcore
    hC₀ hK hh1 hhK hcubic hinnerCore hinnerChart N k hkN htimeEnd S hS X hX hZ hcur hstart
  obtain ⟨p, hp⟩ := hdynamics hs hA hb hb1.le hR hRmax hρ hρ1 hρb hq hqE
    hglobT (hdriftFor Cdyn (le_max_right _ _)) (hdR.trans (by norm_num)) hDphys he hDcap
    (le_refl (0 : ℝ)) hhalf hρcore ha ha16 hc hcore hδ hη hηa hancient hCb.le hC₀ hK hΔ
    hh1 hhK hζ hsepL hRchart hsmall N k hkN htimeEnd hgeom
    (by simpa only [add_zero, zero_add] using hchartCap)
    (by simpa only [add_zero, zero_add] using hsepCap) S hS X hX hZ hcur
    (by simpa only [add_zero, zero_add] using hpactual)
  have hL : 0 < L := circularCanonicalCellNormBudget_pos hγ hγ1
  have hκ : 0 ≤ κ := mul_nonneg (mul_nonneg hCt.le
    (finiteTorusLabelLittleRowCoefficient_nonneg hL.le)) (by positivity)
  have hcauchy : 0 ≤ cauchyContourNormBudget 5 (γ : ℝ) 1 (cellA / 2) L :=
    (cauchySpatialDerivativeBudget_nonneg 5 (by norm_num : (0 : ℝ) ≤ 1)
      (half_pos cellA_pos) 0).trans (le_max_left _ _)
  have htor : 0 ≤ torusCorrectionContourBudget (γ : ℝ) L := by
    unfold torusCorrectionContourBudget
    positivity
  have hBpoly : 0 ≤ Bpoly := by
    unfold Bpoly finiteCurrentPolynomialForcingCoefficient
    positivity [finiteLabelMassBound_nonneg]
  have hnorm (τ : ℝ) : ‖y τ - littleCircularMaterialContours hγ hγ1 τ‖ = ‖x τ k‖ :=
    norm_canonicalPrefixAlignedCurrentCell_sub_reference hγ hγ1 A₀ b R ρ k entrance τ X
  have hcap := hcapture y p Ncap (κ := κ) (Damp := Damp) (D := Dcap) (Bpoly := Bpoly)
    (ρ := ρ) (offset := 0) (c := cs) (W0 := W0)
    hNcap ⟨hDcap, hcapDuration⟩ hcomp hκ hκcap hDamp hBpoly le_rfl hρ.le hcs hW0 hseedLow
    ha₀ hterminal hsmallCap hw₀ hwScale
    (by simpa only [add_zero, zero_add, one_pow, mul_one] using hweighted)
    (by simpa only [add_zero, zero_add] using hpolyCap)
    (fun τ hτ => (hp τ hτ).2.2.2)
    (fun τ hτ => (hp τ hτ).1)
    (fun τ hτ => by rw [hnorm]; exact (hcur τ hτ).trans hδr)
    (by intro τ hτ; simpa only [add_zero, zero_add] using (hp τ hτ).2.1)
  refine ⟨hcap.1, (fun τ hτ => by rw [← hnorm]; exact hcap.2.1 τ hτ), hpactual, ?_⟩
  intro τ hτ
  simpa only [add_zero, zero_add, one_pow, mul_one] using hcap.2.2 τ hτ

end CircularMaterialTransferProfile
end Euler2D

end
