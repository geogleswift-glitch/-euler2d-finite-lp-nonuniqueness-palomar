module

public import RequestProject.Euler.CircularActualCoupledParentCapture
public import RequestProject.Euler.CircularSelectedCanonicalCaptureTarget

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

def HasActualParentMatchedCaptureExtension
    (gseq : CircularConstrainedTangentSpace γ → ℕ → CircularConstrainedTangentSpace γ)
    {s A₀ b R ρ T : ℝ} (hR : 0 < R) (hρ : 0 < ρ)
    {N k : ℕ} (hkN : k ≤ N) {f : Lp ℝ 2 μT}
    (S : BoundedEulerParticleSystem f T) (entrance : ℝ)
    (Ypast : ℝ → FiniteCircularIndex k → LittleContourSpace γ)
    (ℓ : ℕ) (δ ηcur Hcap Cb D₀ Cgraph ξ sCanon Ctarget : ℝ) : Prop :=
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
        ∃ angle : ℝ,
        ‖circularCoRotationCLM γ u (y u) - contourRotationFamilyLittleCLM γ angle
          (circularCoRotationCLM γ sCanon (P.ancient sCanon))‖ ≤ Ctarget * Cgraph * ρ ^ 3 ∧
        ‖circularConstrainedUnstableProjectionCLM hγ hγ1.le
          (circularConstraintProjectionToTangentCLM hγ hγ1.le
            (circularCoRotationCLM γ u (y u) - littleCircularReference hγ hγ1))‖ = δ ∧
        ∀ t ∈ Ico (0 : ℝ) u,
          ‖circularConstrainedUnstableProjectionCLM hγ hγ1.le
            (circularConstraintProjectionToTangentCLM hγ hγ1.le
              (circularCoRotationCLM γ t (y t) - littleCircularReference hγ hγ1))‖ < δ

lemma parentCapture_envelope_bound_relative_section {ℓ Ncap : ℕ} {a Hcap δ u : ℝ}
    (ha : 0 ≤ a) (hHcap : 0 ≤ Hcap)
    (hterminal : a * circularCaptureBlockMultiplier ℓ ^ Ncap <
      (4 * circularCaptureBlockMultiplier ℓ / 3) * δ)
    (hu : u ≤ (Ncap : ℝ) * circularCaptureBlockTime ℓ) :
    Hcap * a * Real.exp (sigma * u) ≤
      (Hcap * (4 * circularCaptureBlockMultiplier ℓ / 3)) * δ := by
  have hexp : Real.exp (sigma * ((Ncap : ℝ) * circularCaptureBlockTime ℓ)) =
      circularCaptureBlockMultiplier ℓ ^ Ncap := by
    rw [circularCaptureBlockMultiplier_eq_exp, ← Real.exp_nat_mul]
    congr 1
    ring
  have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hu sigma_pos.le)
  rw [hexp] at he
  calc
    _ ≤ Hcap * a * circularCaptureBlockMultiplier ℓ ^ Ncap :=
      mul_le_mul_of_nonneg_left he (mul_nonneg hHcap ha)
    _ = Hcap * (a * circularCaptureBlockMultiplier ℓ ^ Ncap) := by ring
    _ ≤ Hcap * ((4 * circularCaptureBlockMultiplier ℓ / 3) * δ) :=
      mul_le_mul_of_nonneg_left hterminal.le hHcap
    _ = _ := by ring

theorem eventually_actualCoupled_parentCapture_matches_selected_target
    {b : ℝ≥0} {s cA q T δ sCanon εtarget Ctarget η Hcap : ℝ} {ℓ : ℕ}
    [Fact (1 ≤ ENNReal.ofReal q)]
    (hs : s ≤ 0) (hb : 0 < b) (hcA : 0 < cA) (hT : 0 < T)
    (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q) (hℓ : 0 < ℓ)
    (hδ : 0 < δ) (hη : 0 < η) (hηa : η ≤ cellA / 4) (hHcap : 0 < Hcap)
    {gseq : CircularConstrainedTangentSpace γ → ℕ → CircularConstrainedTangentSpace γ}
    (htarget : P.IsSelectedCanonicalCaptureTarget gseq δ sCanon εtarget Ctarget)
    (hTargetRadius : (Hcap * (4 * circularCaptureBlockMultiplier ℓ / 3)) * δ < εtarget)
    (hancient : ∀ i, ‖(P.ancient s i).val - circularReferenceC1 hγ hγ1 i‖ ≤ η) :
    ∀ᶠ ξ : ℝ in atTop,
      let ρ := Real.exp (-ξ)
      let hρ := Real.exp_pos (-ξ)
      let R := ρ ^ 10
      let hR := pow_pos hρ 10
      let A₀ := cA * (1 + ξ)
      ∀ N k : ℕ, ∀ hkN : k ≤ N,
      ∀ S : BoundedEulerParticleSystem
        (finiteBaseCurlL2 (A₀ := A₀) (b := (b : ℝ)) (ρ := ρ) hR hρ hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := (b : ℝ)) (ρ := ρ) (q := q) hs hR hρ) N) T,
      IsFourfoldBoundedEulerParticleSystem S →
      ∀ entrance : ℝ, 0 ≤ entrance →
      ∀ Ypast : ℝ → FiniteCircularIndex k → LittleContourSpace γ,
      ∀ Cb D₀ Cgraph : ℝ,
      P.HasActualParentCaptureExtension gseq (s := s) (A₀ := A₀) (b := (b : ℝ))
        hR hρ hkN S entrance Ypast ℓ δ η Hcap Cb D₀ Cgraph ξ →
      P.HasActualParentMatchedCaptureExtension gseq (s := s) (A₀ := A₀) (b := (b : ℝ))
        hR hρ hkN S entrance Ypast ℓ δ η Hcap Cb D₀ Cgraph ξ sCanon Ctarget := by
  obtain ⟨Cgeo, hCgeo, hmatch⟩ :=
    P.exists_uniform_actualCanonical_capture_matches_selected_target
  let targetFactor := Hcap * (4 * circularCaptureBlockMultiplier ℓ / 3)
  have hFactor : 0 < targetFactor := by
    dsimp only [targetFactor]
    rw [circularCaptureBlockMultiplier_eq_exp]
    positivity
  let δgeom := min η (targetFactor * δ)
  have hδgeom : 0 < δgeom := lt_min hη (mul_pos hFactor hδ)
  have hδgeomA : δgeom ≤ cellA / 4 := (min_le_left _ _).trans hηa
  have hδgeomE : δgeom < εtarget := (min_le_right _ _).trans_lt hTargetRadius
  have hbR : 0 < (b : ℝ) := hb
  let dcoef := 4 * Cgeo * cA * T
  let dsupport := fun ξ : ℝ => 2 + dcoef * (1 + ξ)
  have hρlim : Tendsto (fun ξ : ℝ => Real.exp (-ξ)) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero
  have hhalf : ∀ᶠ ξ : ℝ in atTop, Real.exp (-ξ) ≤ (b : ℝ) / 2 :=
    (hρlim.eventually (gt_mem_nhds (half_pos hbR))).mono (fun _ h => h.le)
  have hmax : ∀ᶠ ξ : ℝ in atTop, Real.exp (-ξ) ≤ 1 / 2 :=
    (hρlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).mono (fun _ h => h.le)
  have hdlim : Tendsto (fun ξ : ℝ => dsupport ξ * Real.exp (-ξ) ^ 10) atTop (𝓝 0) := by
    convert tendsto_circularCapture_log_monomial 1 dcoef (1 + dcoef) 10 1 (by decide) using 1
    ext ξ
    dsimp only [dsupport]
    ring
  have hdriftScale : ∀ᶠ ξ : ℝ in atTop, dsupport ξ * Real.exp (-ξ) ^ 10 ≤ 1 / 4 :=
    (hdlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))).mono (fun _ h => h.le)
  have hhlim : Tendsto (fun ξ : ℝ => 2 * Real.exp (-ξ) ^ 6) atTop (𝓝 0) := by
    simpa only [zero_pow (by decide : 6 ≠ 0), mul_zero] using (hρlim.pow 6).const_mul 2
  have hweight : ∀ᶠ ξ : ℝ in atTop, 2 * Real.exp (-ξ) ^ 6 ≤ δgeom :=
    (hhlim.eventually (gt_mem_nhds hδgeom)).mono (fun _ h => h.le)
  filter_upwards [hhalf, hmax, hdriftScale, hweight, eventually_ge_atTop (0 : ℝ)]
    with ξ hρhalf hρmax hdR hhK hξ
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
  have hh1 : 2 * ρ ^ 6 ≤ 1 := hhK.trans (hδgeomA.trans (by linarith only [cellA_lt_one]))
  have hcorei (i : Fin 2) : cellA / 2 ≤ 3 * circularContourRadii i / 4 := by
    have hi := (circularContourRadii_bounds i).2.1
    linarith only [hi, cellA_pos]
  dsimp only
  intro N k hkN S hS entrance he Ypast Cb D₀ Cgraph hcap
  try dsimp only [HasActualParentCaptureExtension] at hcap
  obtain ⟨Ncap, hNcap, hDlog, hterminal, hphysical, X, hX, heq,
    hgrid, henv, hcur, hback, hweighted, hparticles, hgraph, hfirst, _hhit⟩ := hcap
  let Dcap := (Ncap : ℝ) * circularCaptureBlockTime ℓ
  have hDcap : 0 ≤ Dcap := mul_nonneg (Nat.cast_nonneg Ncap) (circularCaptureBlockTime_pos hℓ).le
  have hAk : 0 < ampScale A₀ b k := by unfold ampScale; positivity
  have hEnd : 0 ≤ entrance + Dcap / ampScale A₀ b k := add_nonneg he (div_nonneg hDcap hAk.le)
  have hEndT : entrance + Dcap / ampScale A₀ b k ≤ T :=
    hphysical.le.trans (half_le_self hT.le)
  let α₀ := circularConstrainedUnstableProjectionCLM hγ hγ1.le
    (circularConstraintProjectionToTangentCLM hγ hγ1.le
      (canonicalPrefixAlignedCurrentCell A₀ b R ρ k entrance Ypast 0 - littleCircularReference hγ hγ1))
  have hcurRelative (u : ℝ) (hu : u ∈ Icc (0 : ℝ) Dcap) :
      ‖canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance X u k‖ ≤ targetFactor * δ :=
    (henv u hu).trans (parentCapture_envelope_bound_relative_section
      (norm_nonneg α₀) hHcap.le hterminal hu.2)
  have hcurGeom (u : ℝ) (hu : u ∈ Icc (0 : ℝ) Dcap) :
      ‖canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance X u k‖ ≤ δgeom :=
    le_min (hcur u hu) (hcurRelative u hu)
  obtain ⟨u, hu, htime, angle, hmatched, hvalue, hbefore⟩ :=
    hmatch gseq δ sCanon εtarget Ctarget htarget
      (s := s) (A₀ := A₀) (b := (b : ℝ)) (R := R) (ρ := ρ) (q := q) (T := T)
      (Hglob := T) (a := 1 / 16) (dglob := d)
      (Dphys := entrance + Dcap / ampScale A₀ b k) (entrance := entrance) (Dcap := Dcap)
      (core := cellA / 2) (δgeom := δgeom) (η := η) (C₀ := 2) (K := 1)
      (error := Cgraph * ρ ^ 3)
      hs hA hbR hR hRmax hρ hρone hρb hq hqE le_rfl hdrift hdR hEnd he hDcap
      hδgeomA hδgeomE hcorei (by norm_num) hh1 (by norm_num)
      (by simpa only [mul_one] using hhK) hη.le hηa hancient hkN le_rfl S hS X hX
      hweighted hcurGeom hfirst hgraph
  refine ⟨Ncap, hNcap, hDlog, hterminal, hphysical, X, hX, heq,
    hgrid, henv, hcur, hback, hweighted, hparticles, hgraph, hfirst,
    u, hu, htime, angle, ?_, hvalue, hbefore⟩
  simpa only [mul_assoc] using hmatched

end CircularMaterialTransferProfile
end Euler2D

end
