module

public import RequestProject.Euler.CircularCoupledDeepestEarlierEntry

public import RequestProject.Euler.CircularDeepestEarlierEntry
public import RequestProject.Euler.CircularCaptureCoupledScaleSmallness

/-! The actual earlier section matches the SAME canonical ancient arc
with R=rho^10 and A0=cA*(1+xi). Its normalized matching constant is
chosen before cA, the physical initial sample, q and the time horizon. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 32000000
set_option maxRecDepth 8500

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

theorem exists_eventually_actualCoupledForced_earlier_section_match
    {sCanon η Cmatch Lback : ℝ}
    (hsCanon : sCanon ≤ 0) (hη : 0 < η) (hηa : η ≤ cellA / 4)
    (hCmatch : 0 ≤ Cmatch) (hLback : 0 < Lback) :
    ∃ Cback > 0,
      ∀ b Cb Lclock Dclock : ℝ, 0 < b → b ≤ 1 → 0 ≤ Cb →
      ∀ {s cA q T : ℝ} [Fact (1 ≤ ENNReal.ofReal q)],
      ∀ (hs : s ≤ 0) (hcA : 0 < cA) (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q),
      0 ≤ T → (∀ i, ‖(P.ancient s i).val - circularReferenceC1 hγ hγ1 i‖ ≤ η) →
      ∀ᶠ ξ : ℝ in atTop,
      let ρ := Real.exp (-ξ)
      let hρ := Real.exp_pos (-ξ)
      let R := ρ ^ 10
      let hR := pow_pos hρ 10
      let A₀ := cA * (1 + ξ)
      ∀ N k : ℕ, ∀ hkN : k ≤ N,
      ∀ S : BoundedEulerParticleSystem
        (finiteBaseCurlL2 (A₀ := A₀) (b := b) (ρ := ρ) hR hρ hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := b) (ρ := ρ) (q := q) hs hR hρ) N) T,
      IsFourfoldBoundedEulerParticleSystem S →
      ∀ entrance Dcap : ℝ, 0 ≤ entrance → 0 ≤ Dcap → Dcap ≤ Lclock * ξ + Dclock →
      ∀ X : ℝ → FiniteCircularIndex k → LittleContourSpace γ,
      P.ActualCanonicalPrefixTrajectory s A₀ b R ρ (1 / 16) T hR hρ hkN S
        (entrance + Dcap / ampScale A₀ b k) X →
      (∀ u ∈ Icc (0 : ℝ) Dcap,
        weightedFamilyNorm (2 * ρ ^ 6) k
          (canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance X u) ≤ 1) →
      (∀ u ∈ Icc (0 : ℝ) Dcap,
        ‖canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance X u k‖ ≤ η) →
      (∀ u ∈ Icc (0 : ℝ) Dcap, ∀ z ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N k,
        ‖S.forward (physicalTimeFromNormalized (ampScale A₀ b k) entrance u) z - torusCenter‖ ≤
          Cb * ρ * radScale R ρ k * (1 + u)) →
      let y := canonicalPrefixAlignedCurrentCell A₀ b R ρ k entrance X
      ∀ exit angle : ℝ, exit ∈ Icc Lback Dcap →
      ‖circularCoRotationCLM γ exit (y exit) -
        contourRotationFamilyLittleCLM γ angle (circularCoRotationCLM γ sCanon (P.ancient sCanon))‖ ≤ Cmatch * ρ ^ 3 →
      ‖circularCoRotationCLM γ (exit - Lback) (y (exit - Lback)) -
        contourRotationFamilyLittleCLM γ angle
          (circularCoRotationCLM γ (sCanon - Lback) (P.ancient (sCanon - Lback)))‖ ≤ Cback * ρ ^ 3 := by
  obtain ⟨Cgeo, Ct, Cd, δmatch, εforce, hCgeo, hCt, hCd, hδmatch, hεforce, Klook, hlook⟩ :=
    P.exists_uniform_actualCanonical_capture_quantitative_lookback hsCanon hLback
  let L := circularCanonicalCellNormBudget hγ hγ1
  let core := cellA / 2
  let torusRow := finiteTorusLabelLittleRowCoefficient (γ : ℝ) L
  let Cl := finiteOuterLabelLittleRowCoefficient (γ : ℝ) core L L
  let Ktor := Ct * torusRow
  let Cback := (Cmatch + Lback) * Real.exp ((Klook : ℝ) * Lback) + 1
  have hL : 0 < L := circularCanonicalCellNormBudget_pos hγ hγ1
  have hcore : 0 < core := half_pos cellA_pos
  have htorusRow : 0 ≤ torusRow := finiteTorusLabelLittleRowCoefficient_nonneg hL.le
  have hKtor : 0 ≤ Ktor := mul_nonneg hCt.le htorusRow
  have hCback : 0 < Cback := by dsimp only [Cback]; positivity
  have hsmall (C : ℝ) (n : ℕ) (hn : n ≠ 0) (ε : ℝ) (hε : 0 < ε) :
      ∀ᶠ ξ : ℝ in atTop, C * Real.exp (-ξ) ^ n ≤ ε := by
    have ht : Tendsto (fun ξ : ℝ => C * Real.exp (-ξ) ^ n) atTop (𝓝 0) := by
      simpa only [zero_pow hn, mul_zero] using
        (Real.tendsto_exp_neg_atTop_nhds_zero.pow n).const_mul C
    exact (ht.eventually (gt_mem_nhds hε)).mono (fun _ h => h.le)
  refine ⟨Cback, hCback, ?_⟩
  intro b Cb Lclock Dclock hb hb1 hCb s cA q T _ hs hcA hq hqE hT hancient
  let Kpoly := finiteCurrentPolynomialForcingCoefficient (γ : ℝ) (cellA / 2) L Cb b Cd + 1
  have hcauchy : 0 ≤ cauchyContourNormBudget 5 (γ : ℝ) 1 (cellA / 2) L :=
    (cauchySpatialDerivativeBudget_nonneg 5 (by norm_num : (0 : ℝ) ≤ 1)
      (half_pos cellA_pos) 0).trans (le_max_left _ _)
  have htor : 0 ≤ torusCorrectionContourBudget (γ : ℝ) L := by
    unfold torusCorrectionContourBudget
    positivity
  have hKpoly : 0 ≤ Kpoly := by
    unfold Kpoly finiteCurrentPolynomialForcingCoefficient
    positivity [finiteLabelMassBound_nonneg]
  let packet := min (1 / 16 : ℝ) (cellA / 16)
  have hpacket : 0 < packet := lt_min (by norm_num) (div_pos cellA_pos (by norm_num))
  have hpacketEv := eventually_circularCapture_log_monomial_small
    (K := Cb) (L := Lclock) (D₀ := Dclock) hCb hpacket 1 1 (by decide)
  have hpolyEv := eventually_circularCapture_log_monomial_small
    (K := Kpoly) (L := Lclock) (D₀ := Dclock) hKpoly (by norm_num : (0 : ℝ) < 1 / 2) 3 4 (by decide)
  let dcoef := 4 * Cgeo * cA * T
  let dsupport := fun ξ : ℝ => 2 + dcoef * (1 + ξ)
  have hdRlim : Tendsto (fun ξ : ℝ => dsupport ξ * Real.exp (-ξ) ^ 10) atTop (𝓝 0) := by
    convert tendsto_circularCapture_log_monomial 1 dcoef (1 + dcoef) 10 1 (by decide) using 1
    ext ξ
    dsimp only [dsupport]
    ring
  have hsmallDR := (hdRlim.eventually (gt_mem_nhds
    (by norm_num : (0 : ℝ) < 1 / 4))).mono (fun _ h => h.le)
  filter_upwards [hsmall 1 1 (by decide) (1 / 2) (by norm_num),
    hsmall 1 1 (by decide) (b / 2) (half_pos hb),
    hsmall 1 2 (by decide) (b / 2) (half_pos hb),
    hsmall (5 / 4) 1 (by decide) cellA cellA_pos,
    hsmall (5 / 4) 1 (by decide) (1 / 16) (by norm_num),
    hsmall 2 6 (by decide) 1 (by norm_num), hsmall 2 6 (by decide) η hη,
    hsmall 2 8 (by decide) (1 / 2) (by norm_num),
    hsmall (8 * L) 1 (by decide) core hcore, hsmallDR,
    hsmall (L + 1) 1 (by decide) (1 / 32) (by norm_num),
    hsmall (2 * b * 2 * 1 * (Cl + Ct * torusRow)) 2 (by decide) 1 (by norm_num),
    hsmall (Ktor * η) 3 (by decide) (1 / 2) (by norm_num), hpolyEv, hpacketEv,
    hsmall 1 3 (by decide) εforce hεforce,
    hsmall Cmatch 3 (by decide) δmatch hδmatch, eventually_ge_atTop (0 : ℝ)]
    with ξ hρhalf hρbhalf hρsq hρcore hρchart hh1 hhη hζ hsep hdR hgeom houter
      htor3 hpoly3 hpacket3 hforceSmall hmatchSmall hξ
  simp only [pow_one, one_mul] at hρhalf hρbhalf hρsq hρcore hρchart hsep hdR hgeom hforceSmall
  let ρ := Real.exp (-ξ)
  have hρ : 0 < ρ := Real.exp_pos (-ξ)
  let R := ρ ^ 10
  let A₀ := cA * (1 + ξ)
  let d := 2 + 4 * Cgeo * A₀ * T
  have hR : 0 < R := pow_pos hρ 10
  have hA : 0 < A₀ := mul_pos hcA (by linarith only [hξ])
  have hcat : 0 ≤ Cgeo * A₀ * T := mul_nonneg (mul_nonneg hCgeo.le hA.le) hT
  have hdeq : dsupport ξ = d := by dsimp only [dsupport, dcoef, d, A₀]; ring
  rw [hdeq] at hdR
  have hρ1 : ρ ≤ 1 := hρhalf.trans (by norm_num)
  have hRρ : R ≤ ρ := by
    simpa only [R, pow_one] using pow_le_pow_of_le_one hρ.le hρ1 (by decide : (1 : ℕ) ≤ 10)
  have hRhalf : R ≤ 1 / 2 := hRρ.trans hρhalf
  have hRchart : (5 / 4 : ℝ) * R ≤ 1 / 16 :=
    (mul_le_mul_of_nonneg_left hRρ (by norm_num : (0 : ℝ) ≤ 5 / 4)).trans hρchart
  have hρb : ρ < b := hρbhalf.trans_lt (half_lt_self hb)
  have hdenHalf : (1 / 2 : ℝ) ≤ 1 - ρ / b := by
    have hh : ρ / b ≤ 1 / 2 := (div_le_iff₀ hb).mpr (by nlinarith only [hρbhalf])
    linarith only [hh]
  have hdiv : Cgeo * A₀ / (1 - ρ / b) ≤ 2 * Cgeo * A₀ := by
    calc
      _ ≤ Cgeo * A₀ / (1 / 2) :=
        div_le_div_of_nonneg_left (mul_nonneg hCgeo.le hA.le) (by norm_num) hdenHalf
      _ = _ := by ring
  have hdrift : 5 / 4 + (Cgeo * A₀ / (1 - ρ / b)) * T < d := by
    have hh := mul_le_mul_of_nonneg_right hdiv hT
    dsimp only [d]
    nlinarith only [hh, hcat]
  have hccore (i : Fin 2) : core ≤ 3 * circularContourRadii i / 4 := by
    have hi := (circularContourRadii_bounds i).2.1
    dsimp only [core]
    linarith only [hi, cellA_pos]
  dsimp only
  intro N k hkN S hS entrance Dcap he hD hDlog X hX hweighted hcur hparticles
    exit angle hexit hmatch
  have hAk : 0 < ampScale A₀ b k := div_pos hA (pow_pos hb k)
  have hDphys : 0 ≤ entrance + Dcap / ampScale A₀ b k := add_nonneg he (div_nonneg hD hAk.le)
  have hrad : radScale R ρ k ≤ ρ :=
    (mul_le_of_le_one_right hR.le (pow_le_one₀ hρ.le hρ1)).trans hRρ
  have hrad1 : radScale R ρ k ≤ 1 := hrad.trans hρ1
  have hgeomN : (L + 1) * radScale R ρ k ≤ (1 / 16 : ℝ) / 2 := by
    calc
      _ ≤ (L + 1) * ρ := mul_le_mul_of_nonneg_left hrad (by linarith only [hL])
      _ ≤ 1 / 32 := hgeom
      _ = _ := by norm_num
  have hpacketD : Cb * ρ * (1 + Dcap) ≤ packet := by
    simpa only [pow_one] using hpacket3 Dcap hD hDlog
  have hchartCap : Cb * ρ * radScale R ρ k * (1 + Dcap) ≤ 1 / 16 := by
    calc
      _ = (Cb * ρ * (1 + Dcap)) * radScale R ρ k := by ring
      _ ≤ Cb * ρ * (1 + Dcap) := mul_le_of_le_one_right (by positivity) hrad1
      _ ≤ _ := hpacketD.trans (min_le_left _ _)
  have hsepCap : 8 * (Cb * ρ * (1 + Dcap)) ≤ cellA / 2 := by
    have hh := hpacketD.trans (min_le_right _ _)
    linarith only [hh]
  let Bforce := Ktor * R ^ 8 * η + Kpoly * ρ ^ 6 * (1 + Dcap) ^ 4
  have hρ86 : R ^ 8 ≤ ρ ^ 6 :=
    (pow_le_pow_left₀ hR.le hRρ 8).trans (pow_le_pow_of_le_one hρ.le hρ1 (by decide))
  have hforce3 : Bforce ≤ ρ ^ 3 := by
    have htorBound : Ktor * R ^ 8 * η ≤ (1 / 2 : ℝ) * ρ ^ 3 := by
      calc
        _ ≤ (Ktor * η) * ρ ^ 6 := by nlinarith only [mul_le_mul_of_nonneg_left hρ86 (mul_nonneg hKtor hη.le)]
        _ = ((Ktor * η) * ρ ^ 3) * ρ ^ 3 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right htor3 (pow_nonneg hρ.le 3)
    have hpolyBound : Kpoly * ρ ^ 6 * (1 + Dcap) ^ 4 ≤ (1 / 2 : ℝ) * ρ ^ 3 := by
      calc
        _ = (Kpoly * ρ ^ 3 * (1 + Dcap) ^ 4) * ρ ^ 3 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (hpoly3 Dcap hD hDlog) (pow_nonneg hρ.le 3)
    dsimp only [Bforce]
    linarith only [htorBound, hpolyBound]
  have hbudget : Bforce ≤ εforce := hforce3.trans hforceSmall
  have hquant := hlook (s := s) (A₀ := A₀) (b := b) (R := R) (ρ := ρ) (q := q)
    (T := T) (Hglob := T) (a := 1 / 16) (d := d) (c := core) (δ := η)
    (Dphys := entrance + Dcap / ampScale A₀ b k) (entrance := entrance) (Dcap := Dcap) (offset := 0)
    (η := η) (Cb := Cb) (C₀ := 2) (K := 1) (Δ := 1)
    hs hA hb hb1 hR hRhalf hρ hρ1 hρb hq hqE le_rfl hdrift hdR
    hDphys he hD (by norm_num) hρsq hρcore
    (by norm_num) le_rfl hcore hccore hηa hη.le hηa hancient
    hCb (by norm_num) (by norm_num) (by norm_num)
    hh1 (by simpa only [mul_one] using hhη) hζ hsep hRchart houter
    (by simpa only [Bforce, Ktor, Kpoly, torusRow, zero_add, add_zero] using hbudget)
    N k hkN le_rfl hgeomN
    (by simpa only [add_zero] using hchartCap)
    (by simpa only [add_zero] using hsepCap)
    S hS X hX hweighted hcur (by simpa only [add_zero] using hparticles)
    exit angle hexit (hmatch.trans hmatchSmall)
  simp only [zero_add, add_zero] at hquant
  calc
    _ ≤ _ := hquant
    _ ≤ (Cmatch * ρ ^ 3 + ρ ^ 3 * Lback) * Real.exp ((Klook : ℝ) * Lback) :=
      mul_le_mul_of_nonneg_right (add_le_add hmatch
        (mul_le_mul_of_nonneg_right hforce3 hLback.le)) (Real.exp_pos _).le
    _ = ((Cmatch + Lback) * Real.exp ((Klook : ℝ) * Lback)) * ρ ^ 3 := by ring
    _ ≤ Cback * ρ ^ 3 :=
      mul_le_mul_of_nonneg_right (by dsimp only [Cback]; linarith) (pow_nonneg hρ.le 3)

end CircularMaterialTransferProfile
end Euler2D

end
