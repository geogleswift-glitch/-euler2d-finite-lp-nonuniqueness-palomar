module

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

theorem exists_eventually_actualCoupledDeepest_earlier_section_match
    {sCanon b D η Cmatch Lback : ℝ}
    (hsCanon : sCanon ≤ 0) (hb : 0 < b) (hb1 : b ≤ 1) (hD : 0 ≤ D)
    (hη : 0 < η) (hηa : η ≤ cellA / 4) (hCmatch : 0 ≤ Cmatch) (hLback : 0 < Lback) :
    ∃ Cback > 0,
      ∀ {s cA q T : ℝ} [Fact (1 ≤ ENNReal.ofReal q)],
      ∀ (hs : s ≤ 0) (hcA : 0 < cA) (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q),
      0 ≤ T →
      ∀ᶠ ξ : ℝ in atTop,
      let ρ := Real.exp (-ξ)
      let hρ := Real.exp_pos (-ξ)
      let R := ρ ^ 10
      let hR := pow_pos hρ 10
      let A₀ := cA * (1 + ξ)
      ∀ N : ℕ,
      ∀ S : BoundedEulerParticleSystem
        (finiteBaseCurlL2 (A₀ := A₀) (b := b) (ρ := ρ) hR hρ hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := b) (ρ := ρ) (q := q) hs hR hρ) N) T,
      IsFourfoldBoundedEulerParticleSystem S →
      ∀ X : ℝ → FiniteCircularIndex N → LittleContourSpace γ,
      P.ActualCanonicalPrefixTrajectory s A₀ b R ρ (1 / 16) T hR hρ le_rfl S
        (D / ampScale A₀ b N) X →
      (∀ u ∈ Icc (0 : ℝ) D,
        weightedFamilyNorm (2 * ρ ^ 6) N
          (canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ N 0 X u) ≤ 1) →
      (∀ u ∈ Icc (0 : ℝ) D,
        ‖canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ N 0 X u N‖ ≤ η) →
      let y := canonicalPrefixAlignedCurrentCell A₀ b R ρ N 0 X
      ∀ exit angle : ℝ, exit ∈ Icc Lback D →
      ‖circularCoRotationCLM γ exit (y exit) -
        contourRotationFamilyLittleCLM γ angle (circularCoRotationCLM γ sCanon (P.ancient sCanon))‖ ≤ Cmatch * ρ ^ 3 →
      ‖circularCoRotationCLM γ (exit - Lback) (y (exit - Lback)) -
        contourRotationFamilyLittleCLM γ angle
          (circularCoRotationCLM γ (sCanon - Lback) (P.ancient (sCanon - Lback)))‖ ≤ Cback * ρ ^ 3 := by
  run_tac do IO.eprintln "coupled-earlier: entered body"
  obtain ⟨Cgeo, Ct, Cd, δmatch, εforce, hCgeo, hCt, hCd, hδmatch, hεforce, Klook, hlook⟩ :=
    P.exists_uniform_actualCanonical_capture_quantitative_lookback hsCanon hLback
  run_tac do IO.eprintln "coupled-earlier: selected lookback constants"
  let L := circularCanonicalCellNormBudget hγ hγ1
  let core := cellA / 2
  let torusRow := finiteTorusLabelLittleRowCoefficient (γ : ℝ) L
  let Cl := finiteOuterLabelLittleRowCoefficient (γ : ℝ) core L L
  let Ktor := Ct * torusRow
  let Kpoly := finiteCurrentPolynomialForcingCoefficient (γ : ℝ) (cellA / 2) L 0 b Cd + 1
  let Cforce := Ktor * η + Kpoly * (1 + D) ^ 4
  let Cback := (Cmatch + Cforce * Lback) * Real.exp ((Klook : ℝ) * Lback) + 1
  have hL : 0 < L := circularCanonicalCellNormBudget_pos hγ hγ1
  have hcore : 0 < core := half_pos cellA_pos
  have htorusRow : 0 ≤ torusRow := finiteTorusLabelLittleRowCoefficient_nonneg hL.le
  have hKtor : 0 ≤ Ktor := mul_nonneg hCt.le htorusRow
  have hcauchy : 0 ≤ cauchyContourNormBudget 5 (γ : ℝ) 1 (cellA / 2) L :=
    (cauchySpatialDerivativeBudget_nonneg 5 (by norm_num : (0 : ℝ) ≤ 1)
      (half_pos cellA_pos) 0).trans (le_max_left _ _)
  have htor : 0 ≤ torusCorrectionContourBudget (γ : ℝ) L := by
    unfold torusCorrectionContourBudget
    positivity
  have hKpoly : 0 ≤ Kpoly := by
    unfold Kpoly finiteCurrentPolynomialForcingCoefficient
    positivity [finiteLabelMassBound_nonneg]
  have hCforce : 0 ≤ Cforce := by dsimp only [Cforce]; positivity
  have hCback : 0 < Cback := by dsimp only [Cback]; positivity
  have hsmall (C : ℝ) (n : ℕ) (hn : n ≠ 0) (ε : ℝ) (hε : 0 < ε) :
      ∀ᶠ ξ : ℝ in atTop, C * Real.exp (-ξ) ^ n ≤ ε := by
    have ht : Tendsto (fun ξ : ℝ => C * Real.exp (-ξ) ^ n) atTop (𝓝 0) := by
      simpa only [zero_pow hn, mul_zero] using
        (Real.tendsto_exp_neg_atTop_nhds_zero.pow n).const_mul C
    exact (ht.eventually (gt_mem_nhds hε)).mono (fun _ h => h.le)
  run_tac do IO.eprintln "coupled-earlier: pure budgets ready"
  refine ⟨Cback, hCback, ?_⟩
  intro s cA q T _ hs hcA hq hqE hT
  let dcoef := 4 * Cgeo * cA * T
  let dsupport := fun ξ : ℝ => 2 + dcoef * (1 + ξ)
  have hdRlim : Tendsto (fun ξ : ℝ => dsupport ξ * Real.exp (-ξ) ^ 10) atTop (𝓝 0) := by
    convert tendsto_circularCapture_log_monomial 1 dcoef (1 + dcoef) 10 1 (by decide) using 1
    ext ξ
    dsimp only [dsupport]
    ring
  have hsmallDR := (hdRlim.eventually (gt_mem_nhds
    (by norm_num : (0 : ℝ) < 1 / 4))).mono (fun _ h => h.le)
  run_tac do IO.eprintln "coupled-earlier: eventual scale bounds ready"
  filter_upwards [hsmall 1 1 (by decide) (1 / 2) (by norm_num),
    hsmall 1 1 (by decide) (b / 2) (half_pos hb),
    hsmall 1 2 (by decide) (b / 2) (half_pos hb),
    hsmall (5 / 4) 1 (by decide) cellA cellA_pos,
    hsmall (5 / 4) 1 (by decide) (1 / 16) (by norm_num),
    hsmall 2 6 (by decide) 1 (by norm_num), hsmall 2 6 (by decide) η hη,
    hsmall 2 8 (by decide) (1 / 2) (by norm_num),
    hsmall (8 * L) 1 (by decide) core hcore,
    hsmallDR,
    hsmall (L + 1) 1 (by decide) (1 / 32) (by norm_num),
    hsmall (2 * b * 2 * 1 * (Cl + Ct * torusRow)) 2 (by decide) 1 (by norm_num),
    hsmall Cforce 6 (by decide) εforce hεforce,
    hsmall Cmatch 3 (by decide) δmatch hδmatch, eventually_ge_atTop (0 : ℝ)]
    with ξ hρhalf hρbhalf hρsq hρcore hρchart hh1 hhη hζ hsep hdR hgeom houter hforceSmall hmatchSmall hξ
  simp only [pow_one, one_mul] at hρhalf hρbhalf hρsq hρcore hρchart hsep hdR hgeom
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
  run_tac do IO.eprintln "coupled-earlier: instantiated coupled scale"
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
  let Bforce := Ktor * R ^ 8 * η + Kpoly * ρ ^ 6 * (1 + D) ^ 4
  have hρ86 : R ^ 8 ≤ ρ ^ 6 :=
    (pow_le_pow_left₀ hR.le hRρ 8).trans (pow_le_pow_of_le_one hρ.le hρ1 (by decide))
  have hforce : Bforce ≤ Cforce * ρ ^ 6 := by
    have hh := mul_le_mul_of_nonneg_left hρ86 (mul_nonneg hKtor hη.le)
    calc
      _ = (Ktor * η) * R ^ 8 + (Kpoly * (1 + D) ^ 4) * ρ ^ 6 := by dsimp only [Bforce]; ring
      _ ≤ (Ktor * η) * ρ ^ 6 + (Kpoly * (1 + D) ^ 4) * ρ ^ 6 := add_le_add hh le_rfl
      _ = _ := by dsimp only [Cforce]; ring
  have hbudget : Bforce ≤ εforce := hforce.trans hforceSmall
  run_tac do IO.eprintln "coupled-earlier: instantiating actual trajectory"
  dsimp only
  intro N S hS X hX hweighted hcur exit angle hexit hmatch
  have hAN : 0 < ampScale A₀ b N := div_pos hA (pow_pos hb N)
  have hDphys : 0 ≤ D / ampScale A₀ b N := div_nonneg hD hAN.le
  have hancientNorm : ‖P.ancient s - littleCircularReference hγ hγ1‖ ≤ η := by
    have hh := hcur 0 ⟨le_rfl, hD⟩
    rw [← norm_canonicalPrefixAlignedCurrentCell_sub_reference hγ hγ1 A₀ b R ρ N 0 0 X,
      P.actualCanonicalPrefix_initial_aligned_deepest hR hρ N S X hX,
      littleCircularMaterialContours_zero] at hh
    exact hh
  have hancient (i : Fin 2) :
      ‖(P.ancient s i).val - circularReferenceC1 hγ hγ1 i‖ ≤ η :=
    (norm_le_pi_norm (P.ancient s - littleCircularReference hγ hγ1) i).trans hancientNorm
  have hccore (i : Fin 2) : core ≤ 3 * circularContourRadii i / 4 := by
    have hi := (circularContourRadii_bounds i).2.1
    dsimp only [core]
    linarith only [hi, cellA_pos]
  have hrad : radScale R ρ N ≤ ρ :=
    (mul_le_of_le_one_right hR.le (pow_le_one₀ hρ.le hρ1)).trans hRρ
  have hgeomN : (L + 1) * radScale R ρ N ≤ (1 / 16 : ℝ) / 2 := by
    calc
      _ ≤ (L + 1) * ρ := mul_le_mul_of_nonneg_left hrad (by linarith only [hL])
      _ ≤ 1 / 32 := hgeom
      _ = _ := by norm_num
  have hparticles : ∀ u ∈ Icc (0 : ℝ) D,
      ∀ z ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N N,
      ‖S.forward (physicalTimeFromNormalized (ampScale A₀ b N) 0 u) z - torusCenter‖ ≤
        (0 : ℝ) * ρ * radScale R ρ N * (1 + (0 : ℝ) + u) := by
    intro u hu z hz
    rw [P.finiteInnerActiveInitialLabels_deepest] at hz
    exact (Set.notMem_empty z hz).elim
  run_tac do IO.eprintln "coupled-earlier: applying actual lookback"
  have hquant := hlook (s := s) (A₀ := A₀) (b := b) (R := R) (ρ := ρ) (q := q)
    (T := T) (Hglob := T) (a := 1 / 16) (d := d) (c := core) (δ := η)
    (Dphys := D / ampScale A₀ b N) (entrance := 0) (Dcap := D) (offset := 0)
    (η := η) (Cb := 0) (C₀ := 2) (K := 1) (Δ := 1)
    hs hA hb hb1 hR hRhalf hρ hρ1 hρb hq hqE le_rfl hdrift hdR
    hDphys (by norm_num) hD (by norm_num) hρsq hρcore
    (by norm_num) le_rfl hcore hccore hηa hη.le hηa hancient
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hh1 (by simpa only [mul_one] using hhη) hζ hsep hRchart houter
    (by simpa only [Bforce, Ktor, Kpoly, torusRow, zero_add, add_zero] using hbudget)
    N N le_rfl (by simpa only [zero_add] using (le_refl (D / ampScale A₀ b N))) hgeomN
    (by norm_num) (by simpa only [zero_mul, mul_zero] using (half_pos cellA_pos).le)
    S hS X hX hweighted hcur hparticles exit angle hexit (hmatch.trans hmatchSmall)
  run_tac do IO.eprintln "coupled-earlier: actual lookback applied"
  simp only [zero_add, add_zero] at hquant
  have hρ63 : ρ ^ 6 ≤ ρ ^ 3 := pow_le_pow_of_le_one hρ.le hρ1 (by decide)
  have hforce3 : Bforce ≤ Cforce * ρ ^ 3 :=
    hforce.trans (mul_le_mul_of_nonneg_left hρ63 hCforce)
  calc
    _ ≤ _ := hquant
    _ ≤ (Cmatch * ρ ^ 3 + (Cforce * ρ ^ 3) * Lback) * Real.exp ((Klook : ℝ) * Lback) :=
      mul_le_mul_of_nonneg_right (add_le_add hmatch
        (mul_le_mul_of_nonneg_right hforce3 hLback.le)) (Real.exp_pos _).le
    _ = ((Cmatch + Cforce * Lback) * Real.exp ((Klook : ℝ) * Lback)) * ρ ^ 3 := by ring
    _ ≤ Cback * ρ ^ 3 :=
      mul_le_mul_of_nonneg_right (by dsimp only [Cback]; linarith) (pow_nonneg hρ.le 3)

end CircularMaterialTransferProfile
end Euler2D

end
