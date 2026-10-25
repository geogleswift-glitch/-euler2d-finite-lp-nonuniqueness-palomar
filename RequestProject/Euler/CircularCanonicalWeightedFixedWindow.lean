module

public import RequestProject.Euler.CircularCanonicalAncestorBootstrap
public import RequestProject.Euler.CircularCanonicalStageDeviation
public import RequestProject.Euler.CircularWeightedFixedWindow

/-! The actual ancestor sources retain an O(h) weighted bound on a
fixed observation window. The material tubes, own-label row estimates
and forcing are obtained from the same finite Euler trajectory. -/

@[expose] public section

set_option maxHeartbeats 24000000
set_option maxRecDepth 6500

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

attribute [local instance 2000] rigidGaugeLittle_group rigidGaugeLittle_space rigidGaugeFamily_tower
attribute [local instance] LittleContourSpace.complexScalarNormedSpace LittleContourSpace.complexScalarTower

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_uniform_actualCanonical_weighted_fixed_window_bound :
    let L := circularCanonicalCellNormBudget hγ hγ1
    ∃ Kself : ℝ≥0, 0 < Kself ∧ ∃ r > 0, ∃ Cgeo Ct Cd : ℝ,
      0 < Cgeo ∧ 0 < Ct ∧ 0 < Cd ∧
      ∀ b : ℝ≥0, 0 < b → b ≤ 1 →
      ∀ {core Cb C₀ νbar Lseed δ Kboot Ccur D : ℝ},
      0 < core → (∀ i, core ≤ 3 * circularContourRadii i / 4) →
      0 ≤ Cb → 2 ≤ C₀ → 0 ≤ Lseed → 0 ≤ Kboot → 0 ≤ Ccur → 0 ≤ D → δ ≤ cellA / 4 →
      ∀ {s A₀ R ρ q T Hglob a d Dphys entrance Dcap : ℝ},
      ∀ [Fact (1 ≤ ENNReal.ofReal q)] (hs : s ≤ 0) (hA : 0 < A₀)
        (hR : 0 < R) (hρ : 0 < ρ) (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q),
      let h := C₀ * ρ ^ 6
      let Cu := finiteInnerLabelLittleRowCoefficient (γ : ℝ) (cellA / 2) L
      let Cl := finiteOuterLabelLittleRowCoefficient (γ : ℝ) core L L
      let CtR := Ct * finiteTorusLabelLittleRowCoefficient (γ : ℝ) L * R ^ 8
      let β := 3 * CtR + weightedInteractionRowFeedback b Cu Cl C₀ ρ
      let F := ((Cu + 1) / C₀) * Ccur +
        finitePrefixUniformDeepCoefficient (γ : ℝ) (cellA / 2) L Cd Cb b * (1 + D) ^ 4
      R ≤ 1 / 2 → ρ ≤ 1 → ρ < b → ρ ^ 2 ≤ b / 2 →
      (5 / 4 : ℝ) * ρ ≤ cellA → 10 * ρ ≤ cellA / 2 → 8 * L * ρ ≤ core →
      h ≤ 1 → h * Kboot ≤ min r δ → Ccur * h ≤ δ → C₀ * ρ ^ 8 ≤ 1 / 2 →
      0 ≤ β → ((b * Kself : ℝ≥0) : ℝ) + β ≤ νbar → CtR ≤ 1 →
      Hglob ≤ T → 5 / 4 + (Cgeo * A₀ / (1 - ρ / b)) * Hglob < d → d * R ≤ 1 / 4 →
      0 < a → a ≤ 1 / 16 → (5 / 4 : ℝ) * R ≤ a → (L + 1) * R ≤ a / 2 →
      0 ≤ Dphys → 0 ≤ entrance → 0 ≤ Dcap → Dcap ≤ D →
      Cb * ρ * R * (1 + Dcap) ≤ a → 8 * (Cb * ρ * (1 + Dcap)) ≤ cellA / 2 →
      ∀ (N k : ℕ) (hkN : k ≤ N), entrance + Dcap / ampScale A₀ b k ≤ Dphys →
      ∀ S : BoundedEulerParticleSystem
        (finiteBaseCurlL2 (A₀ := A₀) (b := (b : ℝ)) hR hρ hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := (b : ℝ)) (q := q) hs hR hρ) N) T,
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
      (∀ τ ∈ Icc (0 : ℝ) Dcap, weightedFamilyNorm h k (x τ) ≤ Kboot) →
      weightedFamilyNorm h k (x 0) ≤ Lseed * h →
      (∀ τ ∈ Icc (0 : ℝ) Dcap, ‖x τ k‖ ≤ Ccur * h) →
      (∀ τ ∈ Icc (0 : ℝ) Dcap, ∀ z ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N k,
        ‖S.forward (physicalTimeFromNormalized (ampScale A₀ b k) entrance τ) z - torusCenter‖ ≤
          Cb * ρ * radScale R ρ k * (1 + τ)) →
      ∀ τ ∈ Icc (0 : ℝ) Dcap, weightedFamilyNorm h k (x τ) ≤
        (Lseed + F * D) * Real.exp (νbar * D) * h := by
  dsimp only
  obtain ⟨Kself, hKself, r, hr, hweighted⟩ := exists_circular_weighted_fixed_window_constants hγ hγ1
  obtain ⟨Cgeo, Ct, Cd, hCgeo, hCt, hCd, hactual⟩ := P.exists_uniform_actualCanonicalAncestor_bootstrap_budget
  refine ⟨Kself, hKself, r, hr, Cgeo, Ct, Cd, hCgeo, hCt, hCd, ?_⟩
  intro b hb hb1 core Cb C₀ νbar Lseed δ Kboot Ccur D
    hcore hcorei hCb hC₀ hLseed hKboot hCcur hD hδ
    s A₀ R ρ q T Hglob a d Dphys entrance Dcap _ hs hA hR hρ hq hqE
  let L := circularCanonicalCellNormBudget hγ hγ1
  let h := C₀ * ρ ^ 6
  let Cu := finiteInnerLabelLittleRowCoefficient (γ : ℝ) (cellA / 2) L
  let Cl := finiteOuterLabelLittleRowCoefficient (γ : ℝ) core L L
  let CtR := Ct * finiteTorusLabelLittleRowCoefficient (γ : ℝ) L * R ^ 8
  let β := 3 * CtR + weightedInteractionRowFeedback b Cu Cl C₀ ρ
  let Cpoly := finitePrefixUniformDeepCoefficient (γ : ℝ) (cellA / 2) L Cd Cb b
  let F := ((Cu + 1) / C₀) * Ccur + Cpoly * (1 + D) ^ 4
  intro hRmax hρ1 hρb hhalf hρcore hsepU hsepL hh1 hhsmall hcurSmall hζ hβ hνup hCtR1
    hglobT hdrift hdR ha ha16 hRchart htarget hDphys hentrance hDcap hcapD hchart hsep
    N k hkN htimeEnd S hS X hX hboot hinit hcurrent hparticles
  let x := canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance X
  have hAk : 0 < ampScale A₀ b k := by unfold ampScale; positivity
  have hC₀pos : 0 < C₀ := by linarith only [hC₀]
  have hh : 0 < h := mul_pos hC₀pos (pow_pos hρ 6)
  have hρ6h : ρ ^ 6 ≤ h := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (by linarith only [hC₀] : 1 ≤ C₀) (pow_nonneg hρ.le 6)
  have hL : 0 < L := circularCanonicalCellNormBudget_pos hγ hγ1
  have hcauchy : 0 ≤ cauchyContourNormBudget 5 (γ : ℝ) 1 (cellA / 2) L :=
    (cauchySpatialDerivativeBudget_nonneg 5 (by norm_num : (0 : ℝ) ≤ 1) (half_pos cellA_pos) 0).trans (le_max_left _ _)
  have hweight : 0 ≤ circularRadialPerturbationWeight :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (circularContourRadii_bounds i).1.le)
  have hCu : 0 ≤ Cu := by unfold Cu finiteInnerLabelLittleRowCoefficient; positivity
  have hCpoly : 0 ≤ Cpoly := by
    have htor : 0 ≤ torusCorrectionContourBudget (γ : ℝ) L := by unfold torusCorrectionContourBudget; positivity
    unfold Cpoly finitePrefixUniformDeepCoefficient
    positivity [finiteLabelMassBound_nonneg]
  have hF : 0 ≤ F := by dsimp only [F]; positivity
  let Y : ℕ → ℝ → Fin 2 → LittleContourSpace γ :=
    fun j τ => canonicalPrefixAbsoluteFamily A₀ b R ρ k entrance X τ j
  let u₀ : ℕ → ℝ := fun j => ampScale A₀ b j * entrance
  let cc := fun j τ => littleCircularMaterialContours hγ hγ1 (u₀ j + (b : ℝ) ^ (k - j) * τ)
  have hpoint (j : Fin k) (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) Dcap) :
      ∃ p : Fin 2 → LittleContourSpace γ,
        HasDerivAt (Y j) (((b : ℝ) ^ (k - (j : ℕ))) • circularBanachField hγ hγ1 (Y j τ) + p) τ ∧
        ‖p‖ ≤ h ^ (k - (j : ℕ)) *
          (β * weightedFamilyNorm h k (fun j => Y j τ - cc j τ) + F * h) := by
    let t := physicalTimeFromNormalized (ampScale A₀ b k) entrance τ
    have ht : t ∈ Icc (0 : ℝ) Dphys := by
      dsimp only [t, physicalTimeFromNormalized]
      exact ⟨add_nonneg hentrance (div_nonneg hτ.1 hAk.le),
        (add_le_add le_rfl (div_le_div_of_nonneg_right hτ.2 hAk.le)).trans htimeEnd⟩
    have hclock (l : ℕ) (hl : l ≤ k) : x τ l =
        canonicalPrefixAbsoluteFamily A₀ b R ρ k entrance X τ l -
          littleCircularMaterialContours hγ hγ1 (ampScale A₀ b l * t) :=
      canonicalPrefixStageDeviation_eq_physical hγ hγ1 hA.ne' (NNReal.coe_pos.mpr hb).ne'
        R ρ k entrance τ X l hl
    have hweighted := canonicalPrefixStageDeviation_weighted_eq_physical hγ hγ1 hA.ne'
      (NNReal.coe_pos.mpr hb).ne' R ρ k entrance τ h X
    have hboot' := hboot τ hτ
    rw [hweighted] at hboot'
    have hcur' : ‖canonicalPrefixAbsoluteFamily A₀ b R ρ k entrance X τ k -
        littleCircularMaterialContours hγ hγ1 (ampScale A₀ b k * t)‖ ≤ δ := by
      rw [← hclock k le_rfl]
      exact (hcurrent τ hτ).trans hcurSmall
    have hgeom : (L + 1) * radScale R ρ j ≤ a / 2 :=
      (mul_le_mul_of_nonneg_left
        (mul_le_of_le_one_right hR.le (pow_le_one₀ hρ.le hρ1)) (by linarith : 0 ≤ L + 1)).trans htarget
    have hchart' : Cb * ρ * radScale R ρ k * (1 + τ) ≤ a := by
      have hrk : radScale R ρ k ≤ R := mul_le_of_le_one_right hR.le (pow_le_one₀ hρ.le hρ1)
      exact (mul_le_mul (mul_le_mul_of_nonneg_left hrk (by positivity : 0 ≤ Cb * ρ))
        (add_le_add le_rfl hτ.2) (add_nonneg zero_le_one hτ.1) (by positivity)).trans hchart
    have hsep' : 8 * (Cb * ρ * (1 + τ)) ≤ cellA / 2 := by
      calc
        _ = (8 * (Cb * ρ)) * (1 + τ) := by ring
        _ ≤ (8 * (Cb * ρ)) * (1 + Dcap) :=
          mul_le_mul_of_nonneg_left (add_le_add le_rfl hτ.2) (by positivity)
        _ ≤ _ := by convert hsep using 1 <;> ring
    obtain ⟨p, hd, hp⟩ := hactual hs hA (NNReal.coe_pos.mpr hb) (show (b : ℝ) ≤ 1 from hb1)
      hR hRmax hρ hρ1 hρb hq hqE hglobT hdrift hdR hDphys hhalf hρcore ha ha16
      hcore hcorei hδ hCb hτ.1 hC₀ hKboot hh1 (hhsmall.trans (min_le_right _ _))
      hζ hsepU hsepL hRchart hCtR1 N k j hkN hgeom hchart' hsep' S hS X hX t ht entrance τ rfl le_rfl
      hboot' hcur' (hparticles τ hτ)
    refine ⟨p, ?_, ?_⟩
    · simpa only [Y, canonicalPrefixAbsoluteFamily, dif_pos j.isLt.le] using hd
    · dsimp only at hp
      rw [← hweighted, ← hclock k le_rfl] at hp
      have hpoly : (1 + τ) ^ 4 ≤ (1 + D) ^ 4 :=
        pow_le_pow_left₀ (by linarith only [hτ.1]) (add_le_add le_rfl (hτ.2.trans hcapD)) 4
      have hcoeff : ((Cu + 1) / C₀) * ‖x τ k‖ + Cpoly * ρ ^ 6 * (1 + τ) ^ 4 ≤ F * h := by
        calc
          _ ≤ ((Cu + 1) / C₀) * (Ccur * h) + Cpoly * h * (1 + D) ^ 4 :=
            add_le_add (mul_le_mul_of_nonneg_left (hcurrent τ hτ) (by positivity))
              (mul_le_mul (mul_le_mul_of_nonneg_left hρ6h hCpoly) hpoly (by positivity) (by positivity))
          _ = _ := by dsimp only [F]; ring
      have hrow : β * weightedFamilyNorm h k (x τ) + ((Cu + 1) / C₀) * ‖x τ k‖ +
          Cpoly * ρ ^ 6 * (1 + τ) ^ 4 ≤ β * weightedFamilyNorm h k (x τ) + F * h := by
        linarith only [hcoeff]
      exact hp.trans (mul_le_mul_of_nonneg_left hrow (by positivity))
  exact hweighted b hb hb1 hh hh1 hDcap hcapD hβ hLseed hF hKboot
    (hhsmall.trans (min_le_left _ _)) hνup k Y u₀ hboot hinit hpoint

end CircularMaterialTransferProfile
end Euler2D

end
