module

public import RequestProject.Euler.CircularCanonicalAncientLookback
public import RequestProject.Euler.CircularCanonicalAlignedCurrentDynamics

/-! Earlier-entry matching for the SAME original canonical Euler
capture. Its isolated equation, domain and forcing are CONSTRUCTED
from the actual particle geometry and weighted bounds. The only new
smallness input is an explicit numerical physical-force budget; no
forced curve equation or future lookback closeness is assumed. -/

@[expose] public section

set_option maxHeartbeats 32000000
set_option maxRecDepth 8000

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

theorem exists_uniform_actualCanonical_capture_lookback_entry {sCanon Lback ζ : ℝ}
    (hsCanon : sCanon ≤ 0) (hLback : 0 < Lback) (hζ : 0 < ζ) :
    let L := circularCanonicalCellNormBudget hγ hγ1;
    ∃ Cgeo Ct Cd δmatch εforce : ℝ,
      0 < Cgeo ∧ 0 < Ct ∧ 0 < Cd ∧ 0 < δmatch ∧ 0 < εforce ∧
      ∀ {s A₀ b R ρ q T Hglob a d c δ Dphys entrance Dcap offset η Cb C₀ K Δ : ℝ},
      ∀ [Fact (1 ≤ ENNReal.ofReal q)] (hs : s ≤ 0) (hA : 0 < A₀) (hb : 0 < b)
        (hb1 : b ≤ 1) (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
        (hρb : ρ < b) (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q),
      Hglob ≤ T → 5 / 4 + (Cgeo * A₀ / (1 - ρ / b)) * Hglob < d → d * R ≤ 1 / 4 →
      0 ≤ Dphys → 0 ≤ entrance → 0 ≤ Dcap → 0 ≤ offset →
      ρ ^ 2 ≤ b / 2 → (5 / 4 : ℝ) * ρ ≤ cellA →
      0 < a → a ≤ 1 / 16 → 0 < c → (∀ i, c ≤ 3 * circularContourRadii i / 4) →
      δ ≤ cellA / 4 → 0 ≤ η → η ≤ cellA / 4 →
      (∀ i, ‖(P.ancient s i).val - circularReferenceC1 hγ hγ1 i‖ ≤ η) →
      0 ≤ Cb → 1 ≤ C₀ → 0 ≤ K → 0 ≤ Δ →
      C₀ * ρ ^ 6 ≤ 1 → C₀ * ρ ^ 6 * K ≤ δ → C₀ * ρ ^ 8 ≤ 1 / 2 →
      8 * L * ρ ≤ c → (5 / 4 : ℝ) * R ≤ a →
      (2 * b * C₀ * K * (finiteOuterLabelLittleRowCoefficient (γ : ℝ) c L L +
        Ct * finiteTorusLabelLittleRowCoefficient (γ : ℝ) L)) * ρ ^ 2 ≤ Δ →
      Ct * finiteTorusLabelLittleRowCoefficient (γ : ℝ) L * R ^ 8 * δ +
        (finiteCurrentPolynomialForcingCoefficient (γ : ℝ) (cellA / 2) L Cb b Cd + Δ) *
          ρ ^ 6 * (1 + offset + Dcap) ^ 4 ≤ εforce →
      ∀ (N k : ℕ) (hkN : k ≤ N),
      entrance + Dcap / ampScale A₀ b k ≤ Dphys →
      (L + 1) * radScale R ρ k ≤ a / 2 →
      Cb * ρ * radScale R ρ k * (1 + offset + Dcap) ≤ a →
      8 * (Cb * ρ * (1 + offset + Dcap)) ≤ cellA / 2 →
      ∀ S : BoundedEulerParticleSystem
        (finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N) T,
      IsFourfoldBoundedEulerParticleSystem S →
      ∀ X : ℝ → FiniteCircularIndex k → LittleContourSpace γ,
      P.ActualCanonicalPrefixTrajectory s A₀ b R ρ a Hglob hR hρ hkN S Dphys X →
      let x := canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance X;
      (∀ τ ∈ Icc (0 : ℝ) Dcap, weightedFamilyNorm (C₀ * ρ ^ 6) k (x τ) ≤ K) →
      (∀ τ ∈ Icc (0 : ℝ) Dcap, ‖x τ k‖ ≤ δ) →
      (∀ τ ∈ Icc (0 : ℝ) Dcap, ∀ z ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N k,
        ‖S.forward (physicalTimeFromNormalized (ampScale A₀ b k) entrance τ) z - torusCenter‖ ≤
          Cb * ρ * radScale R ρ k * (1 + offset + τ)) →
      let y := canonicalPrefixAlignedCurrentCell A₀ b R ρ k entrance X;
      ∀ exit angle : ℝ, exit ∈ Icc Lback Dcap →
      ‖circularCoRotationCLM γ exit (y exit) -
        contourRotationFamilyLittleCLM γ angle (circularCoRotationCLM γ sCanon (P.ancient sCanon))‖ ≤ δmatch →
      ‖circularCoRotationCLM γ (exit - Lback) (y (exit - Lback)) -
        contourRotationFamilyLittleCLM γ angle
          (circularCoRotationCLM γ (sCanon - Lback) (P.ancient (sCanon - Lback)))‖ < ζ := by
  dsimp only
  obtain ⟨Cgeo, Ct, Cd, εchart, hCgeo, hCt, hCd, hεchart, hdynamics⟩ :=
    P.exists_uniform_actualCanonical_alignedCurrent_dynamics
  obtain ⟨δmatch, hδmatch, εforce, hεforce, hlookback⟩ :=
    P.exists_canonical_ancient_lookback_entry_accuracy hsCanon hLback hζ
  refine ⟨Cgeo, Ct, Cd, δmatch, εforce, hCgeo, hCt, hCd, hδmatch, hεforce, ?_⟩
  intro s A₀ b R ρ q T Hglob a d c δ Dphys entrance Dcap offset η Cb C₀ K Δ _
    hs hA hb hb1 hR hRmax hρ hρ1 hρb hq hqE hglobT hdrift hdR hDphys hentrance hDcap hoff
    hhalf hcore ha ha16 hc hccore hδ hη hηa hancient hCb hC₀ hK hΔ hh1 hhK hζrho hsepL hRchart
    hsmall hbudget N k hkN htimeEnd hgeom hchartCap hsepCap S hS X hX hZ hcur hparticles exit angle hexit hmatch
  let L := circularCanonicalCellNormBudget hγ hγ1
  let y := canonicalPrefixAlignedCurrentCell A₀ b R ρ k entrance X
  obtain ⟨p, hp⟩ := hdynamics hs hA hb hb1 hR hRmax hρ hρ1 hρb hq hqE hglobT hdrift hdR
    hDphys hentrance hDcap hoff hhalf hcore ha ha16 hc hccore hδ hη hηa hancient hCb hC₀ hK hΔ
    hh1 hhK hζrho hsepL hRchart hsmall N k hkN htimeEnd hgeom hchartCap hsepCap S hS X hX
    hZ hcur hparticles
  have hL : 0 < L := circularCanonicalCellNormBudget_pos hγ hγ1
  have htorus : 0 ≤ Ct * finiteTorusLabelLittleRowCoefficient (γ : ℝ) L * R ^ 8 :=
    mul_nonneg (mul_nonneg hCt.le (finiteTorusLabelLittleRowCoefficient_nonneg hL.le)) (by positivity)
  have hcauchy : 0 ≤ cauchyContourNormBudget 5 (γ : ℝ) 1 (cellA / 2) L :=
    (cauchySpatialDerivativeBudget_nonneg 5 (by norm_num : (0 : ℝ) ≤ 1)
      (half_pos cellA_pos) 0).trans (le_max_left _ _)
  have htor : 0 ≤ torusCorrectionContourBudget (γ : ℝ) L := by
    unfold torusCorrectionContourBudget
    positivity
  have hB : 0 ≤ finiteCurrentPolynomialForcingCoefficient (γ : ℝ) (cellA / 2) L Cb b Cd + Δ := by
    unfold finiteCurrentPolynomialForcingCoefficient
    positivity [finiteLabelMassBound_nonneg]
  have htime (u : ℝ) (hu : u ∈ Icc (0 : ℝ) Lback) : exit - u ∈ Icc (0 : ℝ) Dcap :=
    ⟨by linarith only [hexit.1, hu.2], by linarith only [hexit.2, hu.1]⟩
  apply hlookback exit angle y p
    (fun u hu => (hp (exit - u) (htime u hu)).2.2.1)
    (fun u hu => (hp (exit - u) (htime u hu)).1) _ hmatch
  intro u hu
  have ht := htime u hu
  have hnorm : ‖y (exit - u) - littleCircularMaterialContours hγ hγ1 (exit - u)‖ ≤ δ := by
    dsimp only [y]
    rw [norm_canonicalPrefixAlignedCurrentCell_sub_reference hγ hγ1 A₀ b R ρ k entrance (exit - u) X]
    exact hcur (exit - u) ht
  have hpow : (1 + offset + (exit - u)) ^ 4 ≤ (1 + offset + Dcap) ^ 4 :=
    pow_le_pow_left₀ (by linarith only [hoff, ht.1]) (by linarith only [ht.2]) 4
  have hh := add_le_add (mul_le_mul_of_nonneg_left hnorm htorus)
    (mul_le_mul_of_nonneg_left hpow (mul_nonneg hB (pow_nonneg hρ.le 6)))
  exact ((hp (exit - u) ht).2.1.trans hh).trans hbudget

end CircularMaterialTransferProfile
end Euler2D

end
