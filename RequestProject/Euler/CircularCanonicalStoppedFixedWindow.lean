module

public import RequestProject.Euler.CircularCanonicalAlignedCurrentDynamics
public import RequestProject.Euler.CircularCanonicalInnerParticles
public import RequestProject.Euler.CircularFixedWindowCurrent

/-! A real finite Euler prefix on a fixed preactivation window.
Its small current bound follows from the actual forced equation and
its inner particle fence follows from the same bootstrap history. -/

@[expose] public section

set_option maxHeartbeats 28000000
set_option maxRecDepth 7000

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

theorem exists_uniform_actualCanonical_stopped_fixed_window_bound
    {b Cw D C₀ Lseed δ : ℝ} (hb : 0 < b) (hb1 : b < 1) (hCw : 0 ≤ Cw)
    (hD : 0 < D) (hC₀ : 2 ≤ C₀) (hLseed : 0 ≤ Lseed) (hδ : 0 < δ) (hδa : δ ≤ cellA / 4) :
    let L := circularCanonicalCellNormBudget hγ hγ1
    ∃ Cgeo Ct Cd Cr Kr Ccur : ℝ,
      0 < Cgeo ∧ 0 < Ct ∧ 0 < Cd ∧ 0 < Cr ∧ 0 < Kr ∧ 0 < Ccur ∧
      let Cb := radialStageRadiusConstant Cr Cw b
      ∀ᶠ ξ : ℝ in atTop,
      let ρ := Real.exp (-ξ)
      let h := C₀ * ρ ^ 6
      ∀ {s A₀ R q T Hglob a c d Dphys entrance Dcap η K : ℝ},
      ∀ [Fact (1 ≤ ENNReal.ofReal q)] (hs : s ≤ 0) (hA : 0 < A₀)
        (hR : 0 < R) (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q),
      R ≤ 1 / 2 → R ≤ ρ → ρ ≤ 1 → ρ ≤ b / 2 →
      Hglob ≤ T → 5 / 4 + (Cgeo * A₀ / (1 - ρ / b)) * Hglob < d → d * R ≤ 1 / 16 →
      0 < a → a ≤ 1 / 16 → 0 < c → 0 < d →
      0 ≤ Dphys → 0 ≤ entrance → 0 ≤ Dcap → Dcap ≤ D →
      ρ ^ 2 ≤ b / 2 → (5 / 4 : ℝ) * ρ ≤ cellA →
      (∀ i, c ≤ 3 * circularContourRadii i / 4) →
      0 ≤ η → η ≤ cellA / 4 →
      (∀ i, ‖(P.ancient s i).val - circularReferenceC1 hγ hγ1 i‖ ≤ η) →
      0 ≤ K → h ≤ 1 → h * K ≤ δ → C₀ * ρ ^ 8 ≤ 1 / 2 →
      8 * L * ρ ≤ c → (5 / 4 : ℝ) * R ≤ a →
      (2 * b * C₀ * K * (finiteOuterLabelLittleRowCoefficient (γ : ℝ) c L L +
        Ct * finiteTorusLabelLittleRowCoefficient (γ : ℝ) L)) * ρ ^ 2 ≤ 1 →
      b * finiteEulerUniformRadialCoefficient Kr b R ρ c d δ * Cb ^ 3 *
        ρ ^ 2 * (1 + Dcap) ^ 3 ≤ Cr / 2 →
      Cb * ρ * (1 + Dcap) ≤ c / 2 → Cb * ρ * (1 + Dcap) ≤ d →
      Cb * ρ * R * (1 + Dcap) ≤ a → 8 * (Cb * ρ * (1 + Dcap)) ≤ cellA / 2 →
      ∀ (N k : ℕ) (hkN : k ≤ N), entrance + Dcap / ampScale A₀ b k ≤ Dphys →
      (L + 1) * radScale R ρ k ≤ a / 2 →
      ∀ S : BoundedEulerParticleSystem
        (finiteBaseCurlL2 (A₀ := A₀) (b := b) (ρ := ρ) hR (Real.exp_pos (-ξ)) hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := b) (ρ := ρ) (q := q) hs hR (Real.exp_pos (-ξ))) N) T,
      IsFourfoldBoundedEulerParticleSystem S →
      ∀ X : ℝ → FiniteCircularIndex k → LittleContourSpace γ,
      IsBanachTimeDomainTrajectoryOn
        (S.actualPartialPhaseField (P.finiteInnerInitialLabel s A₀ b R ρ N k) hγ hγ1
          (finiteCircularReferenceC1 hγ hγ1 R ρ) (finiteCircularInterfaceRadius R ρ)
          (finiteCircularInterfaceRadius_pos hR (Real.exp_pos (-ξ)))
          (lift_finiteCircularReferenceC1 hγ hγ1 R ρ) (finiteCircularInterfaceStrength A₀ b))
        (S.actualPartialPhaseDomain (P.finiteInnerInitialLabel s A₀ b R ρ N k)
          (finiteCircularReferenceC1 hγ hγ1 R ρ) (finiteCircularInterfaceRadius R ρ) a Hglob)
        (fun p => finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N (finiteCircularPrefixIndex hkN p)) Dphys X →
      let x := canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance X
      (∀ τ ∈ Icc (0 : ℝ) Dcap, weightedFamilyNorm h k (x τ) ≤ K) →
      (∀ τ ∈ Icc (0 : ℝ) Dcap, ‖x τ k‖ ≤ δ) →
      ‖x 0 k‖ ≤ Lseed * h →
      (∀ z ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N k,
        ‖S.forward entrance z - torusCenter‖ ≤ Cw * ρ * radScale R ρ k) →
      (∀ τ ∈ Icc (0 : ℝ) Dcap, ‖x τ k‖ ≤ Ccur * h) ∧
      ∀ τ ∈ Icc (0 : ℝ) Dcap, ∀ z ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N k,
        ‖S.forward (physicalTimeFromNormalized (ampScale A₀ b k) entrance τ) z - torusCenter‖ ≤
          Cb * ρ * radScale R ρ k * (1 + τ) := by
  dsimp only
  obtain ⟨Cp, Cr, Kr, hCp, hCr, hKr, hparticles⟩ :=
    P.exists_uniform_actualCanonical_inner_particle_confinement hb hb1 hCw
  obtain ⟨Cdyn, Ct, Cd, _εchart, hCdyn, hCt, hCd, _hεchart, hdynamics⟩ :=
    P.exists_uniform_actualCanonical_alignedCurrent_dynamics
  let L := circularCanonicalCellNormBudget hγ hγ1
  let Cb := radialStageRadiusConstant Cr Cw b
  let Cgeo := max Cp Cdyn
  let Ktorus := Ct * finiteTorusLabelLittleRowCoefficient (γ : ℝ) L
  let Bpoly := finiteCurrentPolynomialForcingCoefficient (γ : ℝ) (cellA / 2) L Cb b Cd + 1
  have hCb : 0 < Cb := radialStageRadiusConstant_pos hCr hCw hb hb1
  have hL : 0 < L := circularCanonicalCellNormBudget_pos hγ hγ1
  have hKtorus : 0 ≤ Ktorus :=
    mul_nonneg hCt.le (finiteTorusLabelLittleRowCoefficient_nonneg hL.le)
  have hcauchy : 0 ≤ cauchyContourNormBudget 5 (γ : ℝ) 1 (cellA / 2) L :=
    (cauchySpatialDerivativeBudget_nonneg 5 (by norm_num : (0 : ℝ) ≤ 1)
      (half_pos cellA_pos) 0).trans (le_max_left _ _)
  have htor : 0 ≤ torusCorrectionContourBudget (γ : ℝ) L := by
    unfold torusCorrectionContourBudget
    positivity
  have hBpoly : 0 ≤ Bpoly := by
    unfold Bpoly finiteCurrentPolynomialForcingCoefficient
    positivity [finiteLabelMassBound_nonneg]
  obtain ⟨Ccur, hCcur, hcurrent⟩ := exists_circular_fixed_window_current_bound hγ hγ1
    hD (by linarith only [hC₀] : 1 ≤ C₀) hLseed hBpoly hKtorus hδ.le
  refine ⟨Cgeo, Ct, Cd, Cr, Kr, Ccur, hCp.trans_le (le_max_left _ _), hCt, hCd, hCr, hKr, hCcur, ?_⟩
  filter_upwards [hcurrent] with ξ hξ
  try dsimp only
  let ρ := Real.exp (-ξ)
  let h := C₀ * ρ ^ 6
  intro s A₀ R q T Hglob a c d Dphys entrance Dcap η K _ hs hA hR hq hqE
    hRmax hRρ hρ1 hρhalf hglobT hdrift hdR ha ha16 hc hdpos hDphys he hDcap hcapD
    hhalf hρcore hcore hη hηa hancient hK hh1 hhK hζ hsepL hRchart hsmall
    hcubic hinnerCore hinnerChart hchart hsep N k hkN htimeEnd hgeom S hS X hX hZ hcur hinit hstart
  let x := canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance X
  let y := canonicalPrefixAlignedCurrentCell A₀ b R ρ k entrance X
  have hρ : 0 < ρ := Real.exp_pos _
  have hρb : ρ < b := hρhalf.trans_lt (by linarith only [hb])
  have hden : 0 < 1 - ρ / b := sub_pos.mpr ((div_lt_one hb).mpr hρb)
  have hHglob : 0 ≤ Hglob := (hX.mem 0 ⟨le_rfl, hDphys⟩).1.2
  have hdriftFor (C₁ : ℝ) (hC₁ : C₁ ≤ Cgeo) :
      5 / 4 + (C₁ * A₀ / (1 - ρ / b)) * Hglob < d :=
    (add_le_add le_rfl (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hC₁ hA.le) hden.le) hHglob)).trans_lt hdrift
  have hpactual := hparticles hs hA hR hRmax hρ hρ1 hρhalf hq hqE
    hglobT (hdriftFor Cp (le_max_left _ _)) hdR hc hdpos hDphys he hDcap hhalf hδa hcore
    (by linarith only [hC₀]) hK hh1 hhK hcubic hinnerCore hinnerChart N k hkN htimeEnd S hS X hX
    hZ hcur hstart
  have hchartk : Cb * ρ * radScale R ρ k * (1 + Dcap) ≤ a := by
    have hrk : radScale R ρ k ≤ R := mul_le_of_le_one_right hR.le (pow_le_one₀ hρ.le hρ1)
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrk (by positivity : 0 ≤ Cb * ρ))
      (by linarith only [hDcap] : 0 ≤ 1 + Dcap)).trans hchart
  obtain ⟨p, hp⟩ := hdynamics hs hA hb hb1.le hR hRmax hρ hρ1 hρb hq hqE
    hglobT (hdriftFor Cdyn (le_max_right _ _)) (hdR.trans (by norm_num)) hDphys he hDcap
    (le_refl (0 : ℝ)) hhalf hρcore ha ha16 hc hcore hδa hη hηa hancient hCb.le
    (by linarith only [hC₀]) hK (by norm_num : (0 : ℝ) ≤ 1) hh1 hhK hζ hsepL hRchart hsmall
    N k hkN htimeEnd hgeom
    (by simpa only [add_zero, zero_add] using hchartk)
    (by simpa only [add_zero, zero_add] using hsep) S hS X hX hZ hcur
    (by simpa only [add_zero, zero_add] using hpactual)
  have hnorm (τ : ℝ) : ‖y τ - littleCircularMaterialContours hγ hγ1 τ‖ = ‖x τ k‖ :=
    norm_canonicalPrefixAlignedCurrentCell_sub_reference hγ hγ1 A₀ b R ρ k entrance τ X
  have hinitY : ‖y 0 - littleCircularReference hγ hγ1‖ ≤ Lseed * h := by
    rw [← littleCircularMaterialContours_zero hγ hγ1, hnorm]
    exact hinit
  have hbound := hξ hR hRρ hDcap hcapD y p
    (fun τ hτ => (hp τ hτ).1) hinitY
    (fun τ hτ => by rw [hnorm]; exact hcur τ hτ)
    (by intro τ hτ; simpa only [add_zero, zero_add, Ktorus, mul_assoc] using (hp τ hτ).2.1)
  exact ⟨(fun τ hτ => by rw [← hnorm]; exact hbound τ hτ), hpactual⟩

end CircularMaterialTransferProfile
end Euler2D

end
