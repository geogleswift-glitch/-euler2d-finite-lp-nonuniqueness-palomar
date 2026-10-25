module

public import RequestProject.Euler.CircularCanonicalCurrentBudget
public import RequestProject.Euler.CircularCanonicalCurrentCoordinates
public import RequestProject.Euler.CircularFiniteWeightedMaterialTube
public import RequestProject.Euler.EulerLabelParticleRadiusSupport

/-! A single actual current-cell curve, with its genuine forcing on
the whole stopped interval and its original constraint coordinates.
The source clock retains an arbitrary nonnegative entrance offset. -/

@[expose] public section

set_option maxHeartbeats 24000000
set_option maxRecDepth 6500

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

theorem exists_uniform_actualCanonical_alignedCurrent_dynamics :
    let L := circularCanonicalCellNormBudget hγ hγ1
    ∃ Cgeo Ct Cd ε : ℝ, 0 < Cgeo ∧ 0 < Ct ∧ 0 < Cd ∧ 0 < ε ∧
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
      IsBanachTimeDomainTrajectoryOn
        (S.actualPartialPhaseField (P.finiteInnerInitialLabel s A₀ b R ρ N k) hγ hγ1
          (finiteCircularReferenceC1 hγ hγ1 R ρ) (finiteCircularInterfaceRadius R ρ)
          (finiteCircularInterfaceRadius_pos hR hρ) (lift_finiteCircularReferenceC1 hγ hγ1 R ρ)
          (finiteCircularInterfaceStrength A₀ b))
        (S.actualPartialPhaseDomain (P.finiteInnerInitialLabel s A₀ b R ρ N k)
          (finiteCircularReferenceC1 hγ hγ1 R ρ) (finiteCircularInterfaceRadius R ρ) a Hglob)
        (fun p => finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N (finiteCircularPrefixIndex hkN p)) Dphys X →
      let x := canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance X
      (∀ τ ∈ Icc (0 : ℝ) Dcap, weightedFamilyNorm (C₀ * ρ ^ 6) k (x τ) ≤ K) →
      (∀ τ ∈ Icc (0 : ℝ) Dcap, ‖x τ k‖ ≤ δ) →
      (∀ τ ∈ Icc (0 : ℝ) Dcap, ∀ z ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N k,
        ‖S.forward (physicalTimeFromNormalized (ampScale A₀ b k) entrance τ) z - torusCenter‖ ≤
          Cb * ρ * radScale R ρ k * (1 + offset + τ)) →
      let y := canonicalPrefixAlignedCurrentCell A₀ b R ρ k entrance X
      ∃ p : ℝ → Fin 2 → LittleContourSpace γ, ∀ τ ∈ Icc (0 : ℝ) Dcap,
        HasDerivAt y (circularBanachField hγ hγ1 (y τ) + p τ) τ ∧
        ‖p τ‖ ≤ Ct * finiteTorusLabelLittleRowCoefficient (γ : ℝ) L * R ^ 8 *
            ‖y τ - littleCircularMaterialContours hγ hγ1 τ‖ +
          (finiteCurrentPolynomialForcingCoefficient (γ : ℝ) (cellA / 2) L Cb b Cd + Δ) *
            ρ ^ 6 * (1 + offset + τ) ^ 4 ∧
        y τ ∈ circularBanachDomain hγ hγ1 ∧
        (y τ ∈ ball (littleCircularReference hγ hγ1) ε →
          circularConstrainedChart hγ hγ1
            (circularConstraintProjectionToTangentCLM hγ hγ1.le (y τ - littleCircularReference hγ hγ1)) = y τ) := by
  dsimp only
  obtain ⟨Cgeo, hCgeo, hgeo⟩ := P.exists_uniform_actualPrefix_weighted_materialTube
  obtain ⟨Ct, Cd, hCt, hCd, hcurrent⟩ := P.exists_uniform_actualCanonicalCurrent_derivative_budget
  obtain ⟨ε, hε, hchart⟩ := P.exists_uniform_actualCanonical_alignedCurrent_constraintChart_radius
  refine ⟨Cgeo, Ct, Cd, ε, hCgeo, hCt, hCd, hε, ?_⟩
  intro s A₀ b R ρ q T Hglob a d c δ Dphys entrance Dcap offset η Cb C₀ K Δ _
    hs hA hb hb1 hR hRmax hρ hρ1 hρb hq hqE hglobT hdrift hdR hDphys hentrance hDcap hoff
    hhalf hcore ha ha16 hc hccore hδ hη hηa hancient hCb hC₀ hK hΔ hh1 hhK hζ hsepL hRchart hsmall
    N k hkN htimeEnd hgeom hchartCap hsepCap S hS X hX
  let L := circularCanonicalCellNormBudget hγ hγ1
  let x := canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance X
  let y := canonicalPrefixAlignedCurrentCell A₀ b R ρ k entrance X
  intro hZ hcur hparticles
  have hAk : 0 < ampScale A₀ b k := by unfold ampScale; positivity
  have hC₀pos : 0 < C₀ := by linarith only [hC₀]
  have hwf : P.finiteInitialPeriodicDensity s A₀ b R ρ N =ᵐ[μT]
      (finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
        (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N : R2 → ℝ) := by
    filter_upwards [P.finiteBaseCurlL2_ae_density (A₀ := A₀) (b := b) hs hR hρ hq hqE N,
      ae_restrict_mem measurableSet_torusBox] with z hz hzbox
    exact (P.finiteInitialPeriodicDensity_eq_on_box hs hR hRmax hρ hρ1 N hzbox).trans hz.symm
  have hpoint (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) Dcap) :
      ∃ p₁ : Fin 2 → LittleContourSpace γ,
        HasDerivAt y (circularBanachField hγ hγ1 (y τ) + p₁) τ ∧
        ‖p₁‖ ≤ Ct * finiteTorusLabelLittleRowCoefficient (γ : ℝ) L * R ^ 8 *
            ‖y τ - littleCircularMaterialContours hγ hγ1 τ‖ +
          (finiteCurrentPolynomialForcingCoefficient (γ : ℝ) (cellA / 2) L Cb b Cd + Δ) *
            ρ ^ 6 * (1 + offset + τ) ^ 4 ∧
        y τ ∈ circularBanachDomain hγ hγ1 ∧
        (y τ ∈ ball (littleCircularReference hγ hγ1) ε →
          circularConstrainedChart hγ hγ1
            (circularConstraintProjectionToTangentCLM hγ hγ1.le (y τ - littleCircularReference hγ hγ1)) = y τ) := by
    let t := physicalTimeFromNormalized (ampScale A₀ b k) entrance τ
    have ht : t ∈ Icc (0 : ℝ) Dphys := by
      change 0 ≤ entrance + τ / ampScale A₀ b k ∧ entrance + τ / ampScale A₀ b k ≤ Dphys
      exact ⟨add_nonneg hentrance (div_nonneg hτ.1 hAk.le),
        (add_le_add le_rfl (div_le_div_of_nonneg_right hτ.2 hAk.le)).trans htimeEnd⟩
    let Y := canonicalPrefixAbsoluteFamily A₀ b R ρ k entrance X τ
    let u : ℕ → ℝ := fun l => ampScale A₀ b l * entrance + b ^ (k - l) * τ
    let φ : ℕ → ℝ := fun l => t * finiteAncestorAngularVelocity A₀ b l
    obtain ⟨G, hG, hownq⟩ := hgeo hs hA.le hb hR hRmax hρ hρ1 hρb hq hqE hglobT
      hdrift hdR hDphys hkN S hS X hX t ht hδ hccore hC₀pos hh1 hK hhK Y u φ
      (hZ τ hτ) (hcur τ hτ) (by
        intro p
        have hh := congrArg (fun V : Fin 2 → LittleContourSpace γ => (V p.2).val)
          (canonicalPrefixAbsoluteCell_raw (A₀ := A₀) (b := b) hR hρ k entrance τ X p.1)
        simpa only [Y, canonicalPrefixAbsoluteFamily, dif_pos (Nat.le_of_lt_succ p.1.isLt), φ,
          Pi.smul_apply] using hh.symm)
    have hmem := hX.mem t ht
    have htT : t ∈ Icc (0 : ℝ) T := ⟨ht.1, hmem.1.2.trans hglobT⟩
    have hclock : 1 + (offset + τ) ≤ 1 + offset + Dcap := by linarith only [hτ.2]
    have hlocalChart : Cb * ρ * radScale R ρ k * (1 + (offset + τ)) ≤ a :=
      (mul_le_mul_of_nonneg_left hclock
        (mul_nonneg (mul_nonneg hCb hρ.le) (radScale_pos hR hρ k).le)).trans hchartCap
    have hlocalSep : 8 * (Cb * ρ * (1 + (offset + τ))) ≤ cellA / 2 :=
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hclock (mul_nonneg hCb hρ.le)) (by norm_num)).trans hsepCap
    have hrad1 : Cb * ρ * radScale R ρ k * (1 + (offset + τ)) < 1 :=
      hlocalChart.trans_lt (ha16.trans_lt (by norm_num))
    have hparticleLocal : ∀ z ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N k,
        ‖S.forward t z - torusCenter‖ ≤ Cb * ρ * radScale R ρ k * (1 + (offset + τ)) := by
      simpa only [t, add_assoc] using hparticles τ hτ
    have hsupp : ∀ v ∈ torusBox, Cb * ρ * radScale R ρ k * (1 + (offset + τ)) < ‖v - torusCenter‖ →
        P.finiteInnerClusterSource s A₀ b R ρ N k S t v = 0 := by
      intro v hv hvr
      apply Finset.sum_eq_zero
      intro j hj
      apply S.transportedScalar_support_of_particle_radius htT hrad1 (fun _ hz => hz.1) ?_ hparticleLocal v hv hvr
      intro z hz hn
      by_contra hne
      exact hn ⟨hz, j, hj, hne⟩
    obtain ⟨p₀, hpd, hpn⟩ := hcurrent hs hA hb hb1 hR hRmax hρ hρ1 hhalf hcore
      ha ha16 hc hCb (add_nonneg hoff hτ.1) hC₀ hK hΔ hζ hsepL hRchart hsmall
      N k hkN S hS hglobT hwf X hX t ht G hG (x τ) (hZ τ hτ) hownq
      hgeom hlocalChart hsupp hlocalSep entrance τ rfl
    have hm := canonicalPrefixAbsoluteCell_mem_circularDomain hγ hγ1 hR hρ A₀ b k X t
      hmem.2.1 hmem.2.2.2.1 (Fin.last k) entrance τ rfl
    have hpd' : HasDerivAt (fun u => canonicalPrefixAbsoluteCell A₀ b R ρ k entrance X u (Fin.last k))
        ((1 : ℝ) • circularBanachField hγ hγ1
          (canonicalPrefixAbsoluteCell A₀ b R ρ k entrance X τ (Fin.last k)) + p₀) τ := by
      simpa only [one_smul] using hpd
    have hshift := hasDerivAt_fixedEntranceAligned_slowForcedCircularCurve hγ hγ1 0
      (ampScale A₀ b k * entrance) 1 τ hm hpd'
    let p₁ := contourParameterShiftFamilyCLM γ
      (circularRetardedMaterialShift 0 (ampScale A₀ b k * entrance)) p₀
    refine ⟨p₁, ?_, ?_, ?_, ?_⟩
    · simpa only [y, canonicalPrefixAlignedCurrentCell, p₁, one_smul] using hshift.1
    · have hpn₁ : ‖p₁‖ = ‖p₀‖ := hshift.2
      rw [hpn₁, norm_canonicalPrefixAlignedCurrentCell_sub_reference hγ hγ1 A₀ b R ρ k entrance τ X]
      simpa only [add_assoc] using hpn
    · exact canonicalPrefixAlignedCurrentCell_mem_circularDomain hγ hγ1 hR hρ A₀ b k X t
        hmem.2.1 hmem.2.2.2.1 entrance τ rfl
    · intro hnear
      exact hchart hs hR hρ hη hηa hancient hkN htT G X hG rfl hnear
  let p : ℝ → Fin 2 → LittleContourSpace γ := fun τ =>
    if hτ : τ ∈ Icc (0 : ℝ) Dcap then Classical.choose (hpoint τ hτ) else 0
  refine ⟨p, ?_⟩
  intro τ hτ
  simpa only [p, dif_pos hτ] using Classical.choose_spec (hpoint τ hτ)

end CircularMaterialTransferProfile
end Euler2D

end
