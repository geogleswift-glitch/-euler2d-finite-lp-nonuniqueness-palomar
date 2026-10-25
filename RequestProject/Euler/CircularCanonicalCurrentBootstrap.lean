module

public import RequestProject.Euler.CircularCanonicalCurrentBudget
public import RequestProject.Euler.CircularFiniteWeightedMaterialTube
public import RequestProject.Euler.CircularFiniteInnerParticleConfinement
public import RequestProject.Euler.EulerLabelParticleRadiusSupport

/-! The actual current-cell budget from genuine bootstrap quantities.
The same X supplies its material tube and each own-label deviation;
the actual inner particle bound supplies the rough-source support.
No geometric material tube, row bound or forcing is an input. -/

@[expose] public section

set_option maxHeartbeats 18000000
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

theorem exists_uniform_actualCanonicalCurrent_bootstrap_budget :
    let L := circularCanonicalCellNormBudget hγ hγ1
    ∃ Cgeo Ct Cd : ℝ, 0 < Cgeo ∧ 0 < Ct ∧ 0 < Cd ∧
      ∀ {s A₀ b R ρ q T Hglob a d c δ D Cb Dt C₀ K Δ : ℝ},
      ∀ [Fact (1 ≤ ENNReal.ofReal q)] (hs : s ≤ 0) (hA : 0 < A₀) (hb : 0 < b)
        (hb1 : b ≤ 1) (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
        (hρb : ρ < b) (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q),
      Hglob ≤ T → 5 / 4 + (Cgeo * A₀ / (1 - ρ / b)) * Hglob < d → d * R ≤ 1 / 4 →
      0 ≤ D → ρ ^ 2 ≤ b / 2 → (5 / 4 : ℝ) * ρ ≤ cellA →
      0 < a → a ≤ 1 / 16 → 0 < c → (∀ i, c ≤ 3 * circularContourRadii i / 4) →
      δ ≤ cellA / 4 → 0 ≤ Cb → 0 ≤ Dt → 1 ≤ C₀ → 0 ≤ K → 0 ≤ Δ →
      C₀ * ρ ^ 6 ≤ 1 → C₀ * ρ ^ 6 * K ≤ δ → C₀ * ρ ^ 8 ≤ 1 / 2 →
      8 * L * ρ ≤ c → (5 / 4 : ℝ) * R ≤ a →
      (2 * b * C₀ * K * (finiteOuterLabelLittleRowCoefficient (γ : ℝ) c L L +
        Ct * finiteTorusLabelLittleRowCoefficient (γ : ℝ) L)) * ρ ^ 2 ≤ Δ →
      ∀ (N k : ℕ) (hkN : k ≤ N),
      (L + 1) * radScale R ρ k ≤ a / 2 →
      Cb * ρ * radScale R ρ k * (1 + Dt) ≤ a →
      8 * (Cb * ρ * (1 + Dt)) ≤ cellA / 2 →
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
        (fun p => finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N (finiteCircularPrefixIndex hkN p)) D X →
      ∀ t ∈ Icc (0 : ℝ) D, ∀ entrance τ : ℝ,
      physicalTimeFromNormalized (ampScale A₀ b k) entrance τ = t →
      let Y := canonicalPrefixAbsoluteFamily A₀ b R ρ k entrance X τ
      let x := fun l => Y l - littleCircularMaterialContours hγ hγ1 (ampScale A₀ b l * t)
      weightedFamilyNorm (C₀ * ρ ^ 6) k x ≤ K → ‖x k‖ ≤ δ →
      (∀ z ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N k,
        ‖S.forward t z - torusCenter‖ ≤ Cb * ρ * radScale R ρ k * (1 + Dt)) →
      let y := fun u => canonicalPrefixAbsoluteCell A₀ b R ρ k entrance X u (Fin.last k)
      ∃ p : Fin 2 → LittleContourSpace γ,
        HasDerivAt y (circularBanachField hγ hγ1 (y τ) + p) τ ∧
        ‖p‖ ≤ Ct * finiteTorusLabelLittleRowCoefficient (γ : ℝ) L * R ^ 8 * ‖x k‖ +
          (finiteCurrentPolynomialForcingCoefficient (γ : ℝ) (cellA / 2) L Cb b Cd + Δ) *
            ρ ^ 6 * (1 + Dt) ^ 4 := by
  dsimp only
  obtain ⟨Cgeo, hCgeo, hgeo⟩ := P.exists_uniform_actualPrefix_weighted_materialTube
  obtain ⟨Ct, Cd, hCt, hCd, hcurrent⟩ := P.exists_uniform_actualCanonicalCurrent_derivative_budget
  refine ⟨Cgeo, Ct, Cd, hCgeo, hCt, hCd, ?_⟩
  intro s A₀ b R ρ q T Hglob a d c δ D Cb Dt C₀ K Δ _ hs hA hb hb1 hR hRmax hρ hρ1
    hρb hq hqE hglobT hdrift hdR hD hhalf hcore ha ha16 hc hccore hδ hCb hDt hC₀ hK hΔ
    hh1 hhK hζ hsepL hRchart hsmall N k hkN hgeom hchart hsep S hS X hX t ht entrance τ htime
  let Y := canonicalPrefixAbsoluteFamily A₀ b R ρ k entrance X τ
  let u : ℕ → ℝ := fun l => ampScale A₀ b l * t
  let φ : ℕ → ℝ := fun l => t * finiteAncestorAngularVelocity A₀ b l
  let x := fun l => Y l - littleCircularMaterialContours hγ hγ1 (u l)
  intro hx hcur hparticles
  have hC₀pos : 0 < C₀ := by linarith
  obtain ⟨G, hG, hownq⟩ := hgeo hs hA.le hb hR hRmax hρ hρ1 hρb hq hqE hglobT
    hdrift hdR hD hkN S hS X hX t ht hδ hccore hC₀pos hh1 hK hhK Y u φ hx hcur (by
      intro p
      have hh := congrArg (fun V : Fin 2 → LittleContourSpace γ => (V p.2).val)
        (canonicalPrefixAbsoluteCell_raw (A₀ := A₀) (b := b) hR hρ k entrance τ X p.1)
      rw [htime] at hh
      simpa only [Y, canonicalPrefixAbsoluteFamily, dif_pos (Nat.le_of_lt_succ p.1.isLt), φ,
        Pi.smul_apply] using hh.symm)
  have htT : t ∈ Icc (0 : ℝ) T := ⟨ht.1, (hX.mem t ht).1.2.trans hglobT⟩
  have hrad1 : Cb * ρ * radScale R ρ k * (1 + Dt) < 1 :=
    hchart.trans_lt (ha16.trans_lt (by norm_num))
  have hsupp : ∀ v ∈ torusBox, Cb * ρ * radScale R ρ k * (1 + Dt) < ‖v - torusCenter‖ →
      P.finiteInnerClusterSource s A₀ b R ρ N k S t v = 0 := by
    intro v hv hvr
    apply Finset.sum_eq_zero
    intro j hj
    apply S.transportedScalar_support_of_particle_radius htT hrad1 (fun _ hz => hz.1) ?_ hparticles v hv hvr
    intro z hz hn
    by_contra hne
    exact hn ⟨hz, j, hj, hne⟩
  have hwf : P.finiteInitialPeriodicDensity s A₀ b R ρ N =ᵐ[μT]
      (finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
        (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N : R2 → ℝ) := by
    filter_upwards [P.finiteBaseCurlL2_ae_density (A₀ := A₀) (b := b) hs hR hρ hq hqE N,
      ae_restrict_mem measurableSet_torusBox] with z hz hzbox
    exact (P.finiteInitialPeriodicDensity_eq_on_box hs hR hRmax hρ hρ1 N hzbox).trans hz.symm
  exact hcurrent hs hA hb hb1 hR hRmax hρ hρ1 hhalf hcore ha ha16 hc hCb hDt hC₀ hK hΔ
    hζ hsepL hRchart hsmall N k hkN S hS hglobT hwf X hX t ht G hG x hx hownq
    hgeom hchart hsupp hsep entrance τ htime

end CircularMaterialTransferProfile
end Euler2D

end
