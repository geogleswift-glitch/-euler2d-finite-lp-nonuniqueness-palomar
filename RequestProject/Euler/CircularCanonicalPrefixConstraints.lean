module

public import RequestProject.Euler.CircularCanonicalCurrentCoordinates
public import RequestProject.Euler.CircularFiniteWeightedMaterialTube
public import RequestProject.Euler.CircularCanonicalPrefixMaterialBoundary

/-! The constraints of the same actual canonical prefix follow from
its genuine transported material domains. A single fixed entrance
alignment preserves both fourfold symmetry and the original areas. -/

@[expose] public section

set_option maxHeartbeats 16000000
set_option maxRecDepth 6500

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

attribute [local instance 2000] rigidGaugeLittle_group rigidGaugeLittle_space rigidGaugeFamily_tower
attribute [local instance] LittleContourSpace.complexScalarNormedSpace LittleContourSpace.complexScalarTower
attribute [local irreducible] contourC1GraphSubmodule holderGraphSubmodule
  circularBanachField circularBanachDomain

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem actualCanonical_alignedCurrent_constraints_of_materialTube
    {s R ρ η A₀ b entrance τ t : ℝ} (hs : s ≤ 0)
    (hR : 0 < R) (hρ : 0 < ρ) (hη : 0 ≤ η) (hηa : η ≤ cellA / 4)
    (hancient : ∀ i, ‖(P.ancient s i).val - circularReferenceC1 hγ hγ1 i‖ ≤ η)
    {N k : ℕ} (hkN : k ≤ N) {f : Lp ℝ 2 μT} {T : ℝ}
    {S : BoundedEulerParticleSystem f T} {c δ : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) (G : P.FiniteOuterMaterialTube s R ρ N k S t c δ)
    (X : ℝ → FiniteCircularIndex k → LittleContourSpace γ)
    (hG : ∀ p, G.contours (finiteCircularPrefixIndex hkN p) = (X t p).val)
    (htime : physicalTimeFromNormalized (ampScale A₀ b k) entrance τ = t) :
    (∀ i, canonicalPrefixAlignedCurrentCell A₀ b R ρ k entrance X τ i ∈
      fourfoldLittleContourSubmodule γ) ∧
    ∀ i, littleContourArea γ (canonicalPrefixAlignedCurrentCell A₀ b R ρ k entrance X τ i) =
      Real.pi * circularContourRadii i ^ 2 := by
  let Y := canonicalPrefixAbsoluteCell A₀ b R ρ k entrance X τ (Fin.last k)
  let β := circularRetardedMaterialShift 0 (ampScale A₀ b k * entrance)
  have hraw (i : Fin 2) :
      G.contours (finitePrefixForcingIndex hkN (Fin.last k), i) =
        (radScale R ρ (finitePrefixForcingIndex hkN (Fin.last k)) •
          (exp (((t * finiteAncestorAngularVelocity A₀ b k : ℝ) : ℂ) * I) • Y i)).val := by
    have hh := congrArg (fun V : Fin 2 → LittleContourSpace γ => (V i).val)
      (canonicalPrefixAbsoluteCell_raw (A₀ := A₀) (b := b) hR hρ k entrance τ X (Fin.last k))
    rw [htime] at hh
    simpa only [Y, finitePrefixForcingIndex, finiteCircularPrefixIndex, Fin.val_last, Pi.smul_apply] using
      (hG (Fin.last k, i)).trans hh.symm
  obtain ⟨hfour, harea⟩ := P.finiteOuterMaterialTube_normalized_constraints
    hs hR hρ hη hηa hancient ht G (finitePrefixForcingIndex hkN (Fin.last k))
    (by simp only [finitePrefixForcingIndex, Fin.val_last, le_refl])
    (t * finiteAncestorAngularVelocity A₀ b k) Y hraw
  constructor
  · intro i
    change contourParameterShiftLittleCLM γ (β i) (Y i) ∈ fourfoldLittleContourSubmodule γ
    exact mem_fourfoldLittleContourSubmodule_parameterShift (β i) (Y i) (hfour i)
  · intro i
    change littleContourArea γ (contourParameterShiftLittleCLM γ (β i) (Y i)) = _
    exact (littleContourArea_parameterShiftLittleCLM (β i) (Y i)).trans (harea i)

theorem exists_uniform_actualCanonical_prefix_constraints :
    ∃ Cgeo > 0, ∀ {s A₀ b R ρ q T Hglob a d Dphys core δ η C₀ K : ℝ},
      ∀ [Fact (1 ≤ ENNReal.ofReal q)] (hs : s ≤ 0) (hA : 0 ≤ A₀) (hb : 0 < b)
        (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
        (hρb : ρ < b) (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q),
      Hglob ≤ T → 5 / 4 + (Cgeo * A₀ / (1 - ρ / b)) * Hglob < d → d * R ≤ 1 / 4 →
      0 ≤ Dphys → δ ≤ cellA / 4 → (∀ i, core ≤ 3 * circularContourRadii i / 4) →
      0 < C₀ → C₀ * ρ ^ 6 ≤ 1 → 0 ≤ K → C₀ * ρ ^ 6 * K ≤ δ →
      0 ≤ η → η ≤ cellA / 4 →
      (∀ i, ‖(P.ancient s i).val - circularReferenceC1 hγ hγ1 i‖ ≤ η) →
      ∀ {N k : ℕ} (hkN : k ≤ N),
      ∀ S : BoundedEulerParticleSystem
        (finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N) T,
      IsFourfoldBoundedEulerParticleSystem S →
      ∀ X : ℝ → FiniteCircularIndex k → LittleContourSpace γ,
      P.ActualCanonicalPrefixTrajectory s A₀ b R ρ a Hglob hR hρ hkN S Dphys X →
      ∀ t ∈ Icc (0 : ℝ) Dphys, ∀ entrance τ : ℝ,
      physicalTimeFromNormalized (ampScale A₀ b k) entrance τ = t →
      weightedFamilyNorm (C₀ * ρ ^ 6) k
        (canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance X τ) ≤ K →
      ‖canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance X τ k‖ ≤ δ →
      (∀ i, canonicalPrefixAlignedCurrentCell A₀ b R ρ k entrance X τ i ∈
        fourfoldLittleContourSubmodule γ) ∧
      ∀ i, littleContourArea γ (canonicalPrefixAlignedCurrentCell A₀ b R ρ k entrance X τ i) =
        Real.pi * circularContourRadii i ^ 2 := by
  obtain ⟨Cgeo, hCgeo, hgeo⟩ := P.exists_uniform_actualPrefix_weighted_materialTube
  refine ⟨Cgeo, hCgeo, ?_⟩
  intro s A₀ b R ρ q T Hglob a d Dphys core δ η C₀ K _ hs hA hb hR hRmax hρ hρ1
    hρb hq hqE hglobT hdrift hdR hDphys hδ hcore hC₀ hh1 hK hhK hη hηa hancient
    N k hkN S hS X hX t ht entrance τ htime hZ hcur
  let Y := canonicalPrefixAbsoluteFamily A₀ b R ρ k entrance X τ
  let u : ℕ → ℝ := fun l => ampScale A₀ b l * entrance + b ^ (k - l) * τ
  let φ : ℕ → ℝ := fun l => t * finiteAncestorAngularVelocity A₀ b l
  obtain ⟨G, hG, _hownq⟩ := hgeo hs hA hb hR hRmax hρ hρ1 hρb hq hqE hglobT
    hdrift hdR hDphys hkN S hS X hX t ht hδ hcore hC₀ hh1 hK hhK Y u φ hZ hcur (by
      intro p
      have hh := congrArg (fun V : Fin 2 → LittleContourSpace γ => (V p.2).val)
        (canonicalPrefixAbsoluteCell_raw (A₀ := A₀) (b := b) hR hρ k entrance τ X p.1)
      rw [htime] at hh
      simpa only [Y, canonicalPrefixAbsoluteFamily, dif_pos (Nat.le_of_lt_succ p.1.isLt), φ,
        Pi.smul_apply] using hh.symm)
  have htT : t ∈ Icc (0 : ℝ) T := ⟨ht.1, (hX.mem t ht).1.2.trans hglobT⟩
  exact P.actualCanonical_alignedCurrent_constraints_of_materialTube hs hR hρ hη hηa hancient
    hkN htT G X hG htime

end CircularMaterialTransferProfile
end Euler2D

end
