module

public import RequestProject.Euler.CircularFinitePrefixCanonicalUniqueness
public import RequestProject.Euler.CircularCanonicalStageDeviation

/-! Valid canonical prefixes follow the same original material
particles, including their original boundary parameter. The abbreviation
below is the existing canonical trajectory predicate without alteration. -/

@[expose] public section

set_option maxHeartbeats 10000000
set_option maxRecDepth 5000

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

attribute [local instance 2000] rigidGaugeLittle_group rigidGaugeLittle_space rigidGaugeFamily_tower

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

abbrev ActualCanonicalPrefixTrajectory (s A₀ b R ρ a Hglob : ℝ)
    (hR : 0 < R) (hρ : 0 < ρ) {N k : ℕ} (hkN : k ≤ N)
    {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)
    (D : ℝ) (X : ℝ → FiniteCircularIndex k → LittleContourSpace γ) : Prop :=
  IsBanachTimeDomainTrajectoryOn
    (S.actualPartialPhaseField (P.finiteInnerInitialLabel s A₀ b R ρ N k) hγ hγ1
      (finiteCircularReferenceC1 hγ hγ1 R ρ) (finiteCircularInterfaceRadius R ρ)
      (finiteCircularInterfaceRadius_pos hR hρ) (lift_finiteCircularReferenceC1 hγ hγ1 R ρ)
      (finiteCircularInterfaceStrength A₀ b))
    (S.actualPartialPhaseDomain (P.finiteInnerInitialLabel s A₀ b R ρ N k)
      (finiteCircularReferenceC1 hγ hγ1 R ρ) (finiteCircularInterfaceRadius R ρ) a Hglob)
    (fun p => finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N (finiteCircularPrefixIndex hkN p)) D X

theorem exists_uniform_actualCanonical_prefix_material_boundary :
    ∃ C : ℝ, 0 < C ∧ ∀ {s A₀ b R ρ q T Hglob c : ℝ},
      ∀ [Fact (1 ≤ ENNReal.ofReal q)] (hs : s ≤ 0) (hA : 0 ≤ A₀) (hb : 0 < b)
        (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
        (hρb : ρ < b) (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q),
      Hglob ≤ T → 5 / 4 + (C * A₀ / (1 - ρ / b)) * Hglob < c → c * R ≤ 1 / 4 →
      ∀ N : ℕ,
      ∀ S : BoundedEulerParticleSystem
        (finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N) T,
      ∀ {k : ℕ} (hkN : k ≤ N) {a D : ℝ}, 0 ≤ D →
      ∀ X : ℝ → FiniteCircularIndex k → LittleContourSpace γ,
      P.ActualCanonicalPrefixTrajectory s A₀ b R ρ a Hglob hR hρ hkN S D X →
      ∀ t ∈ Icc (0 : ℝ) D, ∀ p θ,
        S.forward t (complexTorusPoint (LittleContourSpace.lift γ
          (finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N (finiteCircularPrefixIndex hkN p)) θ)) =
          complexTorusPoint (LittleContourSpace.lift γ (X t p) θ) := by
  obtain ⟨C, hC, hidentify⟩ := P.exists_uniform_finiteEuler_partial_material_identification
  refine ⟨C, hC, ?_⟩
  intro s A₀ b R ρ q T Hglob c _ hs hA hb hR hRmax hρ hρ1 hρb hq hqE hglobT hc hcR
    N S k hkN a D hD X hX
  let Z : ℝ → FiniteCircularIndex k → ContourC1Space γ := fun t p => (X t p).val
  have hZ0 : Z 0 = fun p =>
      (finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N (finiteCircularPrefixIndex hkN p)).val :=
    congrArg (fun Y : FiniteCircularIndex k → LittleContourSpace γ => fun p => (Y p).val) hX.initial
  have hphase : ∀ t ∈ Icc (0 : ℝ) D, ∃ β : FiniteCircularIndex k → ℝ, ∀ p,
      ‖contourParameterShiftC1 (β p) (Z t p) - finiteCircularReferenceC1 hγ hγ1 R ρ p‖ <
        finiteCircularInterfaceRadius R ρ p / 4 := fun t ht => (hX.mem t ht).2.2.2.1
  have hZc (p : FiniteCircularIndex k) : ContinuousOn (fun t => Z t p) (Icc (0 : ℝ) D) :=
    (LittleContourSpace.inclusion γ).continuous.comp_continuousOn
      ((continuous_apply p).comp_continuousOn hX.continuous)
  have hmat : ∀ t ∈ Icc (0 : ℝ) D, ∀ p θ,
      HasDerivAt (fun u => ContourC1Space.lift γ (Z u p) θ)
        (contourC1BoundaryField (finiteCircularInterfaceStrength A₀ b) (Z t) p θ +
          S.physicalLabelComplexField (P.finiteInnerInitialLabel s A₀ b R ρ N k) t
            (ContourC1Space.lift γ (Z t p) θ)) t := by
    intro t ht
    exact (S.actualPartialPhaseField_material_iff hγ hγ1
      (finiteCircularReferenceC1 hγ hγ1 R ρ) (finiteCircularInterfaceRadius R ρ)
      (finiteCircularInterfaceRadius_pos hR hρ) (lift_finiteCircularReferenceC1 hγ hγ1 R ρ)
      (finiteCircularInterfaceStrength A₀ b) (hX.hasDerivAt t ht) (hX.mem t ht).2.1).mpr
        (hX.mem t ht).2.2.2.2
  have hDglob : D ≤ Hglob := (hX.mem D ⟨hD, le_rfl⟩).1.2
  have hcoef : 0 ≤ C * A₀ / (1 - ρ / b) :=
    div_nonneg (mul_nonneg hC.le hA) (sub_pos.mpr ((div_lt_one hb).mpr hρb)).le
  have hcD : 5 / 4 + (C * A₀ / (1 - ρ / b)) * D < c :=
    lt_of_le_of_lt (add_le_add le_rfl (mul_le_mul_of_nonneg_left hDglob hcoef)) hc
  have hi := hidentify hs hA hb hR hRmax hρ hρ1 hρb hq hqE hD (hDglob.trans hglobT)
    hcD hcR hkN S Z hZ0 hphase hZc hmat
  intro t ht p θ
  have hh := (hi t ht).1 p θ
  rw [hZ0] at hh
  exact hh

theorem exists_uniform_actualCanonical_crossPrefix_agreement :
    ∃ C : ℝ, 0 < C ∧ ∀ {s A₀ b R ρ q T Hglob c : ℝ},
      ∀ [Fact (1 ≤ ENNReal.ofReal q)] (hs : s ≤ 0) (hA : 0 ≤ A₀) (hb : 0 < b)
        (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
        (hρb : ρ < b) (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q),
      Hglob ≤ T → 5 / 4 + (C * A₀ / (1 - ρ / b)) * Hglob < c → c * R ≤ 1 / 4 →
      ∀ N : ℕ,
      ∀ S : BoundedEulerParticleSystem
        (finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N) T,
      ∀ {k l : ℕ} (hlk : l ≤ k) (hkN : k ≤ N),
      ∀ {a₁ a₂ D₁ D₂ : ℝ}
        {X : ℝ → FiniteCircularIndex k → LittleContourSpace γ}
        {Y : ℝ → FiniteCircularIndex l → LittleContourSpace γ},
      P.ActualCanonicalPrefixTrajectory s A₀ b R ρ a₁ Hglob hR hρ hkN S D₁ X →
      P.ActualCanonicalPrefixTrajectory s A₀ b R ρ a₂ Hglob hR hρ (hlk.trans hkN) S D₂ Y →
      ∀ t, t ∈ Icc (0 : ℝ) D₁ → t ∈ Icc (0 : ℝ) D₂ →
      ∀ p : FiniteCircularIndex l, Y t p = X t (finiteCircularPrefixIndex hlk p) := by
  obtain ⟨C, hC, hboundary⟩ := P.exists_uniform_actualCanonical_prefix_material_boundary
  refine ⟨C, hC, ?_⟩
  intro s A₀ b R ρ q T Hglob c _ hs hA hb hR hRmax hρ hρ1 hρb hq hqE hglobT hc hcR
    N S k l hlk hkN a₁ a₂ D₁ D₂ X Y hX hY t htX htY p
  have hBX := hboundary hs hA hb hR hRmax hρ hρ1 hρb hq hqE hglobT hc hcR N S hkN
    (htX.1.trans htX.2) X hX t htX (finiteCircularPrefixIndex hlk p)
  have hBY := hboundary hs hA hb hR hRmax hρ hρ1 hρb hq hqE hglobT hc hcR N S (hlk.trans hkN)
    (htY.1.trans htY.2) Y hY t htY p
  apply littleContour_eq_of_lift_eq
  intro θ
  apply centeredComplexHomeomorph.injective
  change complexTorusPoint (LittleContourSpace.lift γ (Y t p) θ) =
    complexTorusPoint (LittleContourSpace.lift γ (X t (finiteCircularPrefixIndex hlk p)) θ)
  rw [← hBX θ, ← hBY θ]
  rfl

end CircularMaterialTransferProfile
end Euler2D

end
