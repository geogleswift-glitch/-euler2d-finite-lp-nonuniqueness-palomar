module

public import RequestProject.Euler.CircularCanonicalPrefixMaterialBoundary

/-! Literal scalar vorticity of a canonical trajectory of the SAME
original finite Euler system. The enclosed-domain transport theorem
supplies the density identity; it is not an additional hypothesis. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 5500

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

attribute [local instance 2000] rigidGaugeLittle_group rigidGaugeLittle_space rigidGaugeFamily_tower

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_uniform_actualCanonical_prefix_density :
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
      ∀ t ∈ Icc (0 : ℝ) D, ∀ x ∈ torusBox,
        S.transportedScalar (P.finiteInitialPeriodicDensity s A₀ b R ρ N) t x =
          phaseFiniteContourPatchVorticity (finiteCircularInterfaceStrength A₀ b)
            (fun p => (X t p).val) (centeredComplexHomeomorph.symm x) +
              P.finiteInnerClusterSource s A₀ b R ρ N k S t x := by
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
  intro t ht x hx
  exact (hi t ht).2.2.2 x hx

end CircularMaterialTransferProfile
end Euler2D

end
