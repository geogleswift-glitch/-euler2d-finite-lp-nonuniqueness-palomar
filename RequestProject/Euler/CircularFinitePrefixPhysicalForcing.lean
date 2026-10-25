module

public import RequestProject.Euler.CircularFiniteInteractionDecomposition
public import RequestProject.Euler.CircularFiniteActiveLittleVelocity

/-! The complete off-self forcing of an actual active cell, split at
the current prefix. Every term is a literal source of the same S;
the resulting identity is in the original Little Banach space. -/

@[expose] public section

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

noncomputable section

open Complex Set MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

attribute [local instance 2000] rigidGaugeLittle_group rigidGaugeLittle_space rigidGaugeFamily_tower
attribute [local instance] LittleContourSpace.complexScalarNormedSpace LittleContourSpace.complexScalarTower

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

def finitePrefixOffSelfPhysicalField (s A₀ b R ρ : ℝ) (N j k : ℕ) (hjN : j ≤ N)
    {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T) (t : ℝ) (x : ℂ) : ℂ :=
  (∑ l : Fin j, velocityC (P.finiteOuterLabelComplexPerturbation s A₀ b R ρ N
    (⟨l, l.isLt.trans_le (Nat.le_succ_of_le hjN)⟩ : Fin (N + 1)) S t) x) +
  (∑ l ∈ Finset.Ico (j + 1) (k + 1), velocityC (boxedComplexDensity
    (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N l) t)) x) +
  velocityC (P.finiteInnerClusterComplexSource s A₀ b R ρ N k S t) x +
  (∑ l ∈ Finset.range (k + 1), actualTorusCorrectionVelocity (boxedComplexDensity
    (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N l) t)) x) +
  actualTorusCorrectionVelocity (P.finiteInnerClusterComplexSource s A₀ b R ρ N k S t) x

theorem physicalFiniteVelocity_eq_self_rigid_prefixForcing
    {s A₀ b R ρ : ℝ} (hs : s ≤ 0) (hA : 0 ≤ A₀) (hb : 0 < b)
    (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (N j k : ℕ) (hjk : j ≤ k) (hkN : k ≤ N)
    {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)
    (hwf : P.finiteInitialPeriodicDensity s A₀ b R ρ N =ᵐ[μT] (f : R2 → ℝ))
    (Z : FiniteCircularIndex N → ContourC1Space γ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T)
    (W : Fin 2 → LittleContourSpace γ) (hW : W ∈ circularQuarterPhaseDomain hγ hγ1)
    (hscale : ∀ i, Z (⟨j, Nat.lt_succ_of_le (hjk.trans hkN)⟩, i) = radScale R ρ j • (W i).val)
    (hstartbox : ∀ i, complexTorusPoint '' contourRadialFill (ContourC1Space.lift γ
      (finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N
        (⟨j, Nat.lt_succ_of_le (hjk.trans hkN)⟩, i)).val) ⊆ torusBox)
    (hendbox : ∀ i, complexTorusPoint '' contourRadialFill (ContourC1Space.lift γ
      (Z (⟨j, Nat.lt_succ_of_le (hjk.trans hkN)⟩, i))) ⊆ torusBox)
    (himages : ∀ i, S.forward t '' (complexTorusPoint '' contourRadialFill
      (ContourC1Space.lift γ (finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N
        (⟨j, Nat.lt_succ_of_le (hjk.trans hkN)⟩, i)).val)) =
      complexTorusPoint '' contourRadialFill (ContourC1Space.lift γ
        (Z (⟨j, Nat.lt_succ_of_le (hjk.trans hkN)⟩, i))))
    (i : Fin 2) (θ : ℝ)
    (hx : ∀ l : Fin j, ‖radScale R ρ j • LittleContourSpace.lift γ (W i) θ‖ ≤ cellA * radScale R ρ l) :
    let x := radScale R ρ j • LittleContourSpace.lift γ (W i) θ
    velocityC (S.physicalComplexSource (P.finiteInitialPeriodicDensity s A₀ b R ρ N) t) x +
      planeComplexEquiv (S.correctionLabelField t (complexTorusPoint x)) =
      (ampScale A₀ b j * radScale R ρ j) • LittleContourSpace.lift γ (circularBanachField hγ hγ1 W i) θ +
      (finiteAncestorAngularVelocity A₀ b j : ℂ) * I * x +
      P.finitePrefixOffSelfPhysicalField s A₀ b R ρ N j k (hjk.trans hkN) S t x := by
  dsimp only
  rw [P.velocityC_physicalFiniteDensity_eq_activeSelf_rigid_residual_cluster
    hs hA hb hR hRmax hρ hρ1 N j (hjk.trans hkN) S Z t ht W hW hscale
      hstartbox hendbox himages i θ hx,
    P.velocityC_finiteInnerCluster_eq_middle_add_deep hs hA hb hR hRmax hρ hρ1 N j k hjk hkN,
    P.correctionLabelField_finiteDensity_eq_prefix_add_deep hs hA hb hR hRmax hρ hρ1 N k hkN S hwf t ht]
  unfold finitePrefixOffSelfPhysicalField
  abel

theorem activePhysicalLittleVelocity_eq_self_rigid_prefixForcing
    {s A₀ b R ρ : ℝ} (hs : s ≤ 0) (hA : 0 ≤ A₀) (hb : 0 < b)
    (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (N j k : ℕ) (hjk : j ≤ k) (hkN : k ≤ N)
    {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)
    (hwf : P.finiteInitialPeriodicDensity s A₀ b R ρ N =ᵐ[μT] (f : R2 → ℝ))
    (Z : FiniteCircularIndex N → ContourC1Space γ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T)
    (W : Fin 2 → LittleContourSpace γ) (hW : W ∈ circularQuarterPhaseDomain hγ hγ1)
    (hscale : ∀ i, Z (⟨j, Nat.lt_succ_of_le (hjk.trans hkN)⟩, i) = radScale R ρ j • (W i).val)
    (hstartbox : ∀ i, complexTorusPoint '' contourRadialFill (ContourC1Space.lift γ
      (finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N
        (⟨j, Nat.lt_succ_of_le (hjk.trans hkN)⟩, i)).val) ⊆ torusBox)
    (hendbox : ∀ i, complexTorusPoint '' contourRadialFill (ContourC1Space.lift γ
      (Z (⟨j, Nat.lt_succ_of_le (hjk.trans hkN)⟩, i))) ⊆ torusBox)
    (himages : ∀ i, S.forward t '' (complexTorusPoint '' contourRadialFill
      (ContourC1Space.lift γ (finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N
        (⟨j, Nat.lt_succ_of_le (hjk.trans hkN)⟩, i)).val)) =
      complexTorusPoint '' contourRadialFill (ContourC1Space.lift γ
        (Z (⟨j, Nat.lt_succ_of_le (hjk.trans hkN)⟩, i))))
    (hx : ∀ i θ, ∀ l : Fin j, ‖radScale R ρ j • LittleContourSpace.lift γ (W i) θ‖ ≤ cellA * radScale R ρ l)
    (D Q : Fin 2 → LittleContourSpace γ)
    (hD : ∀ i θ, LittleContourSpace.lift γ (D i) θ =
      velocityC (S.physicalComplexSource (P.finiteInitialPeriodicDensity s A₀ b R ρ N) t)
        (radScale R ρ j • LittleContourSpace.lift γ (W i) θ) +
      planeComplexEquiv (S.correctionLabelField t
        (complexTorusPoint (radScale R ρ j • LittleContourSpace.lift γ (W i) θ))))
    (hQ : ∀ i θ, LittleContourSpace.lift γ (Q i) θ =
      P.finitePrefixOffSelfPhysicalField s A₀ b R ρ N j k (hjk.trans hkN) S t
        (radScale R ρ j • LittleContourSpace.lift γ (W i) θ)) :
    D = (ampScale A₀ b j * radScale R ρ j) • circularBanachField hγ hγ1 W +
      (((finiteAncestorAngularVelocity A₀ b j : ℝ) : ℂ) * I) • (radScale R ρ j • W) + Q := by
  funext i
  apply littleContour_eq_of_lift_eq
  intro θ
  change LittleContourSpace.lift γ (D i) θ =
    (ampScale A₀ b j * radScale R ρ j) • LittleContourSpace.lift γ (circularBanachField hγ hγ1 W i) θ +
      ((finiteAncestorAngularVelocity A₀ b j : ℂ) * I) *
        (radScale R ρ j • LittleContourSpace.lift γ (W i) θ) + LittleContourSpace.lift γ (Q i) θ
  rw [hD, hQ]
  exact P.physicalFiniteVelocity_eq_self_rigid_prefixForcing hs hA hb hR hRmax hρ hρ1
    N j k hjk hkN S hwf Z t ht W hW hscale hstartbox hendbox himages i θ (hx i θ)

end CircularMaterialTransferProfile
end Euler2D

end
