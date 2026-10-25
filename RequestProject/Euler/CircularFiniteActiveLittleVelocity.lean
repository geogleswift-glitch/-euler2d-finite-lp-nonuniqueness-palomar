module

public import RequestProject.Euler.CircularFiniteActiveVelocityDecomposition
public import RequestProject.Euler.CircularRigidRotationGauge

/-! The actual same-S physical velocity decomposition is an identity
in the original Little Banach space. Its three forcing terms are the
real ancestor residual, actual inner cluster, and original torus
correction, each identified by its literal contour lift. -/

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

theorem activePhysicalLittleVelocity_eq_self_rigid_actualForcing
    {s A₀ b R ρ : ℝ} (hs : s ≤ 0) (hA : 0 ≤ A₀) (hb : 0 < b)
    (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (N k : ℕ) (hk : k ≤ N) {f : Lp ℝ 2 μT} {T : ℝ}
    (S : BoundedEulerParticleSystem f T)
    (Z : FiniteCircularIndex N → ContourC1Space γ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T)
    (W : Fin 2 → LittleContourSpace γ) (hW : W ∈ circularQuarterPhaseDomain hγ hγ1)
    (hscale : ∀ i, Z (⟨k, Nat.lt_succ_of_le hk⟩, i) = radScale R ρ k • (W i).val)
    (hstartbox : ∀ i, complexTorusPoint '' contourRadialFill (ContourC1Space.lift γ
      (finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N
        (⟨k, Nat.lt_succ_of_le hk⟩, i)).val) ⊆ torusBox)
    (hendbox : ∀ i, complexTorusPoint '' contourRadialFill
      (ContourC1Space.lift γ (Z (⟨k, Nat.lt_succ_of_le hk⟩, i))) ⊆ torusBox)
    (himages : ∀ i, S.forward t '' (complexTorusPoint '' contourRadialFill
      (ContourC1Space.lift γ (finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N
        (⟨k, Nat.lt_succ_of_le hk⟩, i)).val)) =
      complexTorusPoint '' contourRadialFill
        (ContourC1Space.lift γ (Z (⟨k, Nat.lt_succ_of_le hk⟩, i))))
    (hx : ∀ i θ, ∀ j : Fin k, ‖radScale R ρ k • LittleContourSpace.lift γ (W i) θ‖ ≤
      cellA * radScale R ρ j)
    (D Qa Qi Qt : Fin 2 → LittleContourSpace γ)
    (hD : ∀ i θ, LittleContourSpace.lift γ (D i) θ =
      velocityC (S.physicalComplexSource (P.finiteInitialPeriodicDensity s A₀ b R ρ N) t)
        (radScale R ρ k • LittleContourSpace.lift γ (W i) θ) +
      planeComplexEquiv (S.correctionLabelField t
        (complexTorusPoint (radScale R ρ k • LittleContourSpace.lift γ (W i) θ))))
    (hQa : ∀ i θ, LittleContourSpace.lift γ (Qa i) θ =
      ∑ j : Fin k, velocityC (P.finiteOuterLabelComplexPerturbation s A₀ b R ρ N
        (⟨j, j.isLt.trans_le (Nat.le_succ_of_le hk)⟩ : Fin (N + 1)) S t)
          (radScale R ρ k • LittleContourSpace.lift γ (W i) θ))
    (hQi : ∀ i θ, LittleContourSpace.lift γ (Qi i) θ =
      velocityC (P.finiteInnerClusterComplexSource s A₀ b R ρ N k S t)
        (radScale R ρ k • LittleContourSpace.lift γ (W i) θ))
    (hQt : ∀ i θ, LittleContourSpace.lift γ (Qt i) θ =
      planeComplexEquiv (S.correctionLabelField t
        (complexTorusPoint (radScale R ρ k • LittleContourSpace.lift γ (W i) θ)))) :
    D = (ampScale A₀ b k * radScale R ρ k) • circularBanachField hγ hγ1 W +
      (((finiteAncestorAngularVelocity A₀ b k : ℝ) : ℂ) * I) • (radScale R ρ k • W) +
      (Qa + Qi + Qt) := by
  funext i
  apply Subtype.ext
  apply ContourC1Space.ext
  intro x
  obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective x
  change LittleContourSpace.lift γ (D i) θ =
    (ampScale A₀ b k * radScale R ρ k) •
      LittleContourSpace.lift γ (circularBanachField hγ hγ1 W i) θ +
      ((finiteAncestorAngularVelocity A₀ b k : ℂ) * I) *
        (radScale R ρ k • LittleContourSpace.lift γ (W i) θ) +
      (LittleContourSpace.lift γ (Qa i) θ + LittleContourSpace.lift γ (Qi i) θ +
        LittleContourSpace.lift γ (Qt i) θ)
  rw [hD, hQa, hQi, hQt,
    P.velocityC_physicalFiniteDensity_eq_activeSelf_rigid_residual_cluster
      hs hA hb hR hRmax hρ hρ1 N k hk S Z t ht W hW hscale hstartbox hendbox himages i θ (hx i θ)]
  abel

end CircularMaterialTransferProfile
end Euler2D

end
