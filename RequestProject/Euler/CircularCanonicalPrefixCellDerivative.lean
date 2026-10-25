module

public import RequestProject.Euler.CircularCanonicalPrefixPhysicalDerivative

/-! The actual canonical X itself supplies every cell's Banach
derivative and its literal full physical velocity on the same S. -/

@[expose] public section

set_option maxHeartbeats 12000000
set_option maxRecDepth 6000

noncomputable section

open Complex Set MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

attribute [local instance 2000] rigidGaugeLittle_group rigidGaugeLittle_space rigidGaugeFamily_tower
attribute [local instance] LittleContourSpace.complexScalarNormedSpace LittleContourSpace.complexScalarTower

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem actualCanonicalPrefix_cell_hasDerivAt_fullPhysical
    {s A₀ b R ρ c δ a Hglob D : ℝ} (hs : s ≤ 0) (hA : 0 ≤ A₀) (hb : 0 < b)
    (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    {N k : ℕ} (hkN : k ≤ N) {f : Lp ℝ 2 μT} {T : ℝ}
    (S : BoundedEulerParticleSystem f T) (hglobT : Hglob ≤ T)
    (X : ℝ → FiniteCircularIndex k → LittleContourSpace γ)
    (hX : IsBanachTimeDomainTrajectoryOn
      (S.actualPartialPhaseField (P.finiteInnerInitialLabel s A₀ b R ρ N k) hγ hγ1
        (finiteCircularReferenceC1 hγ hγ1 R ρ) (finiteCircularInterfaceRadius R ρ)
        (finiteCircularInterfaceRadius_pos hR hρ) (lift_finiteCircularReferenceC1 hγ hγ1 R ρ)
        (finiteCircularInterfaceStrength A₀ b))
      (S.actualPartialPhaseDomain (P.finiteInnerInitialLabel s A₀ b R ρ N k)
        (finiteCircularReferenceC1 hγ hγ1 R ρ) (finiteCircularInterfaceRadius R ρ) a Hglob)
      (fun p => finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N (finiteCircularPrefixIndex hkN p)) D X)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) D)
    (G : P.FiniteOuterMaterialTube s R ρ N k S t c δ)
    (hG : ∀ p, G.contours (finiteCircularPrefixIndex hkN p) = (X t p).val)
    (j : Fin (k + 1)) :
    let F := S.actualPartialPhaseField (P.finiteInnerInitialLabel s A₀ b R ρ N k) hγ hγ1
      (finiteCircularReferenceC1 hγ hγ1 R ρ) (finiteCircularInterfaceRadius R ρ)
      (finiteCircularInterfaceRadius_pos hR hρ) (lift_finiteCircularReferenceC1 hγ hγ1 R ρ)
      (finiteCircularInterfaceStrength A₀ b)
    let z := fun u i => X u (j, i)
    let Dcell := fun i => F t (X t) (j, i)
    HasDerivAt z Dcell t ∧ ∀ i θ, LittleContourSpace.lift γ (Dcell i) θ =
      velocityC (S.physicalComplexSource (P.finiteInitialPeriodicDensity s A₀ b R ρ N) t)
        (LittleContourSpace.lift γ (X t (j, i)) θ) +
      planeComplexEquiv (S.correctionLabelField t (complexTorusPoint (LittleContourSpace.lift γ (X t (j, i)) θ))) := by
  dsimp only
  let J : (FiniteCircularIndex k → LittleContourSpace γ) →L[ℝ] (Fin 2 → LittleContourSpace γ) :=
    ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj (j, i))
  refine ⟨J.hasFDerivAt.comp_hasDerivAt t (hX.hasDerivAt t ht), ?_⟩
  have hmem := hX.mem t ht
  obtain ⟨β, hβ⟩ := hmem.2.2.2.1
  have htT : t ∈ Icc (0 : ℝ) T := ⟨ht.1, hmem.1.2.trans hglobT⟩
  intro i θ
  exact P.lift_actualPrefix_canonicalField_eq_fullPhysicalVelocity hs hA hb hR hRmax hρ hρ1
    hkN S t htT G (X t) hG hmem.2.1 β (fun p => (hβ p).le) hmem.2.2.2.2 (j, i) θ

end CircularMaterialTransferProfile
end Euler2D

end
