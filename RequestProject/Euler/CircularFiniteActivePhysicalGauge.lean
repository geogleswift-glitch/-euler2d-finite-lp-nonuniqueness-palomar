module

public import RequestProject.Euler.CircularFiniteActiveLittleVelocity
public import RequestProject.Euler.CircularPhysicalRotatingFrame

/-! The original same-S active material trajectory really satisfies
the original isolated circular equation after its physical time and
length normalization and exact ancestor rigid gauge. The forcing is
the sum of its three actual Little lifts. -/

@[expose] public section

set_option maxHeartbeats 12000000
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

theorem hasDerivAt_activePhysicalNormalizedRotatedCurve
    {s A₀ b R ρ : ℝ} (hs : s ≤ 0) (hA : 0 < A₀) (hb : 0 < b)
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
        (complexTorusPoint (radScale R ρ k • LittleContourSpace.lift γ (W i) θ))))
    (z : ℝ → Fin 2 → LittleContourSpace γ) (hz : HasDerivAt z D t)
    (hzt : z t = radScale R ρ k • W) (e τ : ℝ)
    (htime : physicalTimeFromNormalized (ampScale A₀ b k) e τ = t) :
    let A := ampScale A₀ b k
    let r := radScale R ρ k
    let Ω := finiteAncestorAngularVelocity A₀ b k
    let y := fun u => rigidRotationGauge (Ω / A) 0 u • normalizedPhysicalCurve A r e z u
    let p := rigidRotationGauge (Ω / A) 0 τ • ((A * r)⁻¹ • (Qa + Qi + Qt))
    HasDerivAt y (circularBanachField hγ hγ1 (y τ) + p) τ ∧
      ‖p‖ ≤ (‖Qa‖ + ‖Qi‖ + ‖Qt‖) / (A * r) := by
  have hAk : 0 < ampScale A₀ b k := by unfold ampScale; positivity
  have hrk : 0 < radScale R ρ k := radScale_pos hR hρ k
  have hvector := P.activePhysicalLittleVelocity_eq_self_rigid_actualForcing
    hs hA.le hb hR hRmax hρ hρ1 N k hk S Z t ht W hW hscale
    hstartbox hendbox himages hx D Qa Qi Qt hD hQa hQi hQt
  have hnorm : (radScale R ρ k)⁻¹ • z t = W := by
    rw [hzt, inv_smul_smul₀ hrk.ne']
  have hmem : normalizedPhysicalCurve (ampScale A₀ b k) (radScale R ρ k) e z τ ∈
      circularBanachDomain hγ hγ1 := by
    change (radScale R ρ k)⁻¹ • z (physicalTimeFromNormalized (ampScale A₀ b k) e τ) ∈ _
    rw [htime, hnorm]
    exact hW.1
  have hd : HasDerivAt z
      ((ampScale A₀ b k * radScale R ρ k) • circularBanachField hγ hγ1
          ((radScale R ρ k)⁻¹ • z t) +
        ((finiteAncestorAngularVelocity A₀ b k : ℂ) * I) • z t + (Qa + Qi + Qt)) t := by
    rw [hnorm, hzt]
    rw [hvector] at hz
    exact hz
  have hd' : HasDerivAt z
      ((ampScale A₀ b k * radScale R ρ k) • circularBanachField hγ hγ1
          ((radScale R ρ k)⁻¹ • z (physicalTimeFromNormalized (ampScale A₀ b k) e τ)) +
        ((finiteAncestorAngularVelocity A₀ b k : ℂ) * I) •
          z (physicalTimeFromNormalized (ampScale A₀ b k) e τ) + (Qa + Qi + Qt))
      (physicalTimeFromNormalized (ampScale A₀ b k) e τ) := by
    simpa only [htime] using hd
  exact ⟨hasDerivAt_circularNormalizedPhysicalRotatedCurve hγ hγ1 hAk.ne' hrk.ne'
    (p := fun _ => Qa + Qi + Qt) hmem hd',
    norm_circularNormalizedThreeForcing_le hAk hrk _ τ Qa Qi Qt⟩

end CircularMaterialTransferProfile
end Euler2D

end
