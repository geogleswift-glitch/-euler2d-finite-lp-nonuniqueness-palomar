module

public import RequestProject.Euler.CircularCanonicalPrefixRotatedDynamics
public import RequestProject.Euler.CircularCanonicalAbsoluteGauge

/-! The original canonical X satisfies the isolated circular equation
in the agreed absolute gauge. Only one constant entrance rotation is
applied to the already proved stage dynamics. -/

@[expose] public section

set_option maxHeartbeats 14000000
set_option maxRecDepth 6000

noncomputable section

open Complex Set MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

attribute [local instance 2000] rigidGaugeLittle_group rigidGaugeLittle_space rigidGaugeFamily_tower
attribute [local instance] LittleContourSpace.complexScalarNormedSpace LittleContourSpace.complexScalarTower
attribute [local irreducible] circularBanachField circularBanachDomain

theorem hasDerivAt_circular_constantValueRotation {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (φ a τ : ℝ)
    {y : ℝ → Fin 2 → LittleContourSpace γ} {p : Fin 2 → LittleContourSpace γ}
    (hm : y τ ∈ circularBanachDomain hγ hγ1)
    (hd : HasDerivAt y (a • circularBanachField hγ hγ1 (y τ) + p) τ) :
    HasDerivAt (fun u => exp ((φ : ℂ) * I) • y u)
      (a • circularBanachField hγ hγ1 (exp ((φ : ℂ) * I) • y τ) + exp ((φ : ℂ) * I) • p) τ := by
  have hh := hd.const_smul (exp ((φ : ℂ) * I))
  have hvalue : exp ((φ : ℂ) * I) • (a • circularBanachField hγ hγ1 (y τ) + p) =
      a • circularBanachField hγ hγ1 (exp ((φ : ℂ) * I) • y τ) + exp ((φ : ℂ) * I) • p := by
    rw [circularBanachField_complexValueRotation hγ hγ1 φ hm, smul_add]
    simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
    congr 1
    congr 1
    ring
  rwa [hvalue] at hh

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)
theorem actualCanonicalPrefix_absolute_hasDerivAt
    {s A₀ b R ρ c δ a Hglob D : ℝ} (hs : s ≤ 0) (hA : 0 < A₀) (hb : 0 < b)
    (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hρcore : (5 / 4 : ℝ) * ρ ≤ cellA)
    {N k : ℕ} (hkN : k ≤ N) {f : Lp ℝ 2 μT} {T : ℝ}
    (S : BoundedEulerParticleSystem f T) (hglobT : Hglob ≤ T)
    (hwf : P.finiteInitialPeriodicDensity s A₀ b R ρ N =ᵐ[μT] (f : R2 → ℝ))
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
    (j : Fin (k + 1)) (Q : Fin 2 → LittleContourSpace γ)
    (hQ : ∀ i θ, LittleContourSpace.lift γ (Q i) θ =
      P.finitePrefixOffSelfPhysicalField s A₀ b R ρ N j k ((Nat.le_of_lt_succ j.isLt).trans hkN) S t
        (LittleContourSpace.lift γ (X t (j, i)) θ))
    (aTime τ : ℝ) (htime : physicalTimeFromNormalized (ampScale A₀ b k) aTime τ = t) :
    let A := ampScale A₀ b k
    let r := radScale R ρ j
    let Ω := finiteAncestorAngularVelocity A₀ b j
    let y := fun u => canonicalPrefixAbsoluteCell A₀ b R ρ k aTime X u j
    let p := rigidRotationGauge Ω 0 t • ((A * r)⁻¹ • Q)
    HasDerivAt y ((b ^ (k - (j : ℕ))) • circularBanachField hγ hγ1 (y τ) + p) τ ∧
      ‖p‖ = ‖Q‖ / (A * r) := by
  obtain ⟨hyd, hpnorm⟩ := P.actualCanonicalPrefix_sameGauge_hasDerivAt hs hA hb hR hRmax hρ hρ1 hρcore
    hkN S hglobT hwf X hX t ht G hG j Q hQ aTime τ htime
  let Ω := finiteAncestorAngularVelocity A₀ b j
  let A := ampScale A₀ b k
  let r := radScale R ρ j
  let φ := -Ω * aTime
  let y := fun u => canonicalPrefixRotatedCell A₀ b R ρ k aTime X u j
  let p := rigidRotationGauge (Ω / A) 0 τ • ((A * r)⁻¹ • Q)
  have hmem := hX.mem t ht
  have hraw : normalizedPhysicalCurve A r aTime (fun u i => X u (j, i)) τ ∈
      circularBanachDomain hγ hγ1 := by
    change (fun i => r⁻¹ • X (physicalTimeFromNormalized A aTime τ) (j, i)) ∈ _
    rw [htime]
    exact (normalizedFiniteCircularCell_mem_quarterPhaseDomain hγ hγ1 hR hρ (X t)
      hmem.2.1 hmem.2.2.2.1 j).1
  have hym : y τ ∈ circularBanachDomain hγ hγ1 :=
    circularNormalizedPhysicalRotatedCurve_mem hγ hγ1 A r aTime τ Ω hraw
  have hy := hasDerivAt_circular_constantValueRotation hγ hγ1 φ (b ^ (k - (j : ℕ))) τ hym hyd
  have hfun : (fun u => exp ((φ : ℂ) * I) • y u) =
      (fun u => canonicalPrefixAbsoluteCell A₀ b R ρ k aTime X u j) := by
    funext u
    exact (canonicalPrefixAbsoluteCell_eq_fixedEntranceRotation A₀ b R ρ k aTime X u j).symm
  have hpoint : exp ((φ : ℂ) * I) • y τ = canonicalPrefixAbsoluteCell A₀ b R ρ k aTime X τ j :=
    congrFun hfun τ
  have hp : exp ((φ : ℂ) * I) • p = rigidRotationGauge Ω 0 t • ((A * r)⁻¹ • Q) := by
    dsimp only [p]
    rw [smul_smul, ← absoluteGauge_eq_fixedEntranceRotation, htime]
  rw [hfun, hpoint, hp] at hy
  refine ⟨hy, ?_⟩
  rw [← hp, norm_smul, norm_exp_ofReal_mul_I, one_mul]
  exact hpnorm

end CircularMaterialTransferProfile
end Euler2D

end
