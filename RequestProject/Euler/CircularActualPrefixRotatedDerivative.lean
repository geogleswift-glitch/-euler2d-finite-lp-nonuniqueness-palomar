module

public import RequestProject.Euler.CircularFinitePrefixPhysicalForcing
public import RequestProject.Euler.CircularAncestorTimeRescaling

/-! The same physical material path on the current cell's clock, with
one fixed entrance gauge. The slow self rate is retained exactly. -/

@[expose] public section

set_option maxHeartbeats 12000000
set_option maxRecDepth 5000

noncomputable section

open Complex Set MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

attribute [local instance 2000] rigidGaugeLittle_group rigidGaugeLittle_space rigidGaugeFamily_tower
attribute [local instance] LittleContourSpace.complexScalarNormedSpace LittleContourSpace.complexScalarTower

theorem hasDerivAt_circularCommonClockRotatedCurve {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
    {A Aj r e τ Ω : ℝ} (hA : A ≠ 0) (hr : r ≠ 0)
    {z : ℝ → Fin 2 → LittleContourSpace γ} (Q : Fin 2 → LittleContourSpace γ)
    (hmem : normalizedPhysicalCurve A r e z τ ∈ circularBanachDomain hγ hγ1)
    (hd : HasDerivAt z
      ((Aj * r) • circularBanachField hγ hγ1
          (r⁻¹ • z (physicalTimeFromNormalized A e τ)) +
        ((Ω : ℂ) * I) • z (physicalTimeFromNormalized A e τ) + Q)
      (physicalTimeFromNormalized A e τ)) :
    HasDerivAt (fun u => rigidRotationGauge (Ω / A) 0 u • normalizedPhysicalCurve A r e z u)
      ((Aj / A) • circularBanachField hγ hγ1
          (rigidRotationGauge (Ω / A) 0 τ • normalizedPhysicalCurve A r e z τ) +
        rigidRotationGauge (Ω / A) 0 τ • ((A * r)⁻¹ • Q)) τ := by
  let F := fun W => (Aj / A) • circularBanachField hγ hγ1 W
  have hc (W : Fin 2 → LittleContourSpace γ) :
      (A * r) • F W = (Aj * r) • circularBanachField hγ hγ1 W := by
    dsimp only [F]
    rw [smul_smul]
    congr 1
    field_simp
  have hcov : F (rigidRotationGauge (Ω / A) 0 τ • normalizedPhysicalCurve A r e z τ) =
      rigidRotationGauge (Ω / A) 0 τ • F (normalizedPhysicalCurve A r e z τ) := by
    dsimp only [F]
    have hfield : circularBanachField hγ hγ1
        (rigidRotationGauge (Ω / A) 0 τ • normalizedPhysicalCurve A r e z τ) =
        rigidRotationGauge (Ω / A) 0 τ • circularBanachField hγ hγ1 (normalizedPhysicalCurve A r e z τ) :=
      circularBanachField_complexValueRotation hγ hγ1 ((τ - 0) * (-(Ω / A))) hmem
    rw [hfield]
    simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul, mul_comm]
  apply hasDerivAt_normalizedPhysicalRotatedCurve hA hr (F := F) (p := fun _ => Q) ?_ hcov
  simpa only [hc] using hd

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem hasDerivAt_actualPrefix_sameGauge_currentClock
    {s A₀ b R ρ : ℝ} (hs : s ≤ 0) (hA : 0 < A₀) (hb : 0 < b)
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
        (radScale R ρ j • LittleContourSpace.lift γ (W i) θ))
    (z : ℝ → Fin 2 → LittleContourSpace γ) (hz : HasDerivAt z D t)
    (hzt : z t = radScale R ρ j • W) (e τ : ℝ)
    (htime : physicalTimeFromNormalized (ampScale A₀ b k) e τ = t) :
    let A := ampScale A₀ b k
    let r := radScale R ρ j
    let Ω := finiteAncestorAngularVelocity A₀ b j
    let y := fun u => rigidRotationGauge (Ω / A) 0 u • normalizedPhysicalCurve A r e z u
    let p := rigidRotationGauge (Ω / A) 0 τ • ((A * r)⁻¹ • Q)
    HasDerivAt y ((b ^ (k - j)) • circularBanachField hγ hγ1 (y τ) + p) τ ∧
      ‖p‖ = ‖Q‖ / (A * r) := by
  have hAk : 0 < ampScale A₀ b k := by unfold ampScale; positivity
  have hrj : 0 < radScale R ρ j := radScale_pos hR hρ j
  have hvector := P.activePhysicalLittleVelocity_eq_self_rigid_prefixForcing
    hs hA.le hb hR hRmax hρ hρ1 N j k hjk hkN S hwf Z t ht W hW hscale
    hstartbox hendbox himages hx D Q hD hQ
  have hnorm : (radScale R ρ j)⁻¹ • z t = W := by
    rw [hzt, inv_smul_smul₀ hrj.ne']
  have hmem : normalizedPhysicalCurve (ampScale A₀ b k) (radScale R ρ j) e z τ ∈
      circularBanachDomain hγ hγ1 := by
    change (radScale R ρ j)⁻¹ • z (physicalTimeFromNormalized (ampScale A₀ b k) e τ) ∈ _
    rw [htime, hnorm]
    exact hW.1
  have hd : HasDerivAt z
      ((ampScale A₀ b j * radScale R ρ j) • circularBanachField hγ hγ1
          ((radScale R ρ j)⁻¹ • z t) +
        ((finiteAncestorAngularVelocity A₀ b j : ℂ) * I) • z t + Q) t := by
    rw [hnorm, hzt]
    rw [hvector] at hz
    exact hz
  have hd' := hasDerivAt_circularCommonClockRotatedCurve hγ hγ1 hAk.ne' hrj.ne' Q hmem
    (by simpa only [htime] using hd)
  refine ⟨?_, norm_normalizedPhysicalRotatedForcing hAk hrj _ τ Q⟩
  simpa only [ampScale_ratio_eq_pow hA.ne' hb.ne' hjk] using hd'

end CircularMaterialTransferProfile
end Euler2D

end
