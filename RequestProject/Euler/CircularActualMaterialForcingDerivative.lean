module

public import RequestProject.Euler.CircularMaterialForcingNormalization
public import RequestProject.Euler.CircularCanonicalAbsoluteDynamics

/-! Bind the normalized source on the actual unshifted current
contour to the original SAME canonical trajectory's physical
derivative. The raw forcing is reconstructed, not assumed to agree
with a separately selected derivative source. -/

@[expose] public section

set_option maxHeartbeats 20000000
set_option maxRecDepth 7500

noncomputable section

open Complex Set MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

attribute [local instance 2000] rigidGaugeLittle_group rigidGaugeLittle_space rigidGaugeFamily_tower
attribute [local instance] LittleContourSpace.complexScalarNormedSpace LittleContourSpace.complexScalarTower

def canonicalPrefixMaterialCurrentCell {γ : ℝ≥0} (A₀ b R ρ : ℝ) (k : ℕ)
    (X : ℝ → FiniteCircularIndex k → LittleContourSpace γ) (σ : ℝ) : Fin 2 → LittleContourSpace γ :=
  contourParameterShiftFamilyCLM γ (fun i => -(circularContourAngularVelocities i * σ))
    (canonicalPrefixAbsoluteCell A₀ b R ρ k 0 X σ (Fin.last k))

theorem materialUnshift_circularMaterialContours {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (σ : ℝ) :
    contourParameterShiftFamilyCLM γ (fun i => -(circularContourAngularVelocities i * σ))
      (littleCircularMaterialContours hγ hγ1 σ) = littleCircularReference hγ hγ1 := by
  rw [littleCircularMaterialContours_eq_shift, contourParameterShiftFamilyCLM_add]
  have hz : (fun i => -(circularContourAngularVelocities i * σ)) +
      (fun i => circularContourAngularVelocities i * σ) = 0 := by funext i; simp
  rw [hz, contourParameterShiftFamilyCLM_zero]

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem actualCanonicalPrefix_material_forcing_hasDerivAt
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
    (σ : ℝ) (htime : physicalTimeFromNormalized (ampScale A₀ b k) 0 σ = t)
    (Q : Fin 2 → LittleContourSpace γ)
    (hQ : ∀ i u, LittleContourSpace.lift γ (Q i) u =
      Complex.exp (-(((t * finiteAncestorAngularVelocity A₀ b k : ℝ) : ℂ) * I)) *
        ((ampScale A₀ b k * radScale R ρ k)⁻¹ •
          P.finitePrefixOffSelfPhysicalField s A₀ b R ρ N k k hkN S t
            (radScale R ρ k • (Complex.exp (((t * finiteAncestorAngularVelocity A₀ b k : ℝ) : ℂ) * I) *
              LittleContourSpace.lift γ (canonicalPrefixMaterialCurrentCell A₀ b R ρ k X σ i) u)))) :
    ∃ p : Fin 2 → LittleContourSpace γ,
      HasDerivAt (fun u => canonicalPrefixAbsoluteCell A₀ b R ρ k 0 X u (Fin.last k))
        (circularBanachField hγ hγ1 (canonicalPrefixAbsoluteCell A₀ b R ρ k 0 X σ (Fin.last k)) + p) σ ∧
      contourParameterShiftFamilyCLM γ (fun i => -(circularContourAngularVelocities i * σ)) p = Q := by
  let A := ampScale A₀ b k
  let r := radScale R ρ k
  let Ω := finiteAncestorAngularVelocity A₀ b k
  let θ := t * Ω
  let β : Fin 2 → ℝ := fun i => circularContourAngularVelocities i * σ
  let y := fun u => canonicalPrefixAbsoluteCell A₀ b R ρ k 0 X u (Fin.last k)
  let Z := canonicalPrefixMaterialCurrentCell A₀ b R ρ k X σ
  let raw : Fin 2 → LittleContourSpace γ := fun i => X t (Fin.last k, i)
  have hApos : 0 < A := div_pos hA (pow_pos hb k)
  have hr : 0 < r := radScale_pos hR hρ k
  have hshift : contourParameterShiftFamilyCLM γ β Z = y σ := by
    change contourParameterShiftFamilyCLM γ β (contourParameterShiftFamilyCLM γ (-β) (y σ)) = y σ
    rw [contourParameterShiftFamilyCLM_add, add_neg_cancel, contourParameterShiftFamilyCLM_zero]
  have hraw : r • (Complex.exp ((θ : ℂ) * I) • contourParameterShiftFamilyCLM γ β Z) = raw := by
    rw [hshift]
    have hh := canonicalPrefixAbsoluteCell_raw (A₀ := A₀) (b := b) hR hρ k 0 σ X (Fin.last k)
    rw [htime] at hh
    simpa only [Fin.val_last] using hh
  let Qraw := materialPhysicalForcing A r θ β Q
  have hQraw : ∀ i u, LittleContourSpace.lift γ (Qraw i) u =
      P.finitePrefixOffSelfPhysicalField s A₀ b R ρ N k k hkN S t
        (LittleContourSpace.lift γ (X t (Fin.last k, i)) u) :=
    materialPhysicalForcing_lift hApos.ne' hr.ne' θ β raw Z Q
      (P.finitePrefixOffSelfPhysicalField s A₀ b R ρ N k k hkN S t) hraw hQ
  let p := rigidRotationGauge Ω 0 t • ((A * r)⁻¹ • Qraw)
  have hd := (P.actualCanonicalPrefix_absolute_hasDerivAt hs hA hb hR hRmax hρ hρ1 hρcore hkN
    S hglobT hwf X hX t ht G hG (Fin.last k) Qraw hQraw 0 σ htime).1
  have hgauge : rigidRotationGauge Ω 0 t = Complex.exp (-((θ : ℂ) * I)) := by
    unfold rigidRotationGauge
    congr 1
    dsimp only [θ]
    push_cast
    ring
  refine ⟨p, ?_, ?_⟩
  · simpa only [Fin.val_last, Nat.sub_self, pow_zero, one_smul] using hd
  · change contourParameterShiftFamilyCLM γ (-β) p = Q
    dsimp only [p]
    rw [hgauge]
    exact materialPhysicalForcing_unshift_normalized hApos.ne' hr.ne' θ β Q

end CircularMaterialTransferProfile
end Euler2D

end
