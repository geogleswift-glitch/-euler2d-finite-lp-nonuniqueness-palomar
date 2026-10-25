module

public import RequestProject.Euler.CircularActualMaterialForcingDerivative
public import RequestProject.Euler.CircularNonlinearGrowingEquation
public import RequestProject.Euler.CircularCanonicalPrefixMaterialBoundary

/-! The actual growing coordinate of the SAME original canonical
Euler prefix satisfies the nonlinear scalar equation with the literal
normalized physical source. The strong derivative is derived from
the original Euler particle/contour dynamics, not supplied as input. -/

@[expose] public section

set_option maxHeartbeats 24000000
set_option maxRecDepth 8000

noncomputable section

open Complex Set MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

attribute [local instance 2000] rigidGaugeLittle_group rigidGaugeLittle_space rigidGaugeFamily_tower
attribute [local instance] LittleContourSpace.complexScalarNormedSpace LittleContourSpace.complexScalarTower

def canonicalPrefixMaterialGrowingCoordinate {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (A₀ b R ρ : ℝ) (k : ℕ)
    (X : ℝ → FiniteCircularIndex k → LittleContourSpace γ) (σ : ℝ) : ℂ :=
  circularUnstableCoordinateCLM γ
    (canonicalPrefixMaterialCurrentCell A₀ b R ρ k X σ - littleCircularReference hγ hγ1)

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_uniform_actualCanonical_material_growing_equation :
    ∃ C > 0, ∃ r > 0,
      ∀ {s A₀ b R ρ c δ a Hglob D : ℝ},
      ∀ (hs : s ≤ 0) (hA : 0 < A₀) (hb : 0 < b)
        (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1),
      (5 / 4 : ℝ) * ρ ≤ cellA →
      ∀ {N k : ℕ} (hkN : k ≤ N) {f : Lp ℝ 2 μT} {T : ℝ},
      ∀ S : BoundedEulerParticleSystem f T, Hglob ≤ T →
      P.finiteInitialPeriodicDensity s A₀ b R ρ N =ᵐ[μT] (f : R2 → ℝ) →
      ∀ X : ℝ → FiniteCircularIndex k → LittleContourSpace γ,
      P.ActualCanonicalPrefixTrajectory s A₀ b R ρ a Hglob hR hρ hkN S D X →
      ∀ t ∈ Icc (0 : ℝ) D,
      ∀ G : P.FiniteOuterMaterialTube s R ρ N k S t c δ,
      (∀ p, G.contours (finiteCircularPrefixIndex hkN p) = (X t p).val) →
      ∀ σ : ℝ, physicalTimeFromNormalized (ampScale A₀ b k) 0 σ = t →
      ‖canonicalPrefixAbsoluteCell A₀ b R ρ k 0 X σ (Fin.last k) -
        littleCircularMaterialContours hγ hγ1 σ‖ ≤ r →
      ∀ Q : Fin 2 → LittleContourSpace γ,
      (∀ i u, LittleContourSpace.lift γ (Q i) u =
        Complex.exp (-(((t * finiteAncestorAngularVelocity A₀ b k : ℝ) : ℂ) * I)) *
          ((ampScale A₀ b k * radScale R ρ k)⁻¹ •
            P.finitePrefixOffSelfPhysicalField s A₀ b R ρ N k k hkN S t
              (radScale R ρ k • (Complex.exp (((t * finiteAncestorAngularVelocity A₀ b k : ℝ) : ℂ) * I) *
                LittleContourSpace.lift γ (canonicalPrefixMaterialCurrentCell A₀ b R ρ k X σ i) u)))) →
      ∃ E : ℂ,
        ‖E‖ ≤ C * ‖canonicalPrefixAbsoluteCell A₀ b R ρ k 0 X σ (Fin.last k) -
          littleCircularMaterialContours hγ hγ1 σ‖ ^ 2 ∧
        HasDerivAt (canonicalPrefixMaterialGrowingCoordinate hγ hγ1 A₀ b R ρ k X)
          (lamStar * canonicalPrefixMaterialGrowingCoordinate hγ hγ1 A₀ b R ρ k X σ +
            circularUnstableCoordinateCLM γ Q + E) σ := by
  obtain ⟨Cn, hCn, r, hr, hscalar⟩ := exists_circularNonlinear_growing_equation hγ hγ1
  let C := ‖circularUnstableCoordinateCLM γ‖ * Cn + 1
  have hC : 0 < C := by dsimp only [C]; positivity
  have hCoeff : ‖circularUnstableCoordinateCLM γ‖ * Cn ≤ C := by dsimp only [C]; linarith
  refine ⟨C, hC, r, hr, ?_⟩
  intro s A₀ b R ρ c δ a Hglob D hs hA hb hR hRmax hρ hρ1 hρcore N k hkN f T S hglobT hwf
    X hX t ht G hG σ htime hsmall Q hQ
  let y := fun u => canonicalPrefixAbsoluteCell A₀ b R ρ k 0 X u (Fin.last k)
  obtain ⟨p, hy, hp⟩ := P.actualCanonicalPrefix_material_forcing_hasDerivAt hs hA hb hR hRmax hρ hρ1
    hρcore hkN S hglobT hwf X hX t ht G hG σ htime Q hQ
  have hy1 : HasDerivAt y ((1 : ℝ) • circularBanachField hγ hγ1 (y σ) + p) σ := by
    simpa only [one_smul] using hy
  obtain ⟨E, hE, hd⟩ := hscalar 1 y p σ hy1 (by simpa only [one_mul] using hsmall)
  simp only [Complex.ofReal_one, one_mul, neg_one_mul, neg_mul, abs_one] at hd hE
  have hw (u : ℝ) : circularUnstableCoordinateCLM γ
      (contourParameterShiftFamilyCLM γ (fun i => -(circularContourAngularVelocities i * u))
        (y u - littleCircularMaterialContours hγ hγ1 u)) =
      canonicalPrefixMaterialGrowingCoordinate hγ hγ1 A₀ b R ρ k X u := by
    rw [(contourParameterShiftFamilyCLM γ (fun i => -(circularContourAngularVelocities i * u))).map_sub,
      materialUnshift_circularMaterialContours]
    rfl
  rw [hp] at hd
  simp_rw [hw] at hd
  refine ⟨E, ?_, hd⟩
  exact hE.trans (mul_le_mul_of_nonneg_right hCoeff (sq_nonneg _))

end CircularMaterialTransferProfile
end Euler2D

end
