module

public import RequestProject.Euler.CircularActualInnerProjectedForcing
public import RequestProject.Euler.CircularActualAdjacentMoment

/-! The literal actual finite inner forcing, on the child's clock,
has the observed child moment as its rho^6 leading term. The deeper
labels cost rho^8; the exterior remainder costs rho^10. All quantities
come from one original Euler particle system and uniform constants. -/

@[expose] public section

set_option maxHeartbeats 24000000
set_option maxRecDepth 7500

noncomputable section

open Complex Set MeasureTheory
open scoped NNReal ENNReal ComplexConjugate

namespace Euler2D

local instance (priority := 2000) actualAdjacentProjectedLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) actualAdjacentProjectedLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_uniform_actualFinite_adjacent_projected_leading {b Cb : ℝ}
    (hb : 0 < b) (hCb : 0 ≤ Cb) :
    ∃ C > 0, ∀ {s A₀ R ρ D ε η : ℝ},
      s ≤ 0 → 0 < A₀ → 0 < R → R ≤ 1 / 2 → 0 < ρ → ρ ≤ 1 →
      ρ ^ 2 ≤ b / 2 → 0 ≤ D → 0 ≤ ε → 0 ≤ η →
      ∀ (N j : ℕ), j + 1 ≤ N →
      ∀ {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T),
      IsFourfoldBoundedEulerParticleSystem S → ∀ t ∈ Icc (0 : ℝ) T, ∀ θp θc : ℝ, ∀ M : ℂ,
      Cb * radScale R ρ (j + 1) * (1 + D) < 1 →
      (∀ x ∈ torusBox, Cb * radScale R ρ (j + 1) * (1 + D) < ‖x - torusCenter‖ →
        P.finiteInnerClusterSource s A₀ b R ρ N j S t x = 0) →
      (∀ z, Cb * radScale R ρ (j + 1) * (1 + D) < ‖z‖ →
        boxedComplexDensity (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N (j + 1)) t) z = 0) →
      (∀ z, Cb * radScale R ρ (j + 1) * (1 + D) < ‖z‖ →
        P.finiteInnerClusterComplexSource s A₀ b R ρ N (j + 1) S t z = 0) →
      (‖momentN (boxedComplexDensity
          (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N (j + 1)) t)) 4 -
        (ampScale A₀ b (j + 1) : ℂ) * (radScale R ρ (j + 1) : ℂ) ^ 6 *
          Complex.exp (-(4 * (θc : ℂ) * I)) * M‖ ≤
        ampScale A₀ b (j + 1) * radScale R ρ (j + 1) ^ 6 * η) →
      8 * (Cb * ρ * (1 + D)) ≤ cellA / 2 →
      ∀ Z : Fin 2 → LittleContourSpace γ,
      (∀ i x, cellA / 2 ≤ ‖ContourC1Space.toBCF γ (Z i).val x‖) →
      (∀ i u, ‖LittleContourSpace.lift γ (Z i) u - refCircle (circularContourRadii i) u‖ ≤ ε) →
      ∃ Q : Fin 2 → LittleContourSpace γ,
        (∀ i u, LittleContourSpace.lift γ (Q i) u =
          Complex.exp (-((θp : ℂ) * I)) * ((ampScale A₀ b j * radScale R ρ j)⁻¹ •
            velocityC (P.finiteInnerClusterComplexSource s A₀ b R ρ N j S t)
              (radScale R ρ j • (Complex.exp ((θp : ℂ) * I) * LittleContourSpace.lift γ (Z i) u)))) ∧
        ‖(b : ℂ) * circularUnstableCoordinateCLM γ Q -
          (ρ : ℂ) ^ 6 * Kstar * Complex.exp (4 * ((θp - θc : ℝ) : ℂ) * I) * M‖ ≤
          C * (ρ ^ 10 * (1 + D) ^ 8 + ρ ^ 6 * (1 + D) ^ 4 * ε +
            ρ ^ 8 * (1 + D) ^ 4 + ρ ^ 6 * η) := by
  obtain ⟨Cf, hCf, hforce⟩ := P.exists_uniform_actualFinite_inner_projected_leading hb hCb
  let Cd := 2 * finiteLabelMassBound * Cb ^ 4 / b
  let C := b * Cf + ‖Kstar‖ * Cd + ‖Kstar‖ + 1
  have hCd : 0 ≤ Cd := by dsimp only [Cd]; positivity [finiteLabelMassBound_nonneg]
  have hBCf : 0 ≤ b * Cf := (mul_pos hb hCf).le
  have hKCd : 0 ≤ ‖Kstar‖ * Cd := mul_nonneg (norm_nonneg Kstar) hCd
  have hC : 0 < C := by dsimp only [C]; positivity
  have hCfC : b * Cf ≤ C := by dsimp only [C]; linarith only [hKCd, norm_nonneg Kstar]
  have hCdC : ‖Kstar‖ * Cd ≤ C := by dsimp only [C]; linarith only [hBCf, norm_nonneg Kstar]
  have hKC : ‖Kstar‖ ≤ C := by dsimp only [C]; linarith only [hBCf, hKCd]
  refine ⟨C, hC, ?_⟩
  intro s A₀ R ρ D ε η hs hA hR hRmax hρ hρ1 hhalf hD hε hη N j hjN f T S hS t ht θp θc M
    ha1 hsupp hchild hdeep hclose hsep Z hZ hnear
  have hRs : Cb * radScale R ρ (j + 1) * (1 + D) =
      Cb * ρ * radScale R ρ j * (1 + D) := by rw [radScale_succ_eq_mul]; ring
  obtain ⟨Q, hQ, hprojection⟩ := hforce hs hA hR hRmax hρ hρ1 hhalf hD hε
    N j S hS t ht θp (by rwa [← hRs]) (by simpa only [← hRs] using hsupp) hsep Z hZ hnear
  have hm := P.actual_adjacent_normalized_moment_close hs hA hb hR hRmax hρ hρ1 hhalf hCb hD
    N j hjN S t θp θc M hchild hdeep hclose
  let nM : ℂ := ((ampScale A₀ b j)⁻¹ : ℂ) * ((radScale R ρ j)⁻¹ : ℂ) ^ 6 *
    Complex.exp (4 * (θp : ℂ) * I) * momentN (P.finiteInnerClusterComplexSource s A₀ b R ρ N j S t) 4
  let mChild : ℂ := (ρ : ℂ) ^ 6 * Complex.exp (4 * ((θp - θc : ℝ) : ℂ) * I) * M
  let E₀ := ρ ^ 10 * (1 + D) ^ 8
  let E₁ := ρ ^ 6 * (1 + D) ^ 4 * ε
  let E₂ := ρ ^ 8 * (1 + D) ^ 4
  let E₃ := ρ ^ 6 * η
  have hE₀ : 0 ≤ E₀ := by dsimp only [E₀]; positivity
  have hE₁ : 0 ≤ E₁ := by dsimp only [E₁]; positivity
  have hE₂ : 0 ≤ E₂ := by dsimp only [E₂]; positivity
  have hE₃ : 0 ≤ E₃ := by dsimp only [E₃]; positivity
  change ‖circularUnstableCoordinateCLM γ Q - Kstar * nM‖ ≤ Cf * (E₀ + E₁) at hprojection
  have hm' : ‖(b : ℂ) * nM - mChild‖ ≤ Cd * E₂ + E₃ := by
    convert hm using 1 <;> dsimp only [nM, mChild, Cd, E₂, E₃] <;> ring
  refine ⟨Q, hQ, ?_⟩
  have hdiff : (b : ℂ) * circularUnstableCoordinateCLM γ Q -
      (ρ : ℂ) ^ 6 * Kstar * Complex.exp (4 * ((θp - θc : ℝ) : ℂ) * I) * M =
      (b : ℂ) * (circularUnstableCoordinateCLM γ Q - Kstar * nM) +
        Kstar * ((b : ℂ) * nM - mChild) := by dsimp only [mChild]; ring
  rw [hdiff]
  calc
    _ ≤ ‖(b : ℂ) * (circularUnstableCoordinateCLM γ Q - Kstar * nM)‖ +
        ‖Kstar * ((b : ℂ) * nM - mChild)‖ := norm_add_le _ _
    _ ≤ b * (Cf * (E₀ + E₁)) + ‖Kstar‖ * (Cd * E₂ + E₃) := by
      rw [norm_mul (b : ℂ) (circularUnstableCoordinateCLM γ Q - Kstar * nM),
        norm_mul Kstar ((b : ℂ) * nM - mChild), Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb]
      exact add_le_add (mul_le_mul_of_nonneg_left hprojection hb.le)
        (mul_le_mul_of_nonneg_left hm' (norm_nonneg Kstar))
    _ = (b * Cf) * E₀ + (b * Cf) * E₁ + (‖Kstar‖ * Cd) * E₂ + ‖Kstar‖ * E₃ := by ring
    _ ≤ C * E₀ + C * E₁ + C * E₂ + C * E₃ :=
      add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_right hCfC hE₀)
        (mul_le_mul_of_nonneg_right hCfC hE₁)) (mul_le_mul_of_nonneg_right hCdC hE₂))
        (mul_le_mul_of_nonneg_right hKC hE₃)
    _ = _ := by dsimp only [E₀, E₁, E₂, E₃]; ring

end CircularMaterialTransferProfile
end Euler2D

end
