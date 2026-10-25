module

public import RequestProject.Euler.CircularNormalizedProjectedForcing
public import RequestProject.Euler.CircularFiniteClusterContourForcing

/-! The actual finite Euler inner cluster has a genuine leading
growing-coordinate force. The normalized remainder is uniformly of
order rho^10 plus rho^6 times the actual target contour displacement.
All source invariants and mass estimates come from the same S. -/

@[expose] public section

set_option maxHeartbeats 24000000
set_option maxRecDepth 7500

noncomputable section

open Complex Set MeasureTheory
open scoped NNReal ENNReal ComplexConjugate

namespace Euler2D

local instance (priority := 2000) actualInnerProjectedLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) actualInnerProjectedLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_uniform_actualFinite_inner_projected_leading {b Cb : ℝ}
    (hb : 0 < b) (hCb : 0 ≤ Cb) :
    ∃ C > 0, ∀ {s A₀ R ρ D ε : ℝ},
      s ≤ 0 → 0 < A₀ → 0 < R → R ≤ 1 / 2 → 0 < ρ → ρ ≤ 1 →
      ρ ^ 2 ≤ b / 2 → 0 ≤ D → 0 ≤ ε →
      ∀ (N k : ℕ) {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T),
      IsFourfoldBoundedEulerParticleSystem S → ∀ t ∈ Icc (0 : ℝ) T, ∀ θ : ℝ,
      Cb * ρ * radScale R ρ k * (1 + D) < 1 →
      (∀ x ∈ torusBox, Cb * ρ * radScale R ρ k * (1 + D) < ‖x - torusCenter‖ →
        P.finiteInnerClusterSource s A₀ b R ρ N k S t x = 0) →
      8 * (Cb * ρ * (1 + D)) ≤ cellA / 2 →
      ∀ Z : Fin 2 → LittleContourSpace γ,
      (∀ i x, cellA / 2 ≤ ‖ContourC1Space.toBCF γ (Z i).val x‖) →
      (∀ i u, ‖LittleContourSpace.lift γ (Z i) u - refCircle (circularContourRadii i) u‖ ≤ ε) →
      ∃ Q : Fin 2 → LittleContourSpace γ,
        (∀ i u, LittleContourSpace.lift γ (Q i) u =
          Complex.exp (-((θ : ℂ) * I)) * ((ampScale A₀ b k * radScale R ρ k)⁻¹ •
            velocityC (P.finiteInnerClusterComplexSource s A₀ b R ρ N k S t)
              (radScale R ρ k • (Complex.exp ((θ : ℂ) * I) * LittleContourSpace.lift γ (Z i) u)))) ∧
        ‖circularUnstableCoordinateCLM γ Q - Kstar *
          (((ampScale A₀ b k)⁻¹ : ℂ) * ((radScale R ρ k)⁻¹ : ℂ) ^ 6 *
            Complex.exp (4 * (θ : ℂ) * I) * momentN (P.finiteInnerClusterComplexSource s A₀ b R ρ N k S t) 4)‖ ≤
          C * (ρ ^ 10 * (1 + D) ^ 8 + ρ ^ 6 * (1 + D) ^ 4 * ε) := by
  let d := cellA / 2
  let Acluster := 2 * finiteLabelMassBound / b
  let E₀ := 8 / (15 * Real.pi) * (Cb ^ 8 * Acluster) / d ^ 9
  let E₁ := (5 / (2 * Real.pi * d ^ 6)) * (Cb ^ 4 * Acluster)
  let c₀ := (2 / cellA) * E₀
  let c₁ := (2 / cellA) * E₁
  let C := c₀ + c₁ + 1
  have hd : 0 < d := half_pos cellA_pos
  have hAcl : 0 ≤ Acluster := by dsimp only [Acluster]; positivity [finiteLabelMassBound_nonneg]
  have hE₀ : 0 ≤ E₀ := by dsimp only [E₀]; positivity
  have hE₁ : 0 ≤ E₁ := by dsimp only [E₁]; positivity
  have hc₀ : 0 ≤ c₀ := mul_nonneg (div_nonneg (by norm_num) cellA_pos.le) hE₀
  have hc₁ : 0 ≤ c₁ := mul_nonneg (div_nonneg (by norm_num) cellA_pos.le) hE₁
  have hC : 0 < C := by dsimp only [C]; linarith only [hc₀, hc₁]
  have hc₀C : c₀ ≤ C := by dsimp only [C]; linarith only [hc₁]
  have hc₁C : c₁ ≤ C := by dsimp only [C]; linarith only [hc₀]
  refine ⟨C, hC, ?_⟩
  intro s A₀ R ρ D ε hs hA hR hRmax hρ hρ1 hhalf hD hε N k f T S hS t ht θ ha1 hsupp hsep Z hZ hnear
  let amp := ampScale A₀ b k
  let r := radScale R ρ k
  let w := P.finiteInnerClusterComplexSource s A₀ b R ρ N k S t
  let Rs := Cb * ρ * r * (1 + D)
  let Braw := amp * r ^ 2 * (Acluster * ρ ^ 2)
  have hamp : 0 < amp := div_pos hA (pow_pos hb k)
  have hr : 0 < r := radScale_pos hR hρ k
  have hRs : 0 ≤ Rs := by dsimp only [Rs]; positivity
  have hsmall : ρ ^ 2 < b := hhalf.trans_lt (by linarith only [hb])
  have hratio : ρ ^ 2 / b ≤ 1 / 2 := (div_le_iff₀ hb).mpr (by linarith only [hhalf])
  have hden : 0 < 1 - ρ ^ 2 / b := sub_pos.mpr ((div_lt_one hb).mpr hsmall)
  have hdenHalf : (1 / 2 : ℝ) ≤ 1 - ρ ^ 2 / b := by linarith only [hratio]
  have hw : Integrable w := P.integrable_finiteInnerClusterComplexSource hs hA.le hb hR hRmax hρ hρ1 N k S t
  have hsuppw : ∀ z, Rs < ‖z‖ → w z = 0 := boxedComplexDensity_support hsupp
  have hmassw : (∫ z, w z) = 0 :=
    P.integral_finiteInnerClusterComplexSource_zero hs hA.le hb hR hRmax hρ hρ1 N k S t
  have hsymw : ∀ z, w (I * z) = w z :=
    P.finiteInnerClusterComplexSource_fourfold hs N k S hS ht ha1 hsupp
  have hBraw : (∫ z : ℂ, |w z|) ≤ Braw := by
    have hm : (∫ z : ℂ, |w z|) ≤ finiteLabelMassBound * amp * r ^ 2 * (ρ ^ 2 / b) / (1 - ρ ^ 2 / b) := by
      rw [show w = boxedComplexDensity (P.finiteInnerClusterSource s A₀ b R ρ N k S t) from rfl,
        integral_abs_boxedComplexDensity]
      exact P.integral_abs_finiteInnerClusterSource_le hs hA.le hb hR hRmax hρ hρ1 hsmall N k S t
    calc
      _ ≤ (finiteLabelMassBound * amp * r ^ 2 * (ρ ^ 2 / b)) / (1 / 2) :=
        hm.trans (div_le_div_of_nonneg_left (by positivity [finiteLabelMassBound_nonneg])
          (by norm_num : (0 : ℝ) < 1 / 2) hdenHalf)
      _ = Braw := by dsimp only [Braw, Acluster]; field_simp [hb.ne'] <;> ring
  have hRsNorm : Rs / r = Cb * ρ * (1 + D) := by
    dsimp only [Rs]
    field_simp [hr.ne']
    <;> ring
  have hBnorm : amp⁻¹ * r⁻¹ ^ 2 * Braw = Acluster * ρ ^ 2 := by
    dsimp only [Braw]
    field_simp [hamp.ne', hr.ne']
    <;> ring
  obtain ⟨Q, hQ, hprojection⟩ := exists_circular_normalized_source_forcing_with_projection hγ hγ1.le
    hamp hr θ hRs hw hsuppw hmassw hsymw hBraw hd (half_le_self cellA_pos.le)
    (by rw [hRsNorm]; exact hsep) Z hZ hnear
  refine ⟨Q, hQ, ?_⟩
  rw [hRsNorm, hBnorm] at hprojection
  have herror :
      (2 / cellA) * (8 / (15 * Real.pi) * ((Cb * ρ * (1 + D)) ^ 8 * (Acluster * ρ ^ 2)) / d ^ 9 +
        (5 / (2 * Real.pi * d ^ 6)) * ((Cb * ρ * (1 + D)) ^ 4 * (Acluster * ρ ^ 2)) * ε) ≤
      C * (ρ ^ 10 * (1 + D) ^ 8 + ρ ^ 6 * (1 + D) ^ 4 * ε) := by
    calc
      _ = c₀ * (ρ ^ 10 * (1 + D) ^ 8) + c₁ * (ρ ^ 6 * (1 + D) ^ 4 * ε) := by
        dsimp only [c₀, c₁, E₀, E₁]
        ring
      _ ≤ C * (ρ ^ 10 * (1 + D) ^ 8) + C * (ρ ^ 6 * (1 + D) ^ 4 * ε) :=
        add_le_add (mul_le_mul_of_nonneg_right hc₀C (by positivity))
          (mul_le_mul_of_nonneg_right hc₁C (by positivity))
      _ = _ := by ring
  exact hprojection.trans herror

end CircularMaterialTransferProfile
end Euler2D

end
