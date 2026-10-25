module

public import RequestProject.Euler.TorusPhysicalSourceMass
public import RequestProject.Euler.CircularFiniteContourForcing

/-! A common A₀R² bound for the actual finite source L1 masses,
including the same noncircular ancient base cell. -/

@[expose] public section

set_option maxHeartbeats 2200000

noncomputable section

open Complex ComplexConjugate Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

theorem scalarLp_norm_eq_integral_norm_of_exponent_one {p : ℝ≥0∞} (hp : p = 1)
    (f : Lp ℝ p μT) : ‖f‖ = ∫ x in torusBox, ‖f x‖ := by
  subst p
  exact L1.norm_eq_integral_norm f

def circularFiniteL1Coefficient (b ρ : ℝ) : ℝ :=
  (eLpNorm cellW 1 volume).toReal / (1 - ρ ^ 2 / b) +
    finiteContourPatchMassBound circularContourStrengths circularContourRadii

theorem finiteBaseNormBound_one_eq (A₀ b R ρ : ℝ) :
    finiteBaseNormBound A₀ b R ρ 1
      (finiteContourPatchMassBound circularContourStrengths circularContourRadii) =
      circularFiniteL1Coefficient b ρ * (A₀ * R ^ 2) := by
  simp only [finiteBaseNormBound, circularFiniteL1Coefficient, ENNReal.ofReal_one, div_one,
    Real.rpow_two]

theorem eLpNorm_one_circularPhasePatchPlanarVorticity_le {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {Z : Fin 2 → LittleContourSpace γ}
    (hZ : Z ∈ circularQuarterPhaseDomain hγ hγ1) :
    (eLpNorm (circularPhasePatchPlanarVorticity Z) 1 volume).toReal ≤
      finiteContourPatchMassBound circularContourStrengths circularContourRadii := by
  let hw := memLp_circularPhasePatchPlanarVorticity hγ hγ1 hZ 1
  have hn : (eLpNorm (circularPhasePatchPlanarVorticity Z) 1 volume).toReal =
      ∫ x : R2, ‖circularPhasePatchPlanarVorticity Z x‖ := by
    calc
      _ = ‖hw.toLp (circularPhasePatchPlanarVorticity Z)‖ := (Lp.norm_toLp _ hw).symm
      _ = ∫ x : R2, ‖hw.toLp (circularPhasePatchPlanarVorticity Z) x‖ := L1.norm_eq_integral_norm _
      _ = _ := integral_congr_ae (hw.coeFn_toLp.fun_comp norm)
  rw [hn]
  have he : (∫ x : R2, ‖circularPhasePatchPlanarVorticity Z x‖) =
      ∫ z : ℂ, |circularPhasePatchVorticity Z z| := by
    simpa only [circularPhasePatchPlanarVorticity, Real.norm_eq_abs] using
      measurePreserving_planeComplexEquiv.integral_comp' (fun z => |circularPhasePatchVorticity Z z|)
  rw [he]
  exact integral_abs_circularPhasePatchVorticity_le hγ hγ1 hZ

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem integral_abs_finiteBaseCurlL2_le {s A₀ b R ρ q : ℝ}
    [Fact (1 ≤ ENNReal.ofReal q)] (hs : s ≤ 0) (hA : 0 ≤ A₀) (hb : 0 < b)
    (hR : 0 < R) (hρ : 0 < ρ) (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q)
    (hsmall : ρ ^ 2 < b) (N : ℕ) :
    (∫ x in torusBox, |finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
      (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N x|) ≤
      finiteBaseNormBound A₀ b R ρ 1
        (finiteContourPatchMassBound circularContourStrengths circularContourRadii) := by
  letI : Fact (1 ≤ ENNReal.ofReal (1 : ℝ)) := ⟨by norm_num⟩
  let B := finiteBaseTorusLp (A₀ := A₀) (b := b) (q := 1) hR hρ (by norm_num)
    (P.finiteBaseLp (A₀ := A₀) (b := b) (q := 1) hs hR hρ) N
  have he : (∫ x in torusBox, |finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
      (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N x|) = ‖B‖ := by
    have hn : ‖B‖ = ∫ x in torusBox, ‖B x‖ :=
      scalarLp_norm_eq_integral_norm_of_exponent_one ENNReal.ofReal_one B
    rw [hn]
    apply integral_congr_ae
    filter_upwards [P.finiteBaseCurlL2_ae_density (A₀ := A₀) (b := b) hs hR hρ hq hqE N,
      P.finiteBaseTorusLp_ae_density (A₀ := A₀) (b := b) (q := 1) hs hR hρ (by norm_num) N] with x hf hB
    rw [hf, hB, Real.norm_eq_abs]
  rw [he]
  have hp := eLpNorm_one_circularPhasePatchPlanarVorticity_le hγ hγ1 (P.ancient_domain s hs)
  have hM : 0 ≤ finiteContourPatchMassBound circularContourStrengths circularContourRadii :=
    ENNReal.toReal_nonneg.trans hp
  have hsmall1 : ρ ^ (2 / (1 : ℝ)) < b := by simpa using hsmall
  apply norm_finiteBaseTorusLp_le hA hb hR hρ (by norm_num) hM hsmall1
    (P.finiteBaseLp (A₀ := A₀) (b := b) (q := 1) hs hR hρ)
  intro n
  rw [P.norm_finiteBaseLp hs hA hb hR hρ (by norm_num)]
  apply mul_le_mul_of_nonneg_right
  · simpa only [ENNReal.ofReal_one] using hp
  · unfold ampScale radScale
    positivity

end CircularMaterialTransferProfile

end Euler2D

end
