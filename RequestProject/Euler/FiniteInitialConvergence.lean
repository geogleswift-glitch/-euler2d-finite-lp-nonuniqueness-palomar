module

public import RequestProject.Euler.CurlVelocityStability
public import RequestProject.Euler.DatumProperties

/-!
# Convergence of finite initial velocities with a noncircular base cell

The innermost cell in the finite construction need not be circular.
A uniform bound at its actual geometric scale makes its contribution
vanish, and the specified mean-zero divergence-free velocities converge
to the constructed stationary datum. No velocity-convergence assumption
or Calderón–Zygmund theorem is required.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Euler2D

/-- The exact finite vorticity datum, translated into the physical square. -/
def finiteBaseCurlL2 {A₀ b R ρ q : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hR : 0 < R) (hρ : 0 < ρ) (hq : 0 < q) (hp : 2 ≤ ENNReal.ofReal q)
    (base : ℕ → Lp ℝ (ENNReal.ofReal q) (volume : Measure R2)) (N : ℕ) : Lp ℝ 2 μT :=
  centeredPlaneToTorusL2 hp
    ((∑ j ∈ Finset.range N, datumTermLp (A₀ := A₀) (b := b) hR hρ hq j) + base N)

/-- The actual finite, possibly nonradial initial vorticities converge
strongly to the specified circular series in the physical L² space. -/
theorem tendsto_finiteBaseCurlL2 {A₀ b R ρ q C : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hA : 0 ≤ A₀) (hb : 0 < b) (hR : 0 < R) (hρ : 0 < ρ)
    (hq : 0 < q) (hp : 2 ≤ ENNReal.ofReal q) (hsmall : ρ ^ (2 / q) < b)
    (base : ℕ → Lp ℝ (ENNReal.ofReal q) (volume : Measure R2))
    (hbase : ∀ N, ‖base N‖ ≤ C * (ampScale A₀ b N * radScale R ρ N ^ (2 / q))) :
    Tendsto (finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hp base) atTop
      (𝓝 (centeredPlaneToTorusL2 hp (circularDatumLp (A₀ := A₀) (b := b) hR hρ hq))) :=
  ((centeredPlaneToTorusL2 hp).continuous.tendsto _).comp
    (tendsto_finite_base_datum hA hb hR hρ hq hsmall base hbase)

/-- The velocities belonging to the paper's finite initial vorticities
converge to the explicit stationary datum. Only their actual div–curl
equations and zero spatial means are inputs. -/
theorem tendsto_finite_initial_velocity {A₀ b R ρ q C : ℝ}
    [Fact (1 ≤ ENNReal.ofReal q)]
    (hA : 0 ≤ A₀) (hb : 0 < b) (hR : 0 < R) (hR1 : R ≤ 1)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hq : 0 < q) (hq2 : 2 ≤ q)
    (hp : 2 ≤ ENNReal.ofReal q) (hsmall : ρ ^ (2 / q) < b)
    (base : ℕ → Lp ℝ (ENNReal.ofReal q) (volume : Measure R2))
    (hbase : ∀ N, ‖base N‖ ≤ C * (ampScale A₀ b N * radScale R ρ N ^ (2 / q)))
    (initial : ℕ → L2T) (hdiv : ∀ N, DivFree (initial N))
    (hcurl : ∀ N, IsCurl (initial N)
      (finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hp base N))
    (hmean : ∀ N, (∫ x in torusBox, initial N x) = 0) :
    Tendsto initial atTop (𝓝 (velocityDatumL2 (A₀ := A₀) (b := b) hR hρ)) := by
  have hsmall2 := velocity_two_small_of_vorticity_small hρ hρ1 (by linarith : 1 ≤ q) hsmall
  apply tendsto_velocity_of_curl hdiv
    (divFree_velocityDatumL2 hA hb hR hR1 hρ hρ1 hsmall2) hcurl
  · exact (isCurl_velocityDatumL2 hA hb hR hR1 hρ hρ1 hq hq2 hsmall).congr_ae
      (EventuallyEq.refl _ _) (centeredPlaneToTorusL2_ae hp _).symm
  · intro N
    rw [hmean N, integral_velocityDatumL2 hA hb hR hR1 hρ hρ1 hsmall2]
  · exact tendsto_finiteBaseCurlL2 hA hb hR hρ hq hp hsmall base hbase

end Euler2D

end
