module

public import RequestProject.Euler.BiotSavartL2
public import RequestProject.Euler.FiniteInitialConvergence

/-!
# Identification of the actual datum with its torus Biot–Savart velocity

The explicit radial velocity series is identified with the normalized
inverse curl by uniqueness. Consequently the velocities of the finite
noncircular vorticity data converge without any assumed velocity equations
or any velocity-convergence input.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology

namespace Euler2D

lemma IsCurl.integral_eq_zero {u : R2 → R2} {w : R2 → ℝ} (hc : IsCurl u w) :
    (∫ x in torusBox, w x) = 0 := by
  have h := hc (fun _ => 1) ⟨contDiff_const, fun _ _ => rfl⟩
  simpa [pd] using h

theorem biotSavartL2_eq_of_div_curl {u : L2T} {w : Lp ℝ 2 μT}
    (hu : DivFree u) (hc : IsCurl u w) (hm : (∫ x in torusBox, u x) = 0) :
    biotSavartL2 w = u := by
  exact velocity_eq_of_curl_eq (divFree_biotSavartL2 w) hu
    (isCurl_biotSavartL2 w hc.integral_eq_zero) hc ((integral_biotSavartL2 w).trans hm.symm)

/-- The explicit physical velocity datum is the actual normalized torus
Biot–Savart field of the original circular vorticity series. -/
theorem biotSavartL2_circularDatum {A₀ b R ρ q : ℝ}
    [Fact (1 ≤ ENNReal.ofReal q)]
    (hA : 0 ≤ A₀) (hb : 0 < b) (hR : 0 < R) (hR1 : R ≤ 1)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hq : 0 < q) (hq2 : 2 ≤ q)
    (hp : 2 ≤ ENNReal.ofReal q) (hsmall : ρ ^ (2 / q) < b) :
    biotSavartL2 (centeredPlaneToTorusL2 hp
      (circularDatumLp (A₀ := A₀) (b := b) hR hρ hq)) =
        velocityDatumL2 (A₀ := A₀) (b := b) hR hρ := by
  have hsmall2 := velocity_two_small_of_vorticity_small hρ hρ1 (by linarith : 1 ≤ q) hsmall
  apply biotSavartL2_eq_of_div_curl
    (divFree_velocityDatumL2 hA hb hR hR1 hρ hρ1 hsmall2)
  · exact (isCurl_velocityDatumL2 hA hb hR hR1 hρ hρ1 hq hq2 hsmall).congr_ae
      (EventuallyEq.refl _ _) (centeredPlaneToTorusL2_ae hp _).symm
  · exact integral_velocityDatumL2 hA hb hR hR1 hρ hρ1 hsmall2

/-- The finite initial velocities are constructed by the actual inverse
curl, and their convergence follows from the proved scalar series bound. -/
theorem tendsto_biotSavartL2_finite_base {A₀ b R ρ q C : ℝ}
    [Fact (1 ≤ ENNReal.ofReal q)]
    (hA : 0 ≤ A₀) (hb : 0 < b) (hR : 0 < R) (hR1 : R ≤ 1)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hq : 0 < q) (hq2 : 2 ≤ q)
    (hp : 2 ≤ ENNReal.ofReal q) (hsmall : ρ ^ (2 / q) < b)
    (base : ℕ → Lp ℝ (ENNReal.ofReal q) (volume : Measure R2))
    (hbase : ∀ N, ‖base N‖ ≤ C * (ampScale A₀ b N * radScale R ρ N ^ (2 / q))) :
    Tendsto (fun N => biotSavartL2
      (finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hp base N)) atTop
        (𝓝 (velocityDatumL2 (A₀ := A₀) (b := b) hR hρ)) := by
  rw [← biotSavartL2_circularDatum hA hb hR hR1 hρ hρ1 hq hq2 hp hsmall]
  exact (biotSavartL2.continuous.tendsto _).comp
    (tendsto_finiteBaseCurlL2 hA hb hR hρ hq hp hsmall base hbase)

end Euler2D

end
