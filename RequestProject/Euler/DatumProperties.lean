module

public import RequestProject.Euler.VelocitySobolevDatum
public import RequestProject.Euler.DatumCurlSeries

/-!
# The actual stationary Sobolev datum

The velocity is the physical concentric velocity series, and its curl
is the original circular vorticity series. These are constructed
objects, rather than assumed inputs to the limit proposition.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Euler2D

/-- Admissible small radius ratios can be chosen below any prescribed
positive threshold. This leaves room for the interaction estimates. -/
lemma exists_small_radius_ratio {b q δ : ℝ} (hb : 0 < b) (hq : 0 < q) (hδ : 0 < δ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ ρ < δ ∧ ρ ^ (2 / q) < b := by
  let r := (b / 2) ^ (q / 2)
  have hr : 0 < r := Real.rpow_pos_of_pos (by positivity : 0 < b / 2) _
  let ρ := min r (min (1 / 2) (δ / 2))
  have hρ : 0 < ρ := lt_min hr (lt_min (by norm_num) (half_pos hδ))
  have hρr : ρ ≤ r := min_le_left _ _
  have hρhalf : ρ ≤ 1 / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hρδ : ρ ≤ δ / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hpow : r ^ (2 / q) = b / 2 := by
    dsimp only [r]
    rw [← Real.rpow_mul (by positivity : 0 ≤ b / 2)]
    have he : q / 2 * (2 / q) = 1 := by field_simp [hq.ne']
    rw [he, Real.rpow_one]
  refine ⟨ρ, hρ, by linarith, lt_of_le_of_lt hρδ (half_lt_self hδ), ?_⟩
  exact (Real.rpow_le_rpow hρ.le hρr (by positivity : 0 ≤ 2 / q)).trans_lt
    (by rw [hpow]; linarith)

/-- All stationary-datum conditions, with the exact vorticity identity,
for the actual physical series. No Euler evolution is assumed. -/
theorem physical_datum_properties {A₀ b R ρ p q : ℝ}
    (hA : 0 ≤ A₀) (hb : 0 < b) (hR : 0 < R) (hR1 : R ≤ 1)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hq : 2 ≤ q) (hpq : p ≤ q)
    (hsmall : ρ ^ (2 / q) < b) :
    let u₀ := velocityDatumL2 (A₀ := A₀) (b := b) hR hρ
    (∫ x in torusBox, u₀ x = 0) ∧ DivFree u₀ ∧
      MemW1p (ENNReal.ofReal p) u₀ ∧ IsStationary u₀ ∧
        ∃ ω : R2 → ℝ, MemLp ω (ENNReal.ofReal q) μT ∧ IsCurl u₀ ω := by
  have hqpos : 0 < q := by linarith
  have hqone : (1 : ENNReal) ≤ ENNReal.ofReal q := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ q by linarith)
  letI : Fact (1 ≤ ENNReal.ofReal q) := ⟨hqone⟩
  have hsmall2 := velocity_two_small_of_vorticity_small hρ hρ1 (by linarith : 1 ≤ q) hsmall
  refine ⟨integral_velocityDatumL2 hA hb hR hR1 hρ hρ1 hsmall2,
    divFree_velocityDatumL2 hA hb hR hR1 hρ hρ1 hsmall2,
    (memW1p_velocityDatumL2 hA hb hR hR1 hρ hρ1 hq hsmall).mono_exponent
      (ENNReal.ofReal_le_ofReal hpq),
    isStationary_velocityDatumL2 hA hb hR hR1 hρ hρ1 hsmall2,
    centeredCircularDatum (A₀ := A₀) (b := b) hR hρ hqpos,
    centeredCircularDatum_memLp hR hρ hqpos, ?_⟩
  exact isCurl_velocityDatumL2 hA hb hR hR1 hρ hρ1 hqpos hq hsmall

/-- For every requested finite Sobolev exponent, and arbitrarily small
scale ratio, the initial datum required by the main construction exists
as the explicit physical concentric series. -/
theorem exists_physical_stationary_datum (p : ℝ) {A₀ b R δ : ℝ}
    (hA : 0 ≤ A₀) (hb : 0 < b) (hR : 0 < R) (hR1 : R ≤ 1) (hδ : 0 < δ) :
    ∃ (ρ : ℝ) (hρ : 0 < ρ), ρ < 1 ∧ ρ < δ ∧
      let u₀ := velocityDatumL2 (A₀ := A₀) (b := b) hR hρ
      (∫ x in torusBox, u₀ x = 0) ∧ DivFree u₀ ∧
        MemW1p (ENNReal.ofReal p) u₀ ∧ IsStationary u₀ := by
  let q := max p 2
  have hq : 2 ≤ q := le_max_right _ _
  obtain ⟨ρ, hρ, hρ1, hρδ, hsmall⟩ := exists_small_radius_ratio hb
    (show 0 < q by linarith) hδ
  have hprop := physical_datum_properties hA hb hR hR1 hρ hρ1.le hq (le_max_left p 2) hsmall
  exact ⟨ρ, hρ, hρ1, hρδ, hprop.1, hprop.2.1, hprop.2.2.1, hprop.2.2.2.1⟩

end Euler2D

end
