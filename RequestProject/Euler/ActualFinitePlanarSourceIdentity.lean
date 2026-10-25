module

public import RequestProject.Euler.PlanarPeriodicLabelLocalization
public import RequestProject.Euler.CircularFinitePlanarClusterVelocity

/-! The actual boxed complex source is globally the same single planar
label transported by the original inverse particles. The identity holds
through the full localized time window, without smooth contour data. -/

@[expose] public section

set_option maxHeartbeats 5000000
set_option maxRecDepth 5500

noncomputable section

open Complex Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace Euler2D
namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_uniform_actualFinite_boxed_label_eq_singlePlanar :
    ∃ C : ℝ, 0 < C ∧ ∀ {s A₀ b R ρ q T H c : ℝ},
      ∀ [Fact (1 ≤ ENNReal.ofReal q)] (hs : s ≤ 0) (hA : 0 ≤ A₀) (hb : 0 < b)
        (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
        (hρb : ρ < b) (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q),
      0 ≤ H → H ≤ T → 5 / 4 + (C * A₀ / (1 - ρ / b)) * H < c → c * R < 1 →
      ∀ N : ℕ, ∀ S : BoundedEulerParticleSystem
        (finiteBaseCurlL2 (A₀ := A₀) (b := b) (ρ := ρ) hR hρ hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := b) (ρ := ρ) (q := q) hs hR hρ) N) T,
      ∀ t ∈ Icc (0 : ℝ) H, ∀ j : ℕ,
        boxedComplexDensity (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N j) t) =
          fun z => P.finiteSinglePlanarInitialLabel s A₀ b R ρ N j
            (S.backward t (complexTorusPoint z)) := by
  obtain ⟨C, hC, hlocalize⟩ := P.exists_uniform_actualFinite_planar_label_localization
  refine ⟨C, hC, ?_⟩
  intro s A₀ b R ρ q T H c _ hs hA hb hR hRmax hρ hρ1 hρb hq hqE
    hH hHT hdrift hcR N S t ht j
  have hloc := hlocalize (s := s) (A₀ := A₀) (b := b) (R := R) (ρ := ρ)
    (q := q) (T := T) (H := H) (c := c)
    hs hA hb hR hRmax hρ hρ1 hρb hq hqE hH hHT hdrift hcR N S t ht j
  funext z
  by_cases hz : complexTorusPoint z ∈ torusBox
  · rw [boxedComplexDensity, indicator_of_mem hz]
    have heq := hloc.1 1 1 (complexPhysicalPlane z)
      (by simpa only [one_smul, complexTorusPoint] using hz)
    simpa only [BoundedEulerParticleSystem.normalizedPlanarLabelSource, inv_one,
      one_mul, one_smul, complexTorusPoint] using heq.symm
  · rw [boxedComplexDensity, indicator_of_notMem hz]
    symm
    apply hloc.2
    by_contra hn
    exact hz (norm_sub_center_lt_one_mem_box ((not_lt.mp hn).trans_lt hcR))

end CircularMaterialTransferProfile
end Euler2D

end
