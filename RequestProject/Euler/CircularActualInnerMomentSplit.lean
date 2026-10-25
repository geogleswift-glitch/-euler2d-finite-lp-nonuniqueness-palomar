module

public import RequestProject.Euler.ComplexCompactMomentAdd
public import RequestProject.Euler.CircularFiniteInteractionDecomposition

/-! The true parent inner-cluster moment is exactly the activated
child moment plus the deeper-cluster moment. The latter is bounded
by its own actual transported mass and a supplied particle radius. -/

@[expose] public section

set_option maxHeartbeats 12000000
set_option maxRecDepth 6500

noncomputable section

open Complex Set MeasureTheory
open scoped NNReal ENNReal ComplexConjugate

namespace Euler2D
namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem actual_parent_inner_moment_eq_child_add_deeper
    {s A₀ b R ρ : ℝ} (hs : s ≤ 0) (hA : 0 ≤ A₀) (hb : 0 < b)
    (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hsmall : ρ ^ 2 < b) (N k : ℕ) (hk : 0 < k) (hkN : k ≤ N)
    {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T) (t : ℝ)
    {Bchild Bdeep : ℝ} (hBdeep : 0 ≤ Bdeep)
    (hchild : ∀ z, Bchild < ‖z‖ →
      boxedComplexDensity (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N k) t) z = 0)
    (hdeep : ∀ z, Bdeep < ‖z‖ → P.finiteInnerClusterComplexSource s A₀ b R ρ N k S t z = 0) :
    (momentN (P.finiteInnerClusterComplexSource s A₀ b R ρ N (k - 1) S t) 4 =
      momentN (boxedComplexDensity (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N k) t)) 4 +
        momentN (P.finiteInnerClusterComplexSource s A₀ b R ρ N k S t) 4) ∧
    ‖momentN (P.finiteInnerClusterComplexSource s A₀ b R ρ N (k - 1) S t) 4 -
      momentN (boxedComplexDensity (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N k) t)) 4‖ ≤
        Bdeep ^ 4 * finiteInnerClusterMassBudget A₀ b R ρ k := by
  have hik : Integrable (boxedComplexDensity (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N k) t)) :=
    (P.boxed_finitePeriodicLabel_bounds hs hA hb hR hRmax hρ hρ1 N k S t).1
  have hideep := P.integrable_finiteInnerClusterComplexSource hs hA hb hR hRmax hρ hρ1 N k S t
  have hsplit := P.finiteInnerClusterComplexSource_eq_middle_add_deep s A₀ b R ρ N (k - 1) k
    (Nat.sub_le k 1) hkN S t
  have hksucc : k - 1 + 1 = k := by omega
  have hIco : Finset.Ico k (k + 1) = {k} := by
    ext j
    simp only [Finset.mem_Ico, Finset.mem_singleton]
    omega
  have hsplit' : P.finiteInnerClusterComplexSource s A₀ b R ρ N (k - 1) S t = fun z =>
      boxedComplexDensity (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N k) t) z +
        P.finiteInnerClusterComplexSource s A₀ b R ρ N k S t z := by
    simpa only [hksucc, hIco, Finset.sum_singleton] using hsplit
  have heq : momentN (P.finiteInnerClusterComplexSource s A₀ b R ρ N (k - 1) S t) 4 =
      momentN (boxedComplexDensity (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N k) t)) 4 +
        momentN (P.finiteInnerClusterComplexSource s A₀ b R ρ N k S t) 4 := by
    rw [hsplit']
    exact complexMoment_add_of_compact_support hik hideep hchild hdeep 4
  refine ⟨heq, ?_⟩
  rw [heq, add_sub_cancel_left]
  apply norm_complexMoment_le_support_mass hBdeep hideep hdeep
  rw [finiteInnerClusterComplexSource, integral_abs_boxedComplexDensity]
  exact P.integral_abs_finiteInnerClusterSource_le hs hA hb hR hRmax hρ hρ1 hsmall N k S t

end CircularMaterialTransferProfile
end Euler2D

end
