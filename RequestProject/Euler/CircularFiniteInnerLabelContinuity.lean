module

public import RequestProject.Euler.CircularFiniteClusterContourForcing
public import RequestProject.Euler.TorusPhysicalLabelComplexField

/-! The actual finite inner cluster is one fixed initial label under
the same Euler transport. Its strong L1 time continuity is derived
without assuming that any of its later contours stay near circles. -/

@[expose] public section

set_option maxHeartbeats 2500000

noncomputable section

open Complex Set MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace Euler2D
namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

def finiteInnerInitialLabel (s A₀ b R ρ : ℝ) (N k : ℕ) (x : R2) : ℝ :=
  ∑ j ∈ Finset.Ico (k + 1) (N + 1), P.finitePeriodicLabel s A₀ b R ρ N j x

theorem finiteInnerInitialLabel_bounds {s A₀ b R ρ : ℝ} (hs : s ≤ 0)
    (hA : 0 ≤ A₀) (hb : 0 < b) (hR : 0 < R) (hRmax : R ≤ 1 / 2)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (N k : ℕ) :
    MemLp (P.finiteInnerInitialLabel s A₀ b R ρ N k) 2 μT ∧
      IsTorusPeriodic (P.finiteInnerInitialLabel s A₀ b R ρ N k) ∧
      ∀ x, ‖P.finiteInnerInitialLabel s A₀ b R ρ N k x‖ ≤
        ∑ j ∈ Finset.Ico (k + 1) (N + 1), finiteLabelAmplitudeBound * ampScale A₀ b j := by
  have hi : Integrable (P.finiteInnerInitialLabel s A₀ b R ρ N k) μT :=
    integrable_finset_sum _ fun j _ => (P.finitePeriodicLabel_bounds hs hA hb hR hRmax hρ hρ1 N j).1
  have hbound (x : R2) : ‖P.finiteInnerInitialLabel s A₀ b R ρ N k x‖ ≤
      ∑ j ∈ Finset.Ico (k + 1) (N + 1), finiteLabelAmplitudeBound * ampScale A₀ b j := by
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ =>
      (P.finitePeriodicLabel_bounds hs hA hb hR hRmax hρ hρ1 N j).2.2.1 x)
  refine ⟨MemLp.of_bound hi.aestronglyMeasurable _ (ae_of_all _ hbound), ?_, hbound⟩
  intro x i
  apply Finset.sum_congr rfl
  intro j _
  exact (P.finitePeriodicLabel_bounds hs hA hb hR hRmax hρ hρ1 N j).2.1 x i

theorem transported_finiteInnerInitialLabel_eq (s A₀ b R ρ : ℝ) (N k : ℕ)
    {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T) (t : ℝ) (x : R2) :
    S.transportedScalar (P.finiteInnerInitialLabel s A₀ b R ρ N k) t x =
      P.finiteInnerClusterSource s A₀ b R ρ N k S t x := rfl

theorem physicalComplexSource_finiteInnerInitialLabel_eq (s A₀ b R ρ : ℝ) (N k : ℕ)
    {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T) (t : ℝ) :
    S.physicalComplexSource (P.finiteInnerInitialLabel s A₀ b R ρ N k) t =
      P.finiteInnerClusterComplexSource s A₀ b R ρ N k S t := rfl

theorem tendsto_finiteInnerClusterComplexSource_L1 {s A₀ b R ρ : ℝ} (hs : s ≤ 0)
    (hA : 0 ≤ A₀) (hb : 0 < b) (hR : 0 < R) (hRmax : R ≤ 1 / 2)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (N k : ℕ)
    {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)
    {α : Type*} {l : Filter α} {τ : α → ℝ} {t : ℝ} (hτ : Tendsto τ l (𝓝 t)) :
    Tendsto (fun j => ∫ z : ℂ,
      |P.finiteInnerClusterComplexSource s A₀ b R ρ N k S (τ j) z -
        P.finiteInnerClusterComplexSource s A₀ b R ρ N k S t z|) l (𝓝 0) := by
  simpa only [P.physicalComplexSource_finiteInnerInitialLabel_eq] using
    S.tendsto_physicalComplexSource_L1_of_memLp
      (P.finiteInnerInitialLabel_bounds hs hA hb hR hRmax hρ hρ1 N k).1 hτ

end CircularMaterialTransferProfile
end Euler2D

end
