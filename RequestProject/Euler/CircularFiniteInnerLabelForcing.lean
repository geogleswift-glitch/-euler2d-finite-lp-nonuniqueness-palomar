module

public import RequestProject.Euler.CircularFiniteInnerLabelContinuity
public import RequestProject.Euler.TorusInnerLabelLittleForcing

/-! The original finite inner label sum supplies the genuine candidate
forcing, including the zero-mass and fourfold hypotheses. -/

@[expose] public section

set_option maxHeartbeats 3000000

noncomputable section

open Complex Set MeasureTheory Filter Topology Metric
open scoped NNReal ENNReal

namespace Euler2D
namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem finiteInnerInitialLabel_quarterTurn {s A₀ b R ρ : ℝ} (hs : s ≤ 0)
    (N k : ℕ) (x : R2) :
    P.finiteInnerInitialLabel s A₀ b R ρ N k (torusQuarterTurn x) =
      P.finiteInnerInitialLabel s A₀ b R ρ N k x := by
  apply Finset.sum_congr rfl
  intro j _
  exact P.finitePeriodicLabel_quarterTurn hs N j x

theorem integral_finiteInnerInitialLabel_zero {s A₀ b R ρ : ℝ} (hs : s ≤ 0)
    (hA : 0 ≤ A₀) (hb : 0 < b) (hR : 0 < R) (hRmax : R ≤ 1 / 2)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (N k : ℕ) :
    (∫ x in torusBox, P.finiteInnerInitialLabel s A₀ b R ρ N k x) = 0 := by
  unfold finiteInnerInitialLabel
  rw [integral_finset_sum _ (fun j _ =>
    (P.finitePeriodicLabel_bounds hs hA hb hR hRmax hρ hρ1 N j).1)]
  exact Finset.sum_eq_zero fun j _ => P.integral_finitePeriodicLabel_zero hs hR hRmax hρ hρ1 N j

theorem exists_finiteInnerCluster_candidateLittle_forcing
    {s A₀ b R ρ : ℝ} (hs : s ≤ 0)
    (hA : 0 ≤ A₀) (hb : 0 < b) (hR : 0 < R) (hRmax : R ≤ 1 / 2)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (N k : ℕ)
    {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)
    (hS : IsFourfoldBoundedEulerParticleSystem S)
    {ε a : ℝ} (hε : 0 < ε) (hεT : ε ≤ T) (ha : 0 ≤ a) (ha1 : a < 1)
    (hsupp : ∀ t ∈ Icc (0 : ℝ) ε, ∀ x ∈ torusBox,
      a < ‖x - torusCenter‖ → P.finiteInnerClusterSource s A₀ b R ρ N k S t x = 0)
    {η : ℝ≥0} {ι : Type*} [Fintype ι] (hη1 : (η : ℝ) ≤ 1)
    (d : ι → ℝ) (hd : ∀ i, 0 < d i) (hsep : ∀ i, 16 * a ≤ d i)
    (Z : ι → LittleContourSpace η)
    (hZ : ∀ i x, d i ≤ ‖ContourC1Space.toBCF η (Z i).val x‖) :
    ∃ E : ℝ → (ι → LittleContourSpace η) → ι → LittleContourSpace η,
      ∃ K : ℝ≥0, ∃ U : Set (ι → LittleContourSpace η), U ∈ 𝓝 Z ∧
        (∀ t, LipschitzOnWith K (E t) U) ∧
        (∀ W ∈ U, Continuous (fun t => E t W)) ∧
        ∀ t ∈ Icc (0 : ℝ) ε, ∀ W ∈ U, ∀ i θ,
          LittleContourSpace.lift η (E t W i) θ =
            velocityC (P.finiteInnerClusterComplexSource s A₀ b R ρ N k S t)
              (LittleContourSpace.lift η (W i) θ) := by
  obtain ⟨hq, hqper, hqbound⟩ := P.finiteInnerInitialLabel_bounds hs hA hb hR hRmax hρ hρ1 N k
  have hqm := P.integral_finiteInnerInitialLabel_zero hs hA hb hR hRmax hρ hρ1 N k
  have hqs : ∀ t ∈ Icc (0 : ℝ) ε, ∀ x ∈ torusBox,
      a < ‖x - torusCenter‖ →
        S.transportedScalar (P.finiteInnerInitialLabel s A₀ b R ρ N k) t x = 0 := hsupp
  obtain ⟨E, K, U, hU, hLip, hc, hE⟩ := S.exists_finitePhase_actualInner_forcing
    hS hq hqper (P.finiteInnerInitialLabel_quarterTurn hs N k) hqm hqbound
      hε hεT ha ha1 hqs hη1 d hd hsep Z hZ
  refine ⟨E, K, U, hU, hLip, hc, ?_⟩
  intro t ht W hW i θ
  simpa only [P.physicalComplexSource_finiteInnerInitialLabel_eq] using hE t ht W hW i θ

end CircularMaterialTransferProfile
end Euler2D

end
