module

public import RequestProject.Euler.TorusInnerLabelLittleForcing
public import RequestProject.Euler.ClusterLittleForcingOnTargets

/-! One fixed genuine inner-label forcing on every separated active
target, with a finite contour norm bound and a local restart interface. -/

@[expose] public section

set_option maxHeartbeats 3500000

noncomputable section

open Complex Set MeasureTheory Filter Topology Metric
open scoped NNReal ENNReal

namespace Euler2D
namespace BoundedEulerParticleSystem

variable {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)

theorem exists_finitePhase_fixed_actualInner_forcing
    (hS : IsFourfoldBoundedEulerParticleSystem S)
    {q : R2 → ℝ} {M : ℝ} (hq : MemLp q 2 μT) (hqper : IsTorusPeriodic q)
    (hqrot : ∀ x, q (torusQuarterTurn x) = q x)
    (hqmean : (∫ x in torusBox, q x) = 0) (hM : ∀ x, ‖q x‖ ≤ M)
    {ε a : ℝ} (hε : 0 < ε) (hεT : ε ≤ T) (ha : 0 ≤ a) (ha1 : a < 1)
    (hsupp : ∀ t ∈ Icc (0 : ℝ) ε, ∀ x ∈ torusBox,
      a < ‖x - torusCenter‖ → S.transportedScalar q t x = 0)
    {γ : ℝ≥0} {ι : Type*} [Fintype ι] (hγ1 : (γ : ℝ) ≤ 1)
    (d : ι → ℝ) (hd : ∀ i, 0 < d i) (hsep : ∀ i, 16 * a ≤ d i) :
    ∃ E : ℝ → (ι → LittleContourSpace γ) → ι → LittleContourSpace γ,
      (∀ t W, (∀ i x, d i / 2 ≤ ‖ContourC1Space.toBCF γ (W i).val x‖) → ∀ i θ,
        LittleContourSpace.lift γ (E t W i) θ =
          velocityC (S.physicalComplexSource q (projIcc 0 ε hε.le t))
            (LittleContourSpace.lift γ (W i) θ)) ∧
      (∀ W, (∀ i x, d i / 2 ≤ ‖ContourC1Space.toBCF γ (W i).val x‖) →
        Continuous (fun t => E t W)) ∧
      (∀ Z, (∀ i x, d i ≤ ‖ContourC1Space.toBCF γ (Z i).val x‖) →
        ∃ K : ℝ≥0, ∃ U : Set (ι → LittleContourSpace γ), U ∈ 𝓝 Z ∧
          ∀ t, LipschitzOnWith K (E t) U) ∧
      ∀ t W, (∀ i x, d i / 2 ≤ ‖ContourC1Space.toBCF γ (W i).val x‖) → ∀ i,
        ‖E t W i‖ ≤ cauchyContourNormBudget 5 (γ : ℝ)
          (a ^ 4 * ∫ x in torusBox, |q x|) (d i / 2) ‖W i‖ := by
  let τ : ℝ → ℝ := fun t => projIcc 0 ε hε.le t
  have hτ : Continuous τ := continuous_subtype_val.comp continuous_projIcc
  have hτmem (t : ℝ) : τ t ∈ Icc (0 : ℝ) ε := (projIcc 0 ε hε.le t).property
  have hτT (t : ℝ) : τ t ∈ Icc (0 : ℝ) T := ⟨(hτmem t).1, (hτmem t).2.trans hεT⟩
  let u : ℝ → ℂ → ℝ := fun t => S.physicalComplexSource q (τ t)
  have hqi : Integrable q μT := hq.integrable (by norm_num)
  have hu (t : ℝ) : Integrable (u t) := S.integrable_physicalComplexLabelSource hqi _
  have huM (t : ℝ) (z : ℂ) : |u t z| ≤ M := by
    simpa only [Real.norm_eq_abs] using S.norm_physicalComplexLabelSource_le hM (τ t) z
  have hus (t : ℝ) : ∀ z, a < ‖z‖ → u t z = 0 :=
    S.physicalComplexSource_support (hsupp _ (hτmem t))
  have hum (t : ℝ) : (∫ z, u t z) = 0 :=
    (S.integral_physicalComplexLabelSource hqi hqper _).trans hqmean
  have huy (t : ℝ) : ∀ z, u t (I * z) = u t z :=
    S.physicalComplexSource_fourfold hS hqper hqrot ha1 (hτT t) (hsupp _ (hτmem t))
  let M₄ := a ^ 4 * ∫ x in torusBox, |q x|
  have hM₄ : 0 ≤ M₄ := by dsimp only [M₄]; positivity
  have huM₄ (t : ℝ) : (∫ z : ℂ, ‖z‖ ^ 4 * |u t z|) ≤ M₄ := by
    have hh := fourth_le_mass (hu t) (hus t)
    rw [S.integral_abs_physicalComplexLabelSource hqi hqper] at hh
    exact hh
  have huL1 (s : ℝ) : Tendsto (fun t => ∫ z : ℂ, |u t z - u s z|) (𝓝 s) (𝓝 0) :=
    S.tendsto_physicalComplexSource_L1_of_memLp hq (hτ.tendsto s)
  obtain ⟨E, hE, hc, hlocal⟩ := exists_finiteClusterLittle_fixed_forcing_on_targets
    hγ1 u ha hM₄ hu huM hus hum huy huM₄ huL1 d hd hsep
  refine ⟨E, hE, hc, hlocal, ?_⟩
  intro t W hW i
  obtain ⟨Q, hQ, hn⟩ := exists_clusterContourLittle hγ1 ha (hu t) (hus t)
    (hum t) (huy t) (huM₄ t) (half_pos (hd i)) (by linarith [hsep i]) (W i) (hW i)
  have he : Q = E t W i := by
    apply Subtype.ext
    apply ContourC1Space.ext
    intro x
    obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective x
    exact (hQ θ).trans (hE t W hW i θ).symm
  rwa [he] at hn

end BoundedEulerParticleSystem
end Euler2D

end
