module

public import RequestProject.Euler.RegularizedParticleEstimates
public import RequestProject.Euler.PeriodicLogFlowCompactness

/-! An actual sequence of self-consistent regularized systems and its common flow bounds. -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal

namespace Euler2D

lemma radialApproxScale_le_one (n : ℕ) : radialApproxScale n ≤ 1 := by
  unfold radialApproxScale
  apply (div_le_one (by positivity : (0 : ℝ) < (n : ℝ) + 1)).mpr
  linarith [Nat.cast_nonneg (α := ℝ) n]

def regularizedApproximationConstant (w : R2 → ℝ) (hw : Integrable w μT)
    {T : ℝ} (hT : 0 ≤ T) (n : ℕ) : ℝ≥0 :=
  (exists_regularizedTorusParticleSystem hw hT (radialApproxScale_pos n)
    (radialApproxScale_le_one n)).choose

def regularizedApproximationSystem (w : R2 → ℝ) (hw : Integrable w μT)
    {T : ℝ} (hT : 0 ≤ T) (n : ℕ) :
    SmoothRegularizedParticleSystem (regularizedTorusKernel (radialApproxScale n) (radialApproxScale_pos n))
      w T (regularizedApproximationConstant w hw hT n) (regularizedApproximationConstant w hw hT n) :=
  Classical.choice (exists_regularizedTorusParticleSystem hw hT (radialApproxScale_pos n)
    (radialApproxScale_le_one n)).choose_spec

def regularizedApproximationVelocity (w : R2 → ℝ) (hw : Integrable w μT)
    {T : ℝ} (hT : 0 ≤ T) (n : ℕ) : ℝ → R2 → R2 :=
  (regularizedApproximationSystem w hw hT n).velocity

def regularizedApproximationForward (w : R2 → ℝ) (hw : Integrable w μT)
    {T : ℝ} (hT : 0 ≤ T) (n : ℕ) : ℝ → R2 → R2 :=
  (regularizedApproximationSystem w hw hT n).forward

def regularizedApproximationBackward (w : R2 → ℝ) (hw : Integrable w μT)
    {T : ℝ} (hT : 0 ≤ T) (n : ℕ) : ℝ → R2 → R2 :=
  (regularizedApproximationSystem w hw hT n).backward

theorem exists_uniform_bounds_regularizedApproximation
    (w : R2 → ℝ) (hw : Integrable w μT) {T B : ℝ} (hT : 0 ≤ T)
    (hB0 : 0 ≤ B) (hB : ∀ᵐ y ∂μT, ‖w y‖ ≤ B) :
    ∃ C M : ℝ, 0 ≤ C ∧ 0 ≤ M ∧
      (∀ n t, t ∈ Icc 0 T → ∀ x, ‖regularizedApproximationVelocity w hw hT n t x‖ ≤ M) ∧
      ∀ n t, t ∈ Icc 0 T → ∀ x z, ‖x - z‖ ≤ 1 / 2 →
        ‖regularizedApproximationVelocity w hw hT n t x -
          regularizedApproximationVelocity w hw hT n t z‖ ≤ C * logFlowModulus ‖x - z‖ := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_logLip_regularizedParticleVelocity
  refine ⟨B * C, B * ∫ y in torusBox, ‖torusBiotSavartKernel y‖,
    mul_nonneg hB0 hC, mul_nonneg hB0 (integral_nonneg fun _ => norm_nonneg _), ?_, ?_⟩
  · intro n t ht x
    exact norm_regularizedParticleVelocity_le (radialApproxScale_pos n) (radialApproxScale_le_one n)
      (regularizedApproximationSystem w hw hT n) hB0 hB ht x
  · intro n t ht x z hxz
    exact hbound (radialApproxScale n) (radialApproxScale_pos n) (radialApproxScale_le_one n)
      w T _ _ (regularizedApproximationSystem w hw hT n) B hw.aestronglyMeasurable hB0 hB t ht x z hxz

theorem uniform_subseq_regularizedApproximationForward
    (w : R2 → ℝ) (hw : Integrable w μT) {T B : ℝ} (hT : 0 ≤ T)
    (hB0 : 0 ≤ B) (hB : ∀ᵐ y ∂μT, ‖w y‖ ≤ B) :
    ∃ F : Icc (0 : ℝ) T × R2 → R2, Continuous F ∧
      (∀ t : Icc (0 : ℝ) T, TorusAreaPreserving (fun a => F (t, a))) ∧
      (∀ a, F (⟨0, le_rfl, hT⟩, a) = a) ∧
      (∀ (t : Icc (0 : ℝ) T) a k,
        F (t, a + torusLatticeShift k) = F (t, a) + torusLatticeShift k) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ TendstoUniformly
        (fun n (p : Icc (0 : ℝ) T × R2) => regularizedApproximationForward w hw hT (φ n) p.1 p.2) F atTop := by
  obtain ⟨C, M, hC, hM0, hM, hlip⟩ := exists_uniform_bounds_regularizedApproximation w hw hT hB0 hB
  exact uniform_subseq_periodic_logFlow_family hT hC hM0
    (regularizedApproximationVelocity w hw hT) (regularizedApproximationForward w hw hT)
    (fun n => (regularizedApproximationSystem w hw hT n).forward_continuous)
    (fun n => (regularizedApproximationSystem w hw hT n).derivative)
    (fun n => (regularizedApproximationSystem w hw hT n).initial) hM hlip
    (fun n => (regularizedApproximationSystem w hw hT n).forward_lattice)
    (fun n => (regularizedApproximationSystem w hw hT n).forward_area)

end Euler2D

end
