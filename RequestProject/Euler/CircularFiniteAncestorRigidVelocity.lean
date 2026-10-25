module

public import RequestProject.Euler.CircularFiniteOuterRigidDecomposition

/-! The complete finite set of ancestors has one explicit, constant
angular velocity. The remaining velocity is exactly the sum of the
same-S source residuals used in the outer Little estimates. -/

@[expose] public section

set_option maxHeartbeats 3000000

noncomputable section

open Complex Set MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

def finiteAncestorAngularVelocity (A₀ b : ℝ) (k : ℕ) : ℝ :=
  (∑ j : Fin k, ampScale A₀ b j) / 2

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem velocityC_finiteAncestors_eq_rigid_add_residuals {s A₀ b R ρ : ℝ}
    (hs : s ≤ 0) (hA : 0 ≤ A₀) (hb : 0 < b)
    (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (N k : ℕ) (hk : k ≤ N) {f : Lp ℝ 2 μT} {T : ℝ}
    (S : BoundedEulerParticleSystem f T) (t : ℝ) {x : ℂ}
    (hx : ∀ j : Fin k, ‖x‖ ≤ cellA * radScale R ρ j) :
    let liftj : Fin k → Fin (N + 1) := fun j => ⟨j, j.isLt.trans_le (Nat.le_succ_of_le hk)⟩
    (∑ j : Fin k, velocityC (boxedComplexDensity
      (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N j) t)) x) =
      (finiteAncestorAngularVelocity A₀ b k : ℂ) * I * x +
      ∑ j : Fin k, velocityC
        (P.finiteOuterLabelComplexPerturbation s A₀ b R ρ N (liftj j) S t) x := by
  dsimp only
  have hpoint (j : Fin k) := P.velocityC_boxed_finiteLabel_eq_rigid_add_residual
    hs hA hb hR hRmax hρ hρ1 N
    (⟨j, j.isLt.trans_le (Nat.le_succ_of_le hk)⟩ : Fin (N + 1)) S t (hx j)
  calc
    _ = ∑ j : Fin k, (((ampScale A₀ b j : ℝ) : ℂ) * (I / 2) * x +
        velocityC (P.finiteOuterLabelComplexPerturbation s A₀ b R ρ N
          (⟨j, j.isLt.trans_le (Nat.le_succ_of_le hk)⟩ : Fin (N + 1)) S t) x) :=
      Finset.sum_congr rfl (fun j _ => hpoint j)
    _ = (∑ j : Fin k, ((ampScale A₀ b j : ℝ) : ℂ) * (I / 2) * x) +
        ∑ j : Fin k, velocityC (P.finiteOuterLabelComplexPerturbation s A₀ b R ρ N
          (⟨j, j.isLt.trans_le (Nat.le_succ_of_le hk)⟩ : Fin (N + 1)) S t) x :=
      Finset.sum_add_distrib
    _ = _ := by
      congr 1
      unfold finiteAncestorAngularVelocity
      push_cast
      rw [Finset.sum_div, Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring

end CircularMaterialTransferProfile
end Euler2D

end
