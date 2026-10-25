module

public import RequestProject.Euler.PlanarLogFlowBijective

/-! Actual planar homeomorphism flows for a uniformly approximated
bounded logarithmically Lipschitz velocity. -/

@[expose] public section

noncomputable section

open Set Filter Topology
open scoped NNReal

namespace Euler2D

structure PlanarLogParticleFlow (v : ℝ → R2 → R2) (T : ℝ) where
  forward : ℝ → R2 → R2
  backward : ℝ → R2 → R2
  continuous_forward : Continuous (Function.uncurry forward)
  continuous_backward : Continuous (Function.uncurry backward)
  initial : ∀ a, forward 0 a = a
  derivative : ∀ t ∈ Icc (0 : ℝ) T, ∀ a,
    HasDerivAt (fun s => forward s a) (v t (forward t a)) t
  left_inv : ∀ t ∈ Icc (0 : ℝ) T, ∀ a, backward t (forward t a) = a
  right_inv : ∀ t ∈ Icc (0 : ℝ) T, ∀ a, forward t (backward t a) = a

def PlanarLogParticleFlow.homeomorph {v : ℝ → R2 → R2} {T : ℝ}
    (S : PlanarLogParticleFlow v T) (t : Icc (0 : ℝ) T) : R2 ≃ₜ R2 where
  toFun := S.forward t
  invFun := S.backward t
  left_inv := S.left_inv t t.property
  right_inv := S.right_inv t t.property
  continuous_toFun := S.continuous_forward.comp (continuous_const.prodMk continuous_id)
  continuous_invFun := S.continuous_backward.comp (continuous_const.prodMk continuous_id)

theorem exists_planarLogParticleFlow_of_uniform_approximation
    {v : ℝ → R2 → R2} (hv : Continuous (Function.uncurry v))
    (vn : ℕ → ℝ → R2 → R2) (Kn : ℕ → ℝ≥0) (M C : ℝ≥0)
    (hvn : ∀ n, IsBoundedLipschitzVelocity (vn n) (Kn n) M)
    (hmod : ∀ n t x y, ‖x - y‖ ≤ 1 / 2 →
      ‖vn n t x - vn n t y‖ ≤ (C : ℝ) * logFlowModulus ‖x - y‖)
    (hconv : TendstoUniformly (fun n (p : ℝ × R2) => vn n p.1 p.2)
      (Function.uncurry v) atTop)
    {T : ℝ} (hT : 0 ≤ T) : Nonempty (PlanarLogParticleFlow v T) := by
  classical
  obtain ⟨X, hXc, hX0, hXd⟩ := exists_continuous_planarParticleFamily hv vn Kn M C hvn hmod hconv hT
  have hvm := logMod_planarVelocity_of_uniform_approximation hmod hconv
  have hbij (t : Icc (0 : ℝ) T) : Function.Bijective (X t) :=
    ⟨logParticleFamily_injective hXc hX0 hXd hvm t.property,
      planarParticleFamily_surjective_of_approximation hv vn Kn M C hvn hmod hconv
        hXc hX0 hXd t.property⟩
  let B (t : Icc (0 : ℝ) T) : R2 ≃ R2 := Equiv.ofBijective (X t) (hbij t)
  let Y : ℝ → R2 → R2 := fun t a => (B (projIcc 0 T hT t)).symm a
  have hright (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (a : R2) : X t (Y t a) = a := by
    dsimp only [Y]
    rw [projIcc_of_mem hT ht]
    exact (B ⟨t, ht⟩).apply_symm_apply a
  have hleft (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (a : R2) : Y t (X t a) = a := by
    dsimp only [Y]
    rw [projIcc_of_mem hT ht]
    exact (B ⟨t, ht⟩).symm_apply_apply a
  have he : UniformEquicontinuous
      (fun (_ : Unit) (p : Icc (0 : ℝ) T × R2) => Y p.1 p.2) :=
    uniformEquicontinuous_inverse_logFlow_family hT C.coe_nonneg M.coe_nonneg
      (fun _ : Unit => v) (fun _ : Unit => X) (fun _ : Unit => Y)
      (fun _ => hXc) (fun _ => hXd) (fun _ => hX0) (fun _ => hright) (fun _ => hleft)
      (fun _ t _ x => norm_planarVelocity_of_uniform_approximation hvn hconv t x)
      (fun _ t _ x y hxy => hvm t x y hxy)
  have hBI : Continuous (fun p : Icc (0 : ℝ) T × R2 => (B p.1).symm p.2) := by
    simpa only [Y, projIcc_val] using (he.uniformContinuous ()).continuous
  have hYc : Continuous (Function.uncurry Y) :=
    hBI.comp (((continuous_projIcc (h := hT)).comp continuous_fst).prodMk continuous_snd)
  exact ⟨⟨X, Y, hXc, hYc, hX0, hXd, hleft, hright⟩⟩

end Euler2D

end
