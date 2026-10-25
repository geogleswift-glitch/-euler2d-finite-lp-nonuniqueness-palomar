module

public import RequestProject.Euler.BanachBallRetraction
public import RequestProject.Euler.BoundedNonautonomousBanachFlow

/-! A prescribed full time interval is obtained by an actual bounded
extension and Picard construction. A quantitative Gronwall estimate
then proves that the extension agrees with the original field. The
trajectory is not assumed in advance to stay in the reference tube. -/

@[expose] public section

set_option maxHeartbeats 2500000

noncomputable section

open Set Filter Topology Metric ODE
open scoped NNReal

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem exists_nonautonomous_banachFlow_in_reference_tube
    (F : ℝ → E → E) (c c' : ℝ → E) {U : Set E} {K : ℝ≥0}
    {T r δ ε : ℝ} (hT : 0 < T) (hr : 0 < r) (hδ : 0 < δ) (hε : 0 ≤ ε)
    (hc : ContinuousOn c (Icc (0 : ℝ) T))
    (hc' : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt c (c' t) t)
    (htube : ∀ t ∈ Icc (0 : ℝ) T, closedBall (c t) r ⊆ U)
    (hLip : ∀ t ∈ Icc (0 : ℝ) T, LipschitzOnWith K (F t) U)
    (hcont : ∀ y ∈ U, ContinuousOn (fun t => F t y) (Icc (0 : ℝ) T))
    (herror : ∀ t ∈ Icc (0 : ℝ) T, dist (c' t) (F t (c t)) ≤ ε)
    (hsmall : gronwallBound δ (2 * (K : ℝ)) ε T < r) :
    ∃ X : E → ℝ → E,
      IsNonautonomousBanachFlowOn F U (ball (c 0) δ) T X ∧
      ∀ b ∈ ball (c 0) δ, ∀ t ∈ Icc (0 : ℝ) T,
        dist (X b t) (c t) ≤ gronwallBound δ (2 * (K : ℝ)) ε t ∧
        X b t ∈ ball (c t) r := by
  classical
  let τ : ℝ → ℝ := fun t => (projIcc 0 T hT.le t : ℝ)
  have hτ : Continuous τ := continuous_subtype_val.comp continuous_projIcc
  have hτmem (t : ℝ) : τ t ∈ Icc (0 : ℝ) T := (projIcc 0 T hT.le t).property
  have hτeq (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : τ t = t := by
    exact congrArg Subtype.val (projIcc_of_mem hT.le ht)
  have hcU (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : c t ∈ U :=
    htube t ht (mem_closedBall_self hr.le)
  have hjoint : ContinuousOn (Function.uncurry F) (Icc (0 : ℝ) T ×ˢ U) :=
    continuousOn_prod_of_continuousOn_lipschitzOnWith' _ K hLip hcont
  have hbase : ContinuousOn (fun t => F t (c t)) (Icc (0 : ℝ) T) :=
    hjoint.comp (continuousOn_id.prodMk hc) (fun t ht => ⟨ht, hcU t ht⟩)
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hbase
  have hcc : Continuous (fun t => c (τ t)) := hc.comp_continuous hτ hτmem
  let G : ℝ → E → E := fun t x => F (τ t) (centeredBallRetraction r (c (τ t)) x)
  have hretU (t : ℝ) (x : E) : centeredBallRetraction r (c (τ t)) x ∈ U :=
    htube (τ t) (hτmem t) (centeredBallRetraction_mem_closedBall hr _ _)
  have hGLip (t : ℝ) : LipschitzWith (2 * K) (G t) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have hh := (hLip (τ t) (hτmem t)).dist_le_mul _ (hretU t x) _ (hretU t y)
    calc
      dist (G t x) (G t y) ≤ (K : ℝ) *
          dist (centeredBallRetraction r (c (τ t)) x) (centeredBallRetraction r (c (τ t)) y) := hh
      _ ≤ (K : ℝ) * (2 * dist x y) := mul_le_mul_of_nonneg_left
        ((lipschitzWith_centeredBallRetraction hr (c (τ t))).dist_le_mul x y) K.coe_nonneg
      _ = _ := by simp only [NNReal.coe_mul, NNReal.coe_ofNat]; ring
  have hGc (x : E) : Continuous (fun t => G t x) := by
    apply hjoint.comp_continuous
      (hτ.prodMk ((continuous_centeredBallRetraction hr).comp (hcc.prodMk continuous_const)))
    intro t
    exact ⟨hτmem t, hretU t x⟩
  have hGbound (t : ℝ) (x : E) : ‖G t x‖ ≤ (K : ℝ) * r + |B| := by
    have hh := (hLip (τ t) (hτmem t)).dist_le_mul _ (hretU t x) _ (hcU _ (hτmem t))
    have hd : dist (centeredBallRetraction r (c (τ t)) x) (c (τ t)) ≤ r :=
      mem_closedBall.mp (centeredBallRetraction_mem_closedBall hr _ _)
    calc
      ‖G t x‖ ≤ ‖G t x - F (τ t) (c (τ t))‖ + ‖F (τ t) (c (τ t))‖ := norm_le_norm_sub_add _ _
      _ ≤ (K : ℝ) * r + |B| := by
        rw [← dist_eq_norm]
        exact add_le_add (hh.trans (mul_le_mul_of_nonneg_left hd K.coe_nonneg))
          ((hB _ (hτmem t)).trans (le_abs_self _))
  have hGeq (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (x : E)
      (hx : x ∈ closedBall (c t) r) : G t x = F t x := by
    dsimp only [G]
    rw [hτeq t ht, centeredBallRetraction_eq hr hx]
  obtain ⟨X, hX⟩ := exists_bounded_nonautonomous_banachFlow G (c 0)
    (show 0 ≤ (K : ℝ) * r + |B| by positivity) hδ hT hGLip hGc hGbound
  have hdist (b : E) (hb : b ∈ ball (c 0) δ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      dist (X b t) (c t) ≤ gronwallBound δ (2 * (K : ℝ)) ε t := by
    have hh := dist_le_of_approx_trajectories_ODE (v := G) (K := 2 * K)
      hGLip (hX.continuous b hb)
      (fun u hu => (hX.hasDerivAt b hb u ⟨hu.1, hu.2.le⟩).hasDerivWithinAt)
      (εf := 0) (fun _ _ => by simp)
      hc (fun u hu => (hc' u ⟨hu.1, hu.2.le⟩).hasDerivWithinAt)
      (εg := ε) (fun u hu => by
        rw [hGeq u ⟨hu.1, hu.2.le⟩ (c u) (mem_closedBall_self hr.le)]
        exact herror u ⟨hu.1, hu.2.le⟩)
      (δ := δ) (by rw [hX.initial b hb]; exact (mem_ball.mp hb).le) t ht
    simpa only [zero_add, sub_zero, NNReal.coe_mul, NNReal.coe_ofNat] using hh
  have hmem (b : E) (hb : b ∈ ball (c 0) δ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      X b t ∈ ball (c t) r := by
    apply mem_ball.mpr
    exact (hdist b hb t ht).trans_lt
      ((gronwallBound_mono hδ.le hε (by positivity) ht.2).trans_lt hsmall)
  refine ⟨X, ?_, fun b hb t ht => ⟨hdist b hb t ht, hmem b hb t ht⟩⟩
  constructor
  · exact hX.initial
  · exact hX.continuous
  · intro b hb t ht
    rw [← hGeq t ht (X b t) (ball_subset_closedBall (hmem b hb t ht))]
    exact hX.hasDerivAt b hb t ht
  · intro b hb t ht
    exact htube t ht (ball_subset_closedBall (hmem b hb t ht))

end Euler2D

end
