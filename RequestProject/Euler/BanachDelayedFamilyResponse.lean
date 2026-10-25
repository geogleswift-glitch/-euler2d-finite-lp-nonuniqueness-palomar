module

public import RequestProject.Euler.GronwallForcingBound

/-! A finite family of already existing slow trajectories has a
uniform delayed response. Its actual forcing may contain instantaneous
feedback from the common family norm. A compact-time maximum and a
strict algebraic smallness condition close that feedback, uniformly
in the number of ancestors. -/

@[expose] public section

set_option maxHeartbeats 3000000
set_option maxRecDepth 4000

noncomputable section

open Set Metric
open scoped NNReal

namespace Euler2D

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]

theorem delayed_finiteFamily_response_bound
    {f : E → E} {U : Set E} {K b : ℝ≥0} (hLip : LipschitzOnWith K f U)
    (a : ι → ℝ≥0) (ha : ∀ j, a j ≤ b)
    {D B feedback : ℝ} (hD : 0 ≤ D) (hB : 0 ≤ B) (hfeedback : 0 ≤ feedback)
    (y c p : ι → ℝ → E)
    (h0 : ∀ j, y j 0 = c j 0)
    (hyd : ∀ j t, t ∈ Icc (0 : ℝ) D →
      HasDerivAt (y j) ((a j : ℝ) • (f (y j t) + p j t)) t)
    (hcd : ∀ j t, t ∈ Icc (0 : ℝ) D → HasDerivAt (c j) ((a j : ℝ) • f (c j t)) t)
    (hym : ∀ j t, t ∈ Icc (0 : ℝ) D → y j t ∈ U)
    (hcm : ∀ j t, t ∈ Icc (0 : ℝ) D → c j t ∈ U)
    (hp : ∀ j t, t ∈ Icc (0 : ℝ) D →
      ‖p j t‖ ≤ B + feedback * ‖(fun i => y i t - c i t)‖)
    (hsmall : 2 * ((b : ℝ) * D * Real.exp (((b * K : ℝ≥0) : ℝ) * D)) * feedback ≤ 1) :
    ∀ j t, t ∈ Icc (0 : ℝ) D →
      ‖y j t - c j t‖ ≤
        2 * ((b : ℝ) * D * Real.exp (((b * K : ℝ≥0) : ℝ) * D)) * B := by
  let z : ℝ → ι → E := fun t j => y j t - c j t
  have hzc : ContinuousOn z (Icc (0 : ℝ) D) := by
    apply continuousOn_pi.mpr
    intro j
    have hyc : ContinuousOn (y j) (Icc (0 : ℝ) D) :=
      fun t ht => (hyd j t ht).continuousAt.continuousWithinAt
    have hcc : ContinuousOn (c j) (Icc (0 : ℝ) D) :=
      fun t ht => (hcd j t ht).continuousAt.continuousWithinAt
    exact hyc.sub hcc
  obtain ⟨t₀, ht₀, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (0 : ℝ) D).Nonempty from ⟨0, le_rfl, hD⟩) hzc.norm
  let Q : ℝ := ‖z t₀‖
  have hQ : 0 ≤ Q := norm_nonneg _
  have hbound (t : ℝ) (ht : t ∈ Icc (0 : ℝ) D) : ‖z t‖ ≤ Q := hmax ht
  let F : ℝ := (b : ℝ) * D * Real.exp (((b * K : ℝ≥0) : ℝ) * D)
  have hF : 0 ≤ F := mul_nonneg (mul_nonneg b.coe_nonneg hD) (Real.exp_pos _).le
  have hbase : 0 ≤ B + feedback * Q := add_nonneg hB (mul_nonneg hfeedback hQ)
  have hone (j : ι) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) D) :
      ‖y j t - c j t‖ ≤ F * (B + feedback * Q) := by
    have hKLip : LipschitzOnWith (a j * K) (fun x => (a j : ℝ) • f x) U := by
      apply LipschitzOnWith.of_dist_le_mul
      intro x hx w hw
      rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (a j).coe_nonneg]
      have hh := mul_le_mul_of_nonneg_left (hLip.dist_le_mul x hx w hw) (a j).coe_nonneg
      simpa only [NNReal.coe_mul, dist_eq_norm, mul_assoc] using hh
    have hpc (s : ℝ) (hs : s ∈ Icc (0 : ℝ) D) :
        ‖p j s‖ ≤ B + feedback * Q :=
      (hp j s hs).trans (add_le_add le_rfl
        (mul_le_mul_of_nonneg_left (hbound s hs) hfeedback))
    have hyc : ContinuousOn (y j) (Icc (0 : ℝ) D) :=
      fun s hs => (hyd j s hs).continuousAt.continuousWithinAt
    have hcc : ContinuousOn (c j) (Icc (0 : ℝ) D) :=
      fun s hs => (hcd j s hs).continuousAt.continuousWithinAt
    have hh := dist_le_of_approx_trajectories_ODE_of_mem
      (v := fun _ x => (a j : ℝ) • f x) (s := fun _ => U) (K := a j * K)
      (fun _ _ => hKLip) hyc
      (fun s hs => (hyd j s ⟨hs.1, hs.2.le⟩).hasDerivWithinAt)
      (εf := (a j : ℝ) * (B + feedback * Q)) (fun s hs => by
        have hh' := mul_le_mul_of_nonneg_left (hpc s ⟨hs.1, hs.2.le⟩) (a j).coe_nonneg
        simpa only [smul_add, dist_eq_norm, add_sub_cancel_left, norm_smul,
          Real.norm_eq_abs, abs_of_nonneg (a j).coe_nonneg] using hh')
      (fun s hs => hym j s ⟨hs.1, hs.2.le⟩) hcc
      (fun s hs => (hcd j s ⟨hs.1, hs.2.le⟩).hasDerivWithinAt)
      (εg := 0) (fun _ _ => by simp)
      (fun s hs => hcm j s ⟨hs.1, hs.2.le⟩)
      (δ := 0) (by rw [h0 j]; simp) t ht
    have hh' : ‖y j t - c j t‖ ≤
        gronwallBound 0 (((a j * K : ℝ≥0) : ℝ)) ((a j : ℝ) * (B + feedback * Q)) t := by
      simpa only [dist_eq_norm, add_zero, sub_zero] using hh
    have hg := gronwallBound_le_add_mul_exp (δ := 0) (a j * K).coe_nonneg
      (mul_nonneg (a j).coe_nonneg hbase) ht.1
    have htime : (a j : ℝ) * t ≤ (b : ℝ) * D :=
      (mul_le_mul_of_nonneg_right (show (a j : ℝ) ≤ (b : ℝ) from ha j) ht.1).trans
        (mul_le_mul_of_nonneg_left ht.2 b.coe_nonneg)
    have hexp : Real.exp ((((a j * K : ℝ≥0) : ℝ)) * t) ≤
        Real.exp ((((b * K : ℝ≥0) : ℝ)) * D) := by
      apply Real.exp_le_exp.mpr
      simp only [NNReal.coe_mul]
      nlinarith [mul_le_mul_of_nonneg_left htime K.coe_nonneg]
    have hmul := mul_le_mul htime hexp (Real.exp_pos _).le (mul_nonneg b.coe_nonneg hD)
    calc
      _ ≤ (a j : ℝ) * (B + feedback * Q) * t * Real.exp ((((a j * K : ℝ≥0) : ℝ)) * t) :=
        hh'.trans (by simpa only [zero_add] using hg)
      _ = ((a j : ℝ) * t * Real.exp ((((a j * K : ℝ≥0) : ℝ)) * t)) * (B + feedback * Q) := by ring
      _ ≤ F * (B + feedback * Q) := mul_le_mul_of_nonneg_right hmul hbase
  have hQineq : Q ≤ F * (B + feedback * Q) := by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg hF hbase)).mpr
    intro j
    exact hone j t₀ ht₀
  have hclosed : Q ≤ 2 * F * B := by
    have hh := mul_le_mul_of_nonneg_right hsmall hQ
    change 2 * F * feedback * Q ≤ 1 * Q at hh
    nlinarith
  intro j t ht
  exact ((norm_le_pi_norm (z t) j).trans (hbound t ht)).trans hclosed

end Euler2D

end
