module

public import RequestProject.Euler.BanachLocalBackwardGraph
public import RequestProject.Euler.BanachQuadraticGraphFlattening

/-! Flattening a fixed block uses the very same weighted graph. Its
already proved block invariance and local quadratic Lipschitz estimate
suffice; a new invariant graph or equivalent Banach norm is not chosen. -/

@[expose] public section

set_option maxHeartbeats 2500000

noncomputable section

open Set Filter Topology Metric
open scoped ContDiff

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem exists_fixed_backwardGraph_block_flattened_bounds
    {F : E → E} {P : E →L[ℝ] E} {ρ r : ℝ} {x : E → ℕ → E}
    (hg : IsLocalWeightedBackwardGraph F P ρ r x) (hρ : 1 ≤ ρ) (hr : 0 < r)
    (hP : ∀ v, P (P v) = P v)
    (T : E → E) (hT : ContDiffAt ℝ 2 T 0) (hT0 : T 0 = 0)
    (A : E →L[ℝ] E) (hTA : HasFDerivAt T A 0) (hcomm : A.comp P = P.comp A)
    {d H η₀ : ℝ} (hd : 0 < d) (hdr : d ≤ r / 2) (hH : 0 < H) (hη₀ : 0 < η₀)
    (hquad : ∀ α, P α = α → ‖α‖ ≤ d → ∀ β, P β = β → ‖β‖ ≤ d →
      ‖(x α 0 - α) - (x β 0 - β)‖ ≤ H * (‖α‖ + ‖β‖) * ‖α - β‖)
    (hinv : ∀ α, P α = α → ‖α‖ ≤ η₀ →
      ‖P (T (x α 0))‖ ≤ r / 2 ∧ x (P (T (x α 0))) = (fun n => T (x α n))) :
    ∃ C > 0, ∃ s > 0, s ≤ d ∧ ∀ α w, P α = α → P w = 0 → ‖α‖ + ‖w‖ ≤ s →
      let g := fun v => x v 0 - v
      let z := α + g α + w
      ‖P (T z) - A α‖ ≤ C * (‖α‖ + ‖w‖) ^ 2 ∧
      ‖(T z - P (T z)) - g (P (T z)) - A w‖ ≤ C * (‖α‖ + ‖w‖) * ‖w‖ := by
  let g := fun v => x v 0 - v
  have hg0 : g 0 = 0 := by
    have hh : x 0 0 = 0 := by
      simpa only [Pi.zero_apply] using congrArg (fun y : ℕ → E => y 0) (hg.zero hr.le)
    simpa only [g, sub_zero] using hh
  obtain ⟨M, hM, hbig⟩ := (hT.differentiableAt (by norm_num)).isBigO_sub.exists_pos
  have hb : ∀ᶠ z : E in 𝓝 0, ‖T z‖ ≤ M * ‖z‖ := by
    simpa only [hT0, sub_zero] using hbig.bound
  obtain ⟨p, hp, hlocal⟩ := Metric.eventually_nhds_iff.mp hb
  let η : ℝ := min η₀ (min d (min (p / 4) (d / (4 * M * (‖P‖ + 1)))))
  have hη : 0 < η := by dsimp only [η]; positivity
  have hηd : η ≤ d := (min_le_right _ _).trans (min_le_left _ _)
  have hgker (α : E) (hα : P α = α) (hαd : ‖α‖ ≤ (2 * d) / 2) : P (g α) = 0 := by
    change P (x α 0 - α) = 0
    rw [P.map_sub, hg.coordinate α hα (by linarith), hα, sub_self]
  have hglip (α : E) (hα : P α = α) (hαd : ‖α‖ ≤ (2 * d) / 2)
      (β : E) (hβ : P β = β) (hβd : ‖β‖ ≤ (2 * d) / 2) :
      ‖g α - g β‖ ≤ H * (‖α‖ + ‖β‖) * ‖α - β‖ :=
    hquad α hα (by linarith) β hβ (by linarith)
  have hinv' (α : E) (hα : P α = α) (hαη : ‖α‖ ≤ η) :
      ‖P (T (α + g α))‖ ≤ (2 * d) / 2 ∧
      T (α + g α) - P (T (α + g α)) = g (P (T (α + g α))) := by
    have hαr : ‖α‖ ≤ r / 2 := (hαη.trans hηd).trans hdr
    have hx : ‖x α 0‖ ≤ 2 * ‖α‖ := by
      simpa only [pow_zero, mul_one] using hg.norm_le α hα hαr 0
    have hαp : ‖α‖ ≤ p / 4 :=
      hαη.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    have hxball : x α 0 ∈ ball (0 : E) p := by
      rw [mem_ball, dist_zero_right]
      linarith only [hx, hαp, hp]
    have hαM : ‖α‖ ≤ d / (4 * M * (‖P‖ + 1)) :=
      hαη.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
    have hsmall := (le_div_iff₀ (by positivity : 0 < 4 * M * (‖P‖ + 1))).mp hαM
    have hPt : ‖P (T (x α 0))‖ ≤ d := by
      have hn := P.le_opNorm (T (x α 0))
      have ht := hlocal hxball
      have hh := mul_le_mul_of_nonneg_left (ht.trans (mul_le_mul_of_nonneg_left hx hM.le)) (norm_nonneg P)
      have hmα : 0 ≤ M * ‖α‖ := mul_nonneg hM.le (norm_nonneg α)
      have hpMα : 0 ≤ ‖P‖ * (M * ‖α‖) := mul_nonneg (norm_nonneg P) hmα
      nlinarith only [hn, hh, hsmall, hmα, hpMα]
    have hga : α + g α = x α 0 := by dsimp only [g]; module
    rw [hga]
    refine ⟨by linarith, ?_⟩
    have hh := hinv α hα (hαη.trans (min_le_left _ _))
    have hhead : x (P (T (x α 0))) 0 = T (x α 0) :=
      congrArg (fun y : ℕ → E => y 0) hh.2
    change _ = x (P (T (x α 0))) 0 - P (T (x α 0))
    rw [hhead]
  obtain ⟨C, hC, s, hs, hsd, hbounds⟩ := exists_quadratic_graph_flattened_remainder_bound
    T hT hT0 A P hTA.fderiv hP hcomm g hg0 (by positivity : 0 < 2 * d) hH hη
      (by linarith) hgker hglip hinv'
  exact ⟨C, hC, s, hs, by linarith, hbounds⟩

end Euler2D

end
