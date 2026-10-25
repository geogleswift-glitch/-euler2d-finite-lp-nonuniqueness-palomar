module

public import RequestProject.Euler.BanachQuadraticRemainderDifference

/-! Flattening estimates use only the true C² return map, graph
invariance, and the proved quadratic Lipschitz graph bound. No C³
regularity of the graph is required. -/

@[expose] public section

set_option maxHeartbeats 5000000

noncomputable section

open Set Filter Topology Metric
open scoped ContDiff

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem exists_quadratic_graph_flattened_remainder_bound
    (F : E → E) (hf : ContDiffAt ℝ 2 F 0) (hF0 : F 0 = 0)
    (L P : E →L[ℝ] E) (hderiv : fderiv ℝ F 0 = L)
    (hP : ∀ v, P (P v) = P v) (hcomm : L.comp P = P.comp L)
    (g : E → E) (hg0 : g 0 = 0) {r H η : ℝ}
    (hr : 0 < r) (hH : 0 < H) (hη : 0 < η) (hηr : η ≤ r / 2)
    (hgker : ∀ α, P α = α → ‖α‖ ≤ r / 2 → P (g α) = 0)
    (hglip : ∀ α, P α = α → ‖α‖ ≤ r / 2 → ∀ β, P β = β → ‖β‖ ≤ r / 2 →
      ‖g α - g β‖ ≤ H * (‖α‖ + ‖β‖) * ‖α - β‖)
    (hinv : ∀ α, P α = α → ‖α‖ ≤ η →
      ‖P (F (α + g α))‖ ≤ r / 2 ∧
      F (α + g α) - P (F (α + g α)) = g (P (F (α + g α)))) :
    ∃ C > 0, ∃ s > 0, s ≤ r / 2 ∧ ∀ α w,
      P α = α → P w = 0 → ‖α‖ + ‖w‖ ≤ s →
      let z := α + g α + w
      ‖P (F z) - L α‖ ≤ C * (‖α‖ + ‖w‖) ^ 2 ∧
      ‖(F z - P (F z)) - g (P (F z)) - L w‖ ≤
        C * (‖α‖ + ‖w‖) * ‖w‖ := by
  obtain ⟨B, hB, q, hq, hquad⟩ := exists_banachLocalRemainder_quadratic_difference_bound hf
  let R := banachLocalRemainder F
  let K := 1 + H * r
  let M := ‖L‖ + B * q
  let D := (‖P‖ + 1) * (M + 1)
  have hK1 : 1 ≤ K := by dsimp only [K]; nlinarith
  have hK : 0 < K := zero_lt_one.trans_le hK1
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hD : 0 < D := by dsimp only [D]; positivity
  let s := min η (min (r / 2) (min (q / (2 * K)) (r / (4 * D * K))))
  have hs : 0 < s := by dsimp only [s]; positivity
  have hsr : s ≤ r / 2 := (min_le_right _ _).trans (min_le_left _ _)
  let Cf := ‖P‖ * B * K ^ 2
  let Cw := (1 + ‖P‖ + H * r * ‖P‖) * (2 * B * K)
  have hCf : 0 ≤ Cf := by dsimp only [Cf]; positivity
  have hCw : 0 ≤ Cw := by dsimp only [Cw]; positivity
  refine ⟨Cf + Cw + 1, by positivity, s, hs, hsr, ?_⟩
  intro α w hα hw hsize
  let zg := α + g α
  let z := zg + w
  let A := P (F z)
  let A₀ := P (F zg)
  let size := ‖α‖ + ‖w‖
  have hsize0 : 0 ≤ size := by dsimp only [size]; positivity
  have hαs : ‖α‖ ≤ s := le_trans (le_add_of_nonneg_right (norm_nonneg w)) hsize
  have hαr : ‖α‖ ≤ r / 2 := hαs.trans hsr
  have hαη : ‖α‖ ≤ η := hαs.trans (min_le_left _ _)
  have hgr : ‖g α‖ ≤ H * ‖α‖ ^ 2 := by
    have hh := hglip α hα hαr 0 (map_zero P) (by simpa using (half_pos hr).le)
    simpa only [hg0, sub_zero, norm_zero, add_zero, pow_two, mul_assoc] using hh
  have hzgα : ‖zg‖ ≤ K * ‖α‖ := by
    have har : ‖α‖ ≤ r := hαr.trans (by linarith)
    have hh : H * ‖α‖ ^ 2 ≤ H * (r * ‖α‖) :=
      mul_le_mul_of_nonneg_left (by nlinarith [norm_nonneg α]) hH.le
    calc
      _ ≤ ‖α‖ + ‖g α‖ := norm_add_le _ _
      _ ≤ ‖α‖ + H * ‖α‖ ^ 2 := add_le_add le_rfl hgr
      _ ≤ K * ‖α‖ := by dsimp only [K]; nlinarith
  have hzg : ‖zg‖ ≤ K * size := hzgα.trans
    (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (norm_nonneg w)) hK.le)
  have hz : ‖z‖ ≤ K * size := by
    calc
      _ ≤ ‖zg‖ + ‖w‖ := norm_add_le _ _
      _ ≤ K * ‖α‖ + K * ‖w‖ := add_le_add hzgα
        (by nlinarith [norm_nonneg w])
      _ = _ := by dsimp only [size]; ring
  have hsizeq : size ≤ q / (2 * K) :=
    hsize.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hsizeD : size ≤ r / (4 * D * K) :=
    hsize.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hKq : K * size ≤ q := by
    have hh := (le_div_iff₀ (by positivity : 0 < 2 * K)).mp hsizeq
    nlinarith
  have hDK : D * K * size ≤ r / 4 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 4 * D * K)).mp hsizeD
    nlinarith
  have hzq : z ∈ closedBall (0 : E) q := by
    simpa only [mem_closedBall, dist_zero_right] using hz.trans hKq
  have hzgq : zg ∈ closedBall (0 : E) q := by
    simpa only [mem_closedBall, dist_zero_right] using hzg.trans hKq
  have hR0 : R 0 = 0 := banachLocalRemainder_zero hF0
  have hRsmall (t : E) (ht : t ∈ closedBall (0 : E) q) : ‖R t‖ ≤ B * ‖t‖ ^ 2 := by
    have hh := hquad t ht 0 (mem_closedBall_self hq.le)
    simpa only [banachLocalRemainder_zero hF0, sub_zero, norm_zero, add_zero, pow_two, mul_assoc] using hh
  have hdecomp (t : E) : F t = L t + R t := by
    dsimp only [R, banachLocalRemainder]
    rw [hderiv]
    abel
  have hFbound (t : E) (ht : t ∈ closedBall (0 : E) q) : ‖F t‖ ≤ M * ‖t‖ := by
    have htq : ‖t‖ ≤ q := by simpa only [mem_closedBall, dist_zero_right] using ht
    have hh : B * ‖t‖ ^ 2 ≤ B * (q * ‖t‖) :=
      mul_le_mul_of_nonneg_left (by nlinarith [norm_nonneg t]) hB.le
    calc
      _ = ‖L t + R t‖ := congrArg norm (hdecomp t)
      _ ≤ ‖L t‖ + ‖R t‖ := norm_add_le _ _
      _ ≤ ‖L‖ * ‖t‖ + B * ‖t‖ ^ 2 := add_le_add (L.le_opNorm t) (hRsmall t ht)
      _ ≤ M * ‖t‖ := by dsimp only [M]; nlinarith
  have hPM : ‖P‖ * M ≤ D := by dsimp only [D]; nlinarith [norm_nonneg P]
  have hA : ‖A‖ ≤ r / 2 := by
    calc
      _ ≤ ‖P‖ * ‖F z‖ := P.le_opNorm _
      _ ≤ ‖P‖ * (M * ‖z‖) := mul_le_mul_of_nonneg_left (hFbound z hzq) (norm_nonneg P)
      _ ≤ ‖P‖ * (M * (K * size)) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hz hM) (norm_nonneg P)
      _ = (‖P‖ * M) * (K * size) := by ring
      _ ≤ D * (K * size) := mul_le_mul_of_nonneg_right hPM (mul_nonneg hK.le hsize0)
      _ ≤ r / 2 := by nlinarith
  have hinvα := hinv α hα hαη
  have hA₀ : ‖A₀‖ ≤ r / 2 := hinvα.1
  have hginv : F zg - A₀ = g A₀ := hinvα.2
  have hPL (t : E) : P (L t) = L (P t) :=
    (congrArg (fun Q : E →L[ℝ] E => Q t) hcomm).symm
  have hPLw : P (L w) = 0 := by rw [hPL, hw, map_zero]
  have hPz : P z = α := by
    dsimp only [z, zg]
    rw [P.map_add, P.map_add, hα, hgker α hα hαr, hw, add_zero, add_zero]
  have hAformula : A = L α + P (R z) := by
    change P (F z) = _
    rw [hdecomp, P.map_add, hPL, hPz]
  have hFdiff : F z - F zg = L w + (R z - R zg) := by
    rw [hdecomp z, hdecomp zg]
    change L (zg + w) + R z - (L zg + R zg) = _
    rw [L.map_add]
    abel
  have hAdiff : A - A₀ = P (R z - R zg) := by
    change P (F z) - P (F zg) = _
    rw [← P.map_sub, hFdiff, P.map_add, hPLw, zero_add]
  have hRdiff : ‖R z - R zg‖ ≤ (2 * B * K) * size * ‖w‖ := by
    have hzw : z - zg = w := by dsimp only [z]; abel
    calc
      _ ≤ B * (‖z‖ + ‖zg‖) * ‖z - zg‖ := hquad z hzq zg hzgq
      _ ≤ B * (K * size + K * size) * ‖z - zg‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (add_le_add hz hzg) hB.le) (norm_nonneg _)
      _ = _ := by rw [hzw]; ring
  have hfg : ‖A - L α‖ ≤ Cf * size ^ 2 := by
    rw [hAformula, add_sub_cancel_left]
    have hsq : ‖z‖ ^ 2 ≤ (K * size) ^ 2 := by nlinarith [norm_nonneg z]
    calc
      _ ≤ ‖P‖ * ‖R z‖ := P.le_opNorm _
      _ ≤ ‖P‖ * (B * ‖z‖ ^ 2) := mul_le_mul_of_nonneg_left (hRsmall z hzq) (norm_nonneg P)
      _ ≤ ‖P‖ * (B * (K * size) ^ 2) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hsq hB.le) (norm_nonneg P)
      _ = _ := by dsimp only [Cf]; ring
  have hgd : ‖g A - g A₀‖ ≤ (H * r * ‖P‖) * ‖R z - R zg‖ := by
    have hh := hglip A (hP _) hA A₀ (hP _) hA₀
    calc
      _ ≤ H * (‖A‖ + ‖A₀‖) * ‖A - A₀‖ := hh
      _ ≤ H * r * ‖A - A₀‖ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by linarith : ‖A‖ + ‖A₀‖ ≤ r) hH.le) (norm_nonneg _)
      _ ≤ H * r * (‖P‖ * ‖R z - R zg‖) := mul_le_mul_of_nonneg_left
        (by rw [hAdiff]; exact P.le_opNorm _) (mul_nonneg hH.le hr.le)
      _ = _ := by ring
  have hflat : (F z - A) - g A - L w =
      (R z - R zg) - P (R z - R zg) - (g A - g A₀) := by
    calc
      _ = (F z - F zg - L w) - (A - A₀) - (g A - (F zg - A₀)) := by abel
      _ = _ := by rw [hFdiff, hAdiff, hginv]; abel
  have hwg : ‖(F z - A) - g A - L w‖ ≤ Cw * size * ‖w‖ := by
    rw [hflat]
    calc
      _ ≤ ‖R z - R zg‖ + ‖P (R z - R zg)‖ + ‖g A - g A₀‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ ‖R z - R zg‖ + ‖P‖ * ‖R z - R zg‖ +
          (H * r * ‖P‖) * ‖R z - R zg‖ :=
        add_le_add (add_le_add le_rfl (P.le_opNorm _)) hgd
      _ = (1 + ‖P‖ + H * r * ‖P‖) * ‖R z - R zg‖ := by ring
      _ ≤ (1 + ‖P‖ + H * r * ‖P‖) * ((2 * B * K) * size * ‖w‖) :=
        mul_le_mul_of_nonneg_left hRdiff (by positivity)
      _ = _ := by dsimp only [Cw]; ring
  change ‖A - L α‖ ≤ (Cf + Cw + 1) * size ^ 2 ∧
    ‖(F z - A) - g A - L w‖ ≤ (Cf + Cw + 1) * size * ‖w‖
  constructor
  · exact hfg.trans (mul_le_mul_of_nonneg_right (by linarith : Cf ≤ Cf + Cw + 1) (sq_nonneg _))
  · exact hwg.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith : Cw ≤ Cf + Cw + 1) hsize0) (norm_nonneg _))

end Euler2D

end
