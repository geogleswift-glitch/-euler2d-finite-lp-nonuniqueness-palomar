module

public import Mathlib
public import RequestProject.Euler.TorusCancellation

/-!
# Moment bounds for the inner cluster (Lemma `cs:lem:moment` and the scale part of
Lemma `cs:lem:exterior-remainder`)

With the scales of Definition `cs:def:labels`, `A_j = A₀ b^{-j}`, `r_j = R ρ^j`,
`0 < b < 1/4`, `0 < ρ < b/2`, the labels `ω_j`, `k < j ≤ N`, have
`‖ω_j‖₁ ≤ C_w A_j r_j²`. If they are all supported in `B̄_S` with
`S = C_b r_k ρ (1 + D)` (the conclusion of Lemma `cs:supportlemma`), then

* `fourth_moment_confinement` (**Lemma `cs:lem:moment`**): both the absolute fourth moment
  `M^abs_{4,>k} = ∫ |z|⁴ ∑ |ω_j|` and the signed moment `|M_{4,>k}| = |∫ \bar z⁴ ∑ ω_j|` are at
  most `(2 C_w C_b⁴ / b) A_k r_k⁶ ρ⁶ (1 + D)⁴`;
* `exterior_remainder_at_scale` (second half of **Lemma `cs:lem:exterior-remainder`**): at
  `|x| ≥ c r_k` (and `|x| ≥ 2S`) the exterior multipole remainder of the cluster is at most
  `C A_k r_k ρ¹⁰ (1 + D)⁸`, with `C` independent of `k` and `N`.

The key scalar fact is the geometric mass bound `∑_{j > k} A_j r_j² ≤ (2/b) ρ² A_k r_k²`
(`inner_mass_sum`).
-/

@[expose] public section

open MeasureTheory Complex ComplexConjugate Metric Set Filter

namespace Euler2D

/-- The amplitude scale `A_j = A₀ b^{-j}`. -/
noncomputable def ampScale (A₀ b : ℝ) (j : ℕ) : ℝ := A₀ / b ^ j

/-- The length scale `r_j = R ρ^j`. -/
noncomputable def radScale (R ρ : ℝ) (j : ℕ) : ℝ := R * ρ ^ j

/-- Geometric mass bound: `∑_{k < j ≤ N} A_j r_j² ≤ (2/b) ρ² A_k r_k²`. -/
lemma inner_mass_sum {A₀ b R ρ : ℝ} (hA₀ : 0 ≤ A₀) (hb0 : 0 < b) (hb : b < 1 / 4)
    (hρ0 : 0 < ρ) (hρ : ρ < b / 2) (k N : ℕ) :
    ∑ j ∈ Finset.Ioc k N, ampScale A₀ b j * radScale R ρ j ^ 2
      ≤ 2 / b * ρ ^ 2 * (ampScale A₀ b k * radScale R ρ k ^ 2) := by
  set q := ρ ^ 2 / b with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q ≤ 1 / 2 := by rw [hq, div_le_iff₀ hb0]; nlinarith
  have hterm : ∀ j, k ≤ j → ampScale A₀ b j * radScale R ρ j ^ 2
      = (ampScale A₀ b k * radScale R ρ k ^ 2) * q ^ (j - k) := by
    intro j hj
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hj
    simp only [ampScale, radScale, hq, Nat.add_sub_cancel_left]
    rw [div_pow, pow_add, pow_add]; field_simp; ring
  rw [Finset.sum_congr rfl (fun j hj => hterm j (Finset.mem_Ioc.mp hj).1.le), ← Finset.mul_sum]
  set Ck := ampScale A₀ b k * radScale R ρ k ^ 2 with hCkdef
  have hCk : 0 ≤ Ck := by simp only [hCkdef, ampScale]; positivity
  have hgeo : ∑ j ∈ Finset.Ioc k N, q ^ (j - k) ≤ 2 * q := by
    rw [← Finset.Ico_add_one_add_one_eq_Ioc, Finset.sum_Ico_eq_sum_range]
    have e : ∀ m, q ^ (k + 1 + m - k) = q * q ^ m := by
      intro m; rw [show k + 1 + m - k = m + 1 by omega, pow_succ]; ring
    simp only [e, ← Finset.mul_sum]
    have hs : ∑ m ∈ Finset.range (N + 1 - (k + 1)), q ^ m ≤ (1 - q)⁻¹ := by
      rw [← tsum_geometric_of_lt_one hq0 (by linarith)]
      exact Summable.sum_le_tsum _ (fun i _ => by positivity)
        (summable_geometric_of_lt_one hq0 (by linarith))
    have h1q : (1 - q)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    calc q * ∑ m ∈ Finset.range (N + 1 - (k + 1)), q ^ m ≤ q * (1 - q)⁻¹ := by gcongr
      _ ≤ q * 2 := by gcongr
      _ = 2 * q := by ring
  calc Ck * ∑ j ∈ Finset.Ioc k N, q ^ (j - k) ≤ Ck * (2 * q) := by gcongr
    _ = 2 / b * ρ ^ 2 * Ck := by rw [hq]; ring

/-- Moments of a density supported in `B̄_S`: `∫ |z|ᵐ |ω| ≤ Sᵐ ∫ |ω|`. -/
lemma moment_le_of_supp {ω : ℂ → ℝ} {S : ℝ} (hω : Integrable ω)
    (hsupp : ∀ z, S < ‖z‖ → ω z = 0) (m : ℕ) :
    ∫ z, ‖z‖ ^ m * |ω z| ≤ S ^ m * ∫ z, |ω z| := by
  rw [← integral_const_mul]
  refine integral_mono (integrable_norm_pow_mul_of_supp hω hsupp m) (hω.abs.const_mul _)
    fun z => ?_
  by_cases hz : ω z = 0
  · simp [hz]
  have hzS : ‖z‖ ≤ S := not_lt.mp fun h => hz (hsupp z h)
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hzS m) (abs_nonneg _)

/-- The `m`-th absolute moment of the inner cluster. -/
lemma cluster_moment_bound {A₀ b R ρ Cw S : ℝ} (hA₀ : 0 ≤ A₀) (hb0 : 0 < b) (hb : b < 1 / 4)
    (hρ0 : 0 < ρ) (hρ : ρ < b / 2) (hCw : 0 ≤ Cw) {k N : ℕ} (ω : ℕ → ℂ → ℝ)
    (hint : ∀ j ∈ Finset.Ioc k N, Integrable (ω j))
    (hL1 : ∀ j ∈ Finset.Ioc k N, ∫ z, |ω j z| ≤ Cw * ampScale A₀ b j * radScale R ρ j ^ 2)
    (hsupp : ∀ j ∈ Finset.Ioc k N, ∀ z, S < ‖z‖ → ω j z = 0) (hS : 0 ≤ S) (m : ℕ) :
    ∫ z, ‖z‖ ^ m * ∑ j ∈ Finset.Ioc k N, |ω j z|
      ≤ S ^ m * (Cw * (2 / b * ρ ^ 2 * (ampScale A₀ b k * radScale R ρ k ^ 2))) := by
  simp_rw [Finset.mul_sum]
  rw [integral_finset_sum _
    (fun j hj => integrable_norm_pow_mul_of_supp (hint j hj) (hsupp j hj) m)]
  calc ∑ j ∈ Finset.Ioc k N, ∫ z, ‖z‖ ^ m * |ω j z|
      ≤ ∑ j ∈ Finset.Ioc k N, S ^ m * (Cw * (ampScale A₀ b j * radScale R ρ j ^ 2)) := by
        refine Finset.sum_le_sum fun j hj => ?_
        refine (moment_le_of_supp (hint j hj) (hsupp j hj) m).trans ?_
        exact (mul_le_mul_of_nonneg_left (hL1 j hj) (pow_nonneg hS m)).trans_eq (by ring)
    _ = S ^ m * (Cw * ∑ j ∈ Finset.Ioc k N, ampScale A₀ b j * radScale R ρ j ^ 2) := by
        rw [Finset.mul_sum, Finset.mul_sum]
    _ ≤ _ := by
        gcongr
        exact inner_mass_sum hA₀ hb0 hb hρ0 hρ k N

/-- **Lemma `cs:lem:moment`** (*Fourth-moment confinement estimate*). Under the label norms
`‖ω_j‖₁ ≤ C_w A_j r_j²` and the support conclusion `supp ω_j ⊂ B̄_{C_b r_k ρ (1+D)}` of
Lemma `cs:supportlemma`, both the absolute and the signed fourth moments of the inner cluster are
at most `(2 C_w C_b⁴ / b) A_k r_k⁶ ρ⁶ (1 + D)⁴`. -/
theorem fourth_moment_confinement {A₀ b R ρ Cw Cb D : ℝ} (hA₀ : 0 ≤ A₀) (hb0 : 0 < b)
    (hb : b < 1 / 4) (hρ0 : 0 < ρ) (hρ : ρ < b / 2) (hCw : 0 ≤ Cw) {k N : ℕ}
    (ω : ℕ → ℂ → ℝ) (hint : ∀ j ∈ Finset.Ioc k N, Integrable (ω j))
    (hL1 : ∀ j ∈ Finset.Ioc k N, ∫ z, |ω j z| ≤ Cw * ampScale A₀ b j * radScale R ρ j ^ 2)
    (hsupp : ∀ j ∈ Finset.Ioc k N, ∀ z,
      Cb * radScale R ρ k * ρ * (1 + D) < ‖z‖ → ω j z = 0) :
    (∫ z, ‖z‖ ^ 4 * ∑ j ∈ Finset.Ioc k N, |ω j z|
      ≤ 2 * Cw * Cb ^ 4 / b * ampScale A₀ b k * radScale R ρ k ^ 6 * ρ ^ 6 * (1 + D) ^ 4) ∧
    ‖∫ z, ((∑ j ∈ Finset.Ioc k N, ω j z : ℝ) : ℂ) * conj z ^ 4‖
      ≤ 2 * Cw * Cb ^ 4 / b * ampScale A₀ b k * radScale R ρ k ^ 6 * ρ ^ 6 * (1 + D) ^ 4 := by
  set S := Cb * radScale R ρ k * ρ * (1 + D) with hSdef
  have hsupp' : ∀ j ∈ Finset.Ioc k N, ∀ z, |S| < ‖z‖ → ω j z = 0 :=
    fun j hj z hz => hsupp j hj z ((le_abs_self S).trans_lt hz)
  have hmom := cluster_moment_bound hA₀ hb0 hb hρ0 hρ hCw ω hint hL1 hsupp' (abs_nonneg S) 4
  have heq : |S| ^ 4 * (Cw * (2 / b * ρ ^ 2 * (ampScale A₀ b k * radScale R ρ k ^ 2)))
      = 2 * Cw * Cb ^ 4 / b * ampScale A₀ b k * radScale R ρ k ^ 6 * ρ ^ 6 * (1 + D) ^ 4 := by
    rw [Even.pow_abs ⟨2, rfl⟩ S, hSdef]; ring
  rw [heq] at hmom
  refine ⟨hmom, (norm_integral_le_integral_norm _).trans (le_trans ?_ hmom)⟩
  have hint4 : Integrable (fun z => ‖z‖ ^ 4 * ∑ j ∈ Finset.Ioc k N, |ω j z|) := by
    simp_rw [Finset.mul_sum]
    exact integrable_finset_sum _
      (fun j hj => integrable_norm_pow_mul_of_supp (hint j hj) (hsupp' j hj) 4)
  refine integral_mono_of_nonneg (Eventually.of_forall fun z => norm_nonneg _) hint4
    (Eventually.of_forall fun z => ?_)
  simp only
  rw [norm_mul, norm_real, norm_pow, Complex.norm_conj, Real.norm_eq_abs, mul_comm]
  exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)

/-- **Lemma `cs:lem:exterior-remainder`**, second part. Let the inner labels `ω_j`,
`k < j ≤ N`, be integrable, fourfold symmetric, of zero mass, with
`‖ω_j‖₁ ≤ C_w A_j r_j²` and supported in `B̄_S`, `S = C_b r_k ρ (1+D)`. At any point `x` with
`|x| ≥ c r_k` and `|x| ≥ 2|S|`, the velocity of the cluster `ζ = ∑ ω_j` differs from its
fourth-moment field by at most `C A_k r_k ρ¹⁰ (1+D)⁸` with
`C = (8/(15π)) · 2 C_w C_b⁸ / (b c⁹)`, independent of `k` and `N`. -/
theorem exterior_remainder_at_scale {A₀ b R ρ Cw Cb D c : ℝ} (hA₀ : 0 ≤ A₀) (hb0 : 0 < b)
    (hb : b < 1 / 4) (hρ0 : 0 < ρ) (hρ : ρ < b / 2) (hCw : 0 ≤ Cw) (hR : 0 < R) (hc : 0 < c)
    {k N : ℕ} (ω : ℕ → ℂ → ℝ) (hint : ∀ j ∈ Finset.Ioc k N, Integrable (ω j))
    (hL1 : ∀ j ∈ Finset.Ioc k N, ∫ z, |ω j z| ≤ Cw * ampScale A₀ b j * radScale R ρ j ^ 2)
    (hmass : ∀ j ∈ Finset.Ioc k N, ∫ z, ω j z = 0)
    (hsym : ∀ j ∈ Finset.Ioc k N, ∀ z, ω j (I * z) = ω j z)
    (hsupp : ∀ j ∈ Finset.Ioc k N, ∀ z,
      Cb * radScale R ρ k * ρ * (1 + D) < ‖z‖ → ω j z = 0)
    {x : ℂ} (hx : c * radScale R ρ k ≤ ‖x‖)
    (hx2 : 2 * |Cb * radScale R ρ k * ρ * (1 + D)| ≤ ‖x‖) :
    ‖velocityC (fun z => ∑ j ∈ Finset.Ioc k N, ω j z) x
        - I / (2 * Real.pi) * momentN (fun z => ∑ j ∈ Finset.Ioc k N, ω j z) 4 * (conj x ^ 5)⁻¹‖
      ≤ 8 / (15 * Real.pi) * (2 * Cw * Cb ^ 8 / (b * c ^ 9)) * ampScale A₀ b k *
          radScale R ρ k * ρ ^ 10 * (1 + D) ^ 8 := by
  set S := Cb * radScale R ρ k * ρ * (1 + D) with hSdef
  set ζ : ℂ → ℝ := fun z => ∑ j ∈ Finset.Ioc k N, ω j z with hζdef
  have hrk : 0 < radScale R ρ k := by simp only [radScale]; positivity
  have hxpos : 0 < ‖x‖ := lt_of_lt_of_le (by positivity) hx
  have hx0 : x ≠ 0 := norm_pos_iff.mp hxpos
  have hsupp' : ∀ j ∈ Finset.Ioc k N, ∀ z, |S| < ‖z‖ → ω j z = 0 :=
    fun j hj z hz => hsupp j hj z ((le_abs_self S).trans_lt hz)
  have hζint : Integrable ζ := integrable_finset_sum _ hint
  have hζsupp : ∀ z, |S| < ‖z‖ → ζ z = 0 := fun z hz =>
    Finset.sum_eq_zero fun j hj => hsupp' j hj z hz
  have hζmass : ∫ z, ζ z = 0 := by
    rw [hζdef, integral_finset_sum _ hint]
    exact Finset.sum_eq_zero hmass
  have hζsym : ∀ z, ζ (I * z) = ζ z := fun z =>
    Finset.sum_congr rfl fun j hj => hsym j hj z
  have hrem := exterior_multipole_remainder hζint hζsupp hζmass hζsym hx0 hx2
  have hmom := cluster_moment_bound hA₀ hb0 hb hρ0 hρ hCw ω hint hL1 hsupp' (abs_nonneg S) 8
  have h8 : ∫ w, ‖w‖ ^ 8 * |ζ w| ≤ ∫ z, ‖z‖ ^ 8 * ∑ j ∈ Finset.Ioc k N, |ω j z| := by
    have hint8 : Integrable (fun z => ‖z‖ ^ 8 * ∑ j ∈ Finset.Ioc k N, |ω j z|) := by
      simp_rw [Finset.mul_sum]
      exact integrable_finset_sum _
        (fun j hj => integrable_norm_pow_mul_of_supp (hint j hj) (hsupp' j hj) 8)
    refine integral_mono (integrable_norm_pow_mul_of_supp hζint hζsupp 8) hint8 fun z => ?_
    exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
  set M := |S| ^ 8 * (Cw * (2 / b * ρ ^ 2 * (ampScale A₀ b k * radScale R ρ k ^ 2))) with hMdef
  have hM0 : 0 ≤ M := by simp only [hMdef, ampScale]; positivity
  have hx9 : (c * radScale R ρ k) ^ 9 ≤ ‖x‖ ^ 9 := pow_le_pow_left₀ (by positivity) hx 9
  calc _ ≤ 8 / (15 * Real.pi) * (∫ w, ‖w‖ ^ 8 * |ζ w|) / ‖x‖ ^ 9 := hrem
    _ ≤ 8 / (15 * Real.pi) * M / (c * radScale R ρ k) ^ 9 := by
        gcongr
        exact h8.trans hmom
    _ = _ := by
        rw [hMdef, Even.pow_abs ⟨4, rfl⟩ S, hSdef]
        field_simp
        ring

end Euler2D
