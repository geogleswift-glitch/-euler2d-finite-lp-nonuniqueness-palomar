module

public import RequestProject.Euler.CircularFinitePrefixPlanarRows
public import RequestProject.Euler.CircularFiniteTorusInteractionRow

/-! The actual periodic part of an active prefix, summed without losing
the source label's own displacement or the self row's linear factor. -/

@[expose] public section

set_option maxHeartbeats 7000000
set_option maxRecDepth 4000

noncomputable section

open Complex Set MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D
namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

def finitePrefixTorusRowField (s A₀ b R ρ : ℝ) (N k : ℕ)
    {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T) (t : ℝ) (x : ℂ) : ℂ :=
  ∑ l : Fin (k + 1), actualTorusCorrectionVelocity (boxedComplexDensity
    (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N l) t)) x

theorem exists_uniform_finitePrefix_torus_contourLittle_rows :
    ∃ C : ℝ, 0 < C ∧ ∀ {η : ℝ≥0}, (η : ℝ) ≤ 1 →
      ∀ {s A₀ b R ρ c δ a L : ℝ},
      s ≤ 0 → 0 < A₀ → 0 < b → ∀ (hR : 0 < R), R ≤ 1 / 2 →
      ∀ (hρ : 0 < ρ), ρ ≤ 1 → 0 < a → a ≤ 1 / 16 →
      ∀ (N k j : ℕ) (hkN : k ≤ N),
      ∀ {f : Lp ℝ 2 μT} {T : ℝ},
      ∀ S : BoundedEulerParticleSystem f T, ∀ t ∈ Icc (0 : ℝ) T,
      ∀ G : P.FiniteOuterMaterialTube s R ρ N k S t c δ,
      ∀ q : Fin (k + 1) → ℝ, (∀ l, 0 ≤ q l) →
      (∀ (l : Fin (k + 1)) i,
        ‖contourParameterShiftC1 (G.shifts (finitePrefixForcingIndex hkN l, i))
          (G.contours (finitePrefixForcingIndex hkN l, i)) - G.reference (finitePrefixForcingIndex hkN l, i)‖ ≤
          radScale R ρ l * q l) →
      (∀ l : Fin (k + 1), (5 / 4 : ℝ) * radScale R ρ l ≤ a) →
      0 ≤ L → (L + 1) * radScale R ρ j ≤ a / 2 →
      ∀ W : LittleContourSpace η, ‖W‖ ≤ L * radScale R ρ j →
      ∃ Q : LittleContourSpace η,
        (∀ θ, LittleContourSpace.lift η Q θ =
          P.finitePrefixTorusRowField s A₀ b R ρ N k S t (LittleContourSpace.lift η W θ)) ∧
        ‖Q‖ / (ampScale A₀ b k * radScale R ρ j) ≤
          ∑ l : Fin (k + 1), if j ≤ (l : ℕ) then
            C * finiteTorusLabelLittleRowCoefficient (η : ℝ) L * R ^ 8 *
              b ^ (k - (l : ℕ)) * ρ ^ (6 * ((l : ℕ) - j)) * q l else
            C * finiteTorusLabelLittleRowCoefficient (η : ℝ) L * R ^ 8 *
              b ^ (k - (l : ℕ)) * ρ ^ (2 * (j - (l : ℕ))) * q l := by
  obtain ⟨C, hC, hrow⟩ := P.exists_uniform_finiteLabel_torus_contourLittle_rows
  refine ⟨C, hC, ?_⟩
  intro η hη s A₀ b R ρ c δ a L hs hA hb hR hRmax hρ hρ1 ha ha16
    N k j hkN f T S t ht G q hq0 hq hradius hL hgeom W hW
  classical
  have hAk : 0 < ampScale A₀ b k := by unfold ampScale; positivity
  have hrj : 0 < radScale R ρ j := radScale_pos hR hρ j
  have hden : 0 < ampScale A₀ b k * radScale R ρ j := mul_pos hAk hrj
  have hex (l : Fin (k + 1)) : ∃ Ql : LittleContourSpace η,
      (∀ θ, LittleContourSpace.lift η Ql θ = actualTorusCorrectionVelocity (boxedComplexDensity
        (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N l) t)) (LittleContourSpace.lift η W θ)) ∧
      ‖Ql‖ / (ampScale A₀ b k * radScale R ρ j) ≤ if j ≤ (l : ℕ) then
        C * finiteTorusLabelLittleRowCoefficient (η : ℝ) L * R ^ 8 *
          b ^ (k - (l : ℕ)) * ρ ^ (6 * ((l : ℕ) - j)) * q l else
        C * finiteTorusLabelLittleRowCoefficient (η : ℝ) L * R ^ 8 *
          b ^ (k - (l : ℕ)) * ρ ^ (2 * (j - (l : ℕ))) * q l := by
    let ll := finitePrefixForcingIndex hkN l
    have hlk : (ll : ℕ) ≤ k := Nat.le_of_lt_succ l.isLt
    let Gl := P.finiteOuterMaterialTubeRestrict G hlk
    obtain ⟨Ql, hQl, hupper, hlower⟩ := hrow hη hs hA hb hR hRmax hρ hρ1 ha ha16
      N k j ll hlk S t ht Gl (hq0 l) (hq l) (hradius l) hL hgeom W hW
    refine ⟨Ql, hQl, ?_⟩
    by_cases hjl : j ≤ (l : ℕ)
    · simpa only [hjl, if_true, ll, finitePrefixForcingIndex] using hupper hjl
    · simpa only [hjl, if_false, ll, finitePrefixForcingIndex] using
        hlower (Nat.le_of_lt (Nat.lt_of_not_ge hjl))
  choose Ql hQl hn using hex
  refine ⟨∑ l, Ql l, ?_, ?_⟩
  · intro θ
    change LittleContourSpace.eval η (θ : ContourCircle) (∑ l, Ql l) = _
    rw [map_sum]
    exact Finset.sum_congr rfl (fun l _ => hQl l θ)
  · calc
      _ ≤ (∑ l, ‖Ql l‖) / (ampScale A₀ b k * radScale R ρ j) :=
        div_le_div_of_nonneg_right (norm_sum_le _ _) hden.le
      _ = ∑ l, ‖Ql l‖ / (ampScale A₀ b k * radScale R ρ j) := Finset.sum_div _ _ _
      _ ≤ _ := Finset.sum_le_sum (fun l _ => hn l)

end CircularMaterialTransferProfile
end Euler2D

end
