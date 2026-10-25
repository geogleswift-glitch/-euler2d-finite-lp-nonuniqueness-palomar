module

public import RequestProject.Euler.CircularRetardedInteractionRows
public import RequestProject.Euler.CircularFinitePrefixPhysicalForcing

/-! Summing the real planar interaction rows of one actual active
prefix constructs its true Little forcing and retains every source's
own deviation. The actual deep cluster is kept separate. -/

@[expose] public section

set_option maxHeartbeats 7000000
set_option maxRecDepth 4000

noncomputable section

open Complex Set MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

def finitePrefixForcingIndex {N k : ℕ} (hkN : k ≤ N) (l : Fin (k + 1)) : Fin (N + 1) :=
  ⟨l, l.isLt.trans_le (Nat.succ_le_succ hkN)⟩

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

def finitePrefixPlanarRowField (s A₀ b R ρ : ℝ) (N k j : ℕ) (hkN : k ≤ N)
    {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T) (t : ℝ) (x : ℂ) : ℂ :=
  ∑ l : Fin (k + 1), if (l : ℕ) < j then
    velocityC (P.finiteOuterLabelComplexPerturbation s A₀ b R ρ N (finitePrefixForcingIndex hkN l) S t) x
  else if j < (l : ℕ) then velocityC (boxedComplexDensity
    (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N l) t)) x else 0

theorem exists_finitePrefix_planar_contourLittle_rows
    {η : ℝ≥0} (hη : (η : ℝ) ≤ 1) {s A₀ b R ρ c B δ e L : ℝ}
    (hs : s ≤ 0) (hA : 0 < A₀) (hb : 0 < b)
    (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (N k j : ℕ) (hkN : k ≤ N) (hjk : j ≤ k)
    {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T)
    (G : P.FiniteOuterMaterialTube s R ρ N k S t c δ)
    (q : Fin (k + 1) → ℝ) (hq0 : ∀ l, 0 ≤ q l)
    (hq : ∀ (l : Fin (k + 1)) i,
      ‖contourParameterShiftC1 (G.shifts (finitePrefixForcingIndex hkN l, i))
        (G.contours (finitePrefixForcingIndex hkN l, i)) - G.reference (finitePrefixForcingIndex hkN l, i)‖ ≤
        radScale R ρ l * q l)
    (hc : 0 < c) (hB : 0 < B) (he : 0 < e)
    (hsepU : ∀ l : Fin (k + 1), j < (l : ℕ) → 10 * radScale R ρ l ≤ e * radScale R ρ j)
    (hsepL : ∀ l : Fin (k + 1), (l : ℕ) < j → 8 * (B * radScale R ρ j) ≤ c * radScale R ρ l)
    (W : LittleContourSpace η)
    (hWmax : ∀ x, ‖ContourC1Space.toBCF η W.val x‖ ≤ B * radScale R ρ j)
    (hWmin : ∀ x, e * radScale R ρ j ≤ ‖ContourC1Space.toBCF η W.val x‖)
    (hL : ‖W‖ ≤ radScale R ρ j * L) :
    ∃ Q : LittleContourSpace η,
      (∀ θ, LittleContourSpace.lift η Q θ =
        P.finitePrefixPlanarRowField s A₀ b R ρ N k j hkN S t (LittleContourSpace.lift η W θ)) ∧
      ‖Q‖ / (ampScale A₀ b k * radScale R ρ j) ≤
        (∑ l : Fin (k + 1), if (l : ℕ) < j then
          finiteOuterLabelLittleRowCoefficient (η : ℝ) c B L * b ^ (k - (l : ℕ)) *
            ρ ^ (2 * (j - (l : ℕ))) * q l else if j < (l : ℕ) then
          finiteInnerLabelLittleRowCoefficient (η : ℝ) e L * b ^ (k - (l : ℕ)) *
            ρ ^ (6 * ((l : ℕ) - j)) * q l else 0) := by
  classical
  have hAk : 0 < ampScale A₀ b k := by unfold ampScale; positivity
  have hrj : 0 < radScale R ρ j := radScale_pos hR hρ j
  let den := ampScale A₀ b k * radScale R ρ j
  have hden : 0 < den := mul_pos hAk hrj
  have hex (l : Fin (k + 1)) : ∃ Ql : LittleContourSpace η,
      (∀ θ, LittleContourSpace.lift η Ql θ =
        if (l : ℕ) < j then velocityC (P.finiteOuterLabelComplexPerturbation s A₀ b R ρ N
          (finitePrefixForcingIndex hkN l) S t) (LittleContourSpace.lift η W θ)
        else if j < (l : ℕ) then velocityC (boxedComplexDensity
          (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N l) t)) (LittleContourSpace.lift η W θ) else 0) ∧
      ‖Ql‖ / den ≤ if (l : ℕ) < j then
        finiteOuterLabelLittleRowCoefficient (η : ℝ) c B L * b ^ (k - (l : ℕ)) *
          ρ ^ (2 * (j - (l : ℕ))) * q l else if j < (l : ℕ) then
        finiteInnerLabelLittleRowCoefficient (η : ℝ) e L * b ^ (k - (l : ℕ)) *
          ρ ^ (6 * ((l : ℕ) - j)) * q l else 0 := by
    let ll := finitePrefixForcingIndex hkN l
    have hlk : (ll : ℕ) ≤ k := Nat.le_of_lt_succ l.isLt
    let Gl := P.finiteOuterMaterialTubeRestrict G hlk
    by_cases hlj : (l : ℕ) < j
    · obtain ⟨Ql, hQl, hn⟩ := P.exists_finiteOuterLabel_contourLittle_lowerRow hη hs hA hb hR hRmax hρ hρ1
        N k j ll hlj.le hlk S t ht Gl (hq l) hc hB (hsepL l hlj) W hWmax hL
      refine ⟨Ql, ?_, ?_⟩
      · intro θ; simpa only [hlj, if_true] using hQl θ
      · simpa only [hlj, if_true] using hn
    · by_cases hjl : j < (l : ℕ)
      · obtain ⟨Ql, hQl, hn⟩ := P.exists_finiteInnerLabel_contourLittle_upperRow hη hs hA hb hR hRmax hρ hρ1
          N k j ll hjl.le hlk S t ht Gl (hq0 l) (hq l) he (hsepU l hjl) W hWmin hL
        refine ⟨Ql, ?_, ?_⟩
        · intro θ; simpa only [hlj, if_false, hjl, if_true] using hQl θ
        · simpa only [hlj, if_false, hjl, if_true] using hn
      · refine ⟨0, ?_, ?_⟩
        · intro θ; simp [hlj, hjl]
        · simp [hlj, hjl]
  choose Ql hQl hn using hex
  refine ⟨∑ l, Ql l, ?_, ?_⟩
  · intro θ
    change LittleContourSpace.eval η (θ : ContourCircle) (∑ l, Ql l) = _
    rw [map_sum]
    exact Finset.sum_congr rfl (fun l _ => hQl l θ)
  · calc
      _ ≤ (∑ l, ‖Ql l‖) / den := div_le_div_of_nonneg_right (norm_sum_le _ _) hden.le
      _ = ∑ l, ‖Ql l‖ / den := Finset.sum_div _ _ _
      _ ≤ _ := Finset.sum_le_sum (fun l _ => hn l)

end CircularMaterialTransferProfile
end Euler2D

end
