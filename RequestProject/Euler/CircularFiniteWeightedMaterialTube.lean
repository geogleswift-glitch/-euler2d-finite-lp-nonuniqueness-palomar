module

public import RequestProject.Euler.CircularFinitePrefixMaterialTube
public import RequestProject.Euler.CircularRetardedLabelDeviation
public import RequestProject.Euler.CircularFinitePrefixPlanarRows
public import RequestProject.Euler.WeightedPrefixGeometry

/-! The same actual canonical prefix supplies its real material tube
and every own-label row bound from the weighted ancestor norm and the
current norm. These are geometric consequences of the same raw path. -/

@[expose] public section

set_option maxHeartbeats 10000000
set_option maxRecDepth 5000

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

attribute [local instance 2000] rigidGaugeLittle_group rigidGaugeLittle_space rigidGaugeFamily_tower
attribute [local instance] LittleContourSpace.complexScalarNormedSpace LittleContourSpace.complexScalarTower

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_uniform_actualPrefix_weighted_materialTube :
    ∃ C : ℝ, 0 < C ∧ ∀ {s A₀ b R ρ q T Hglob a c D : ℝ},
      ∀ [Fact (1 ≤ ENNReal.ofReal q)] (hs : s ≤ 0) (hA : 0 ≤ A₀) (hb : 0 < b)
        (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
        (hρb : ρ < b) (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q),
      Hglob ≤ T → 5 / 4 + (C * A₀ / (1 - ρ / b)) * Hglob < c → c * R ≤ 1 / 4 →
      0 ≤ D → ∀ {N k : ℕ} (hk : k ≤ N),
      ∀ S : BoundedEulerParticleSystem
        (finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N) T,
      IsFourfoldBoundedEulerParticleSystem S →
      let qinner := P.finiteInnerInitialLabel s A₀ b R ρ N k
      let F := S.actualPartialPhaseField qinner hγ hγ1
        (finiteCircularReferenceC1 hγ hγ1 R ρ) (finiteCircularInterfaceRadius R ρ)
        (finiteCircularInterfaceRadius_pos hR hρ) (lift_finiteCircularReferenceC1 hγ hγ1 R ρ)
        (finiteCircularInterfaceStrength A₀ b)
      let U := S.actualPartialPhaseDomain qinner
        (finiteCircularReferenceC1 hγ hγ1 R ρ) (finiteCircularInterfaceRadius R ρ) a Hglob
      let Zinit : FiniteCircularIndex k → LittleContourSpace γ := fun p =>
        finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N (finiteCircularPrefixIndex hk p)
      ∀ X : ℝ → FiniteCircularIndex k → LittleContourSpace γ,
      IsBanachTimeDomainTrajectoryOn F U Zinit D X →
      ∀ t ∈ Icc (0 : ℝ) D, ∀ {core δ C₀ K : ℝ},
      δ ≤ cellA / 4 → (∀ i, core ≤ 3 * circularContourRadii i / 4) →
      0 < C₀ → C₀ * ρ ^ 6 ≤ 1 → 0 ≤ K → C₀ * ρ ^ 6 * K ≤ δ →
      ∀ Y : ℕ → Fin 2 → LittleContourSpace γ, ∀ u φ : ℕ → ℝ,
      weightedFamilyNorm (C₀ * ρ ^ 6) k
        (fun l => Y l - littleCircularMaterialContours hγ hγ1 (u l)) ≤ K →
      ‖Y k - littleCircularMaterialContours hγ hγ1 (u k)‖ ≤ δ →
      (∀ p : FiniteCircularIndex k, (X t p).val =
        (radScale R ρ p.1 • (exp (((φ p.1 : ℝ) : ℂ) * I) • Y p.1 p.2)).val) →
      ∃ G : P.FiniteOuterMaterialTube s R ρ N k S t core δ,
        (∀ p : FiniteCircularIndex k,
          G.contours (finiteCircularPrefixIndex hk p) = (X t p).val) ∧
        (∀ (l : Fin (k + 1)) i,
          ‖contourParameterShiftC1 (G.shifts (finitePrefixForcingIndex hk l, i))
            (G.contours (finitePrefixForcingIndex hk l, i)) - G.reference (finitePrefixForcingIndex hk l, i)‖ ≤
            radScale R ρ l * ‖Y l - littleCircularMaterialContours hγ hγ1 (u l)‖) := by
  obtain ⟨C, hC, htube⟩ := P.exists_uniform_actualPrefix_materialTube
  refine ⟨C, hC, ?_⟩
  intro s A₀ b R ρ q T Hglob a c D _ hs hA hb hR hRmax hρ hρ1 hρb hq hqE
    hglobT hc hcR hD N k hk S hS
  dsimp only
  intro X hX t ht core δ C₀ K hδ hcore hC₀ hh1 hK hsmall Y u φ hx hcur hraw
  let x : ℕ → Fin 2 → LittleContourSpace γ :=
    fun l => Y l - littleCircularMaterialContours hγ hγ1 (u l)
  have hh : 0 < C₀ * ρ ^ 6 := mul_pos hC₀ (pow_pos hρ 6)
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans hcur
  have hfull (l : Fin (k + 1)) : ‖x l‖ ≤ δ :=
    norm_prefix_le_of_weighted_current hh hh1 hK k x hx hcur hsmall l
  let β : FiniteCircularIndex k → ℝ :=
    fun p => circularRetardedMaterialShift (φ p.1) (u p.1) p.2
  have hβ (p : FiniteCircularIndex k) :
      ‖contourParameterShiftC1 (β p) (X t p).val - finiteCircularReferenceC1 hγ hγ1 R ρ p‖ ≤
        δ * radScale R ρ p.1 := by
    rw [hraw p]
    have hn := norm_le_pi_norm
      (contourParameterShiftFamilyCLM γ (circularRetardedMaterialShift (φ p.1) (u p.1))
        (radScale R ρ p.1 • (exp (((φ p.1 : ℝ) : ℂ) * I) • Y p.1)) -
        radScale R ρ p.1 • littleCircularReference hγ hγ1) p.2
    rw [norm_circularRetardedPhysicalAligned_sub_reference hγ hγ1
      (radScale_pos hR hρ p.1).le] at hn
    exact hn.trans (by nlinarith only [mul_le_mul_of_nonneg_left (hfull p.1) (radScale_pos hR hρ p.1).le])
  obtain ⟨G, hG⟩ := htube hs hA hb hR hRmax hρ hρ1 hρb hq hqE
    hglobT hc hcR hD hk S hS X hX t ht hδ hcore β hβ
  let YY : Fin (N + 1) → Fin 2 → LittleContourSpace γ := fun j => Y j
  let uu : Fin (N + 1) → ℝ := fun j => u j
  let φφ : Fin (N + 1) → ℝ := fun j => φ j
  have hrawG (j : Fin (N + 1)) (hj : (j : ℕ) ≤ k) (i : Fin 2) :
      G.contours (j, i) = (radScale R ρ j • (exp (((φφ j : ℝ) : ℂ) * I) • YY j i)).val := by
    let jj : Fin (k + 1) := ⟨j, Nat.lt_succ_of_le hj⟩
    exact (hG (jj, i)).trans (hraw (jj, i))
  have hprefix : circularRetardedPrefixDeviation hγ hγ1 k YY uu ≤ δ := by
    apply (pi_norm_le_iff_of_nonneg hδ0).mpr
    intro j
    exact hfull ⟨j.val, Nat.lt_succ_of_le j.property⟩
  have hprefixSmall := hprefix.trans hδ
  let G' := P.finiteOuterMaterialTubeOfRetardedFamily hR hρ G YY uu φφ hrawG hprefixSmall
  refine ⟨{ G' with relative_tube := ?_ }, ?_, ?_⟩
  · intro j hj i
    exact (P.finiteRetardedTube_relative_label hR hρ G YY uu φφ hrawG hprefixSmall j hj i).trans
      (mul_le_mul_of_nonneg_left (hfull ⟨j, Nat.lt_succ_of_le hj⟩) (radScale_pos hR hρ j).le)
  · exact hG
  · intro l i
    exact P.finiteRetardedTube_relative_label hR hρ G YY uu φφ hrawG hprefixSmall
      (finitePrefixForcingIndex hk l) (Nat.le_of_lt_succ l.isLt) i

end CircularMaterialTransferProfile
end Euler2D

end
