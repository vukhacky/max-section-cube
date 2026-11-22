import CubeSections.Geometry.CornerArea
import CubeSections.Semantics
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Real

/-! A genuine density-to-strip-loss implication. The pushforward density and its
almost-everywhere bound are explicit inputs; the area and measure subtraction
are proved here. No coarea or induction hypothesis is hidden in a definition.
-/
noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace CubeSections

theorem measure_removedCorners_le_of_density
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (F : Ω → ℝ × ℝ) (hF : Measurable F) (ρ : ℝ × ℝ → ℝ≥0∞)
    (hmap : Measure.map F μ = volume.withDensity ρ)
    (K : ℝ) (hK : 0 ≤ K)
    (hcap : ∀ᵐ p ∂volume, ρ p ≤ ENNReal.ofReal K)
    {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1/2) :
    μ (F ⁻¹' squareRemovedCorners t) ≤ ENNReal.ofReal (4*K*t^2) := by
  have harea := volume_squareRemovedCorners ht₀ ht₁
  have hm := congrArg (fun ν : Measure (ℝ × ℝ) => ν (squareRemovedCorners t)) hmap
  rw [Measure.map_apply hF (measurableSet_squareRemovedCorners t),
    withDensity_apply ρ (measurableSet_squareRemovedCorners t)] at hm
  rw [hm]
  calc
    (∫⁻ p in squareRemovedCorners t, ρ p) ≤
        ∫⁻ _ in squareRemovedCorners t, ENNReal.ofReal K :=
      lintegral_mono_ae (ae_restrict_of_ae hcap)
    _ = ENNReal.ofReal (4*K*t^2) := by
      rw [lintegral_const, Measure.restrict_apply_univ, harea,
        ← ENNReal.ofReal_mul hK]
      congr 1
      ring

/-- A bounded planar pushforward density controls the retained mass. The cap is
unnormalized: `K * μ(S).toReal`, so the result is a relative retained fraction. -/
theorem retained_measure_of_square_density
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (S : Set Ω)
    (hfinite : μ S ≠ ∞) (F : Ω → ℝ × ℝ) (hF : Measurable F)
    (hsquare : ∀ x ∈ S, -1 ≤ (F x).1 ∧ (F x).1 ≤ 1 ∧
      -1 ≤ (F x).2 ∧ (F x).2 ≤ 1)
    (ρ : ℝ × ℝ → ℝ≥0∞)
    (hmap : Measure.map F (μ.restrict S) = volume.withDensity ρ)
    (K : ℝ) (hK : 0 ≤ K)
    (hcap : ∀ᵐ p ∂volume, ρ p ≤ ENNReal.ofReal (K * (μ S).toReal))
    {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1/2) :
    max 0 (1-4*K*t^2) * (μ S).toReal ≤
      (μ (S ∩ {x | |(F x).1+(F x).2| ≤ 2*(1-t)})).toReal := by
  let strip : Set Ω := {x | |(F x).1+(F x).2| ≤ 2*(1-t)}
  have hmstrip : MeasurableSet strip := by
    exact measurableSet_le (continuous_abs.measurable.comp (hF.fst.add hF.snd)) measurable_const
  have hset : S \ strip = S ∩ (F ⁻¹' squareRemovedCorners t) := by
    ext x
    constructor
    · rintro ⟨hx,hstrip⟩
      have hs := hsquare x hx
      refine ⟨hx,hs.1,hs.2.1,hs.2.2.1,hs.2.2.2,?_⟩
      exact lt_of_not_ge hstrip
    · rintro ⟨hx,hcorn⟩
      exact ⟨hx,not_le_of_gt hcorn.2.2.2.2⟩
  have hcut := measure_removedCorners_le_of_density (μ.restrict S) F hF ρ hmap
    (K*(μ S).toReal) (mul_nonneg hK ENNReal.toReal_nonneg) hcap ht₀ ht₁
  rw [Measure.restrict_apply ((measurableSet_squareRemovedCorners t).preimage hF),
    inter_comm, ← hset] at hcut
  have hcutR : (μ (S \ strip)).toReal ≤ 4*(K*(μ S).toReal)*t^2 :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hcut
  have hsum := measureReal_inter_add_sdiff (μ := μ) (s := S) hmstrip hfinite
  change (μ (S ∩ strip)).toReal + (μ (S \ strip)).toReal = (μ S).toReal at hsum
  change max 0 (1-4*K*t^2) * (μ S).toReal ≤ (μ (S ∩ strip)).toReal
  by_cases hnonneg : 0 ≤ 1-4*K*t^2
  · rw [max_eq_right hnonneg]
    nlinarith
  · rw [max_eq_left (le_of_not_ge hnonneg), zero_mul]
    exact ENNReal.toReal_nonneg

/-- Raw row coordinates rescaled so that the cube projects into [-1,1]^2. -/
def normalizedPairCoordinates {n k : ℕ} (U : Frame n k) (i j : Fin n) :
    E k → ℝ × ℝ := fun x => (2*(U x) i, 2*(U x) j)

theorem measurable_normalizedPairCoordinates {n k : ℕ} (U : Frame n k) (i j : Fin n) :
    Measurable (normalizedPairCoordinates U i j) := by
  have hi : Continuous (fun x : E k => (U x) i) :=
    (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i).comp U.continuous
  have hj : Continuous (fun x : E k => (U x) j) :=
    (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) j).comp U.continuous
  exact ((continuous_const.mul hi).prodMk (continuous_const.mul hj)).measurable

theorem normalizedPairCoordinates_in_square {n k : ℕ} (U : Frame n k) (i j : Fin n)
    (x : E k) (hx : x ∈ U ⁻¹' cube n) :
    -1 ≤ (normalizedPairCoordinates U i j x).1 ∧
      (normalizedPairCoordinates U i j x).1 ≤ 1 ∧
      -1 ≤ (normalizedPairCoordinates U i j x).2 ∧
      (normalizedPairCoordinates U i j x).2 ≤ 1 := by
  have hi := abs_le.mp (hx i)
  have hj := abs_le.mp (hx j)
  dsimp [normalizedPairCoordinates]
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

theorem normalizedPairCoordinates_strip {n k : ℕ} (U : Frame n k) (i j : Fin n) (t : ℝ) :
    {x | |(normalizedPairCoordinates U i j x).1 +
      (normalizedPairCoordinates U i j x).2| ≤ 2*(1-t)} =
      {x | |(U x) i+(U x) j| ≤ 1-t} := by
  ext x
  dsimp [normalizedPairCoordinates]
  rw [← mul_add, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  constructor <;> intro h <;> linarith

/-- The actual section's retained-volume estimate from an explicit planar
pushforward density cap. It does not require maximality. -/
theorem retained_volume_of_pair_density {n k : ℕ} (U : Frame n k) (i j : Fin n)
    (ρ : ℝ × ℝ → ℝ≥0∞)
    (hmap : Measure.map (normalizedPairCoordinates U i j)
      (volume.restrict (U ⁻¹' cube n)) = volume.withDensity ρ)
    (K : ℝ) (hK : 0 ≤ K)
    (hcap : ∀ᵐ p ∂volume, ρ p ≤ ENNReal.ofReal (K * sectionVolume U))
    {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1/2) :
    max 0 (1-4*K*t^2) * sectionVolume U ≤
      (volume ((U ⁻¹' cube n) ∩ {x | |(U x) i+(U x) j| ≤ 1-t})).toReal := by
  have h := retained_measure_of_square_density volume (U ⁻¹' cube n)
    (sectionMass_ne_top U) (normalizedPairCoordinates U i j)
    (measurable_normalizedPairCoordinates U i j)
    (normalizedPairCoordinates_in_square U i j) ρ hmap K hK hcap ht₀ ht₁
  rw [normalizedPairCoordinates_strip] at h
  exact h

#print axioms measure_removedCorners_le_of_density
#print axioms retained_measure_of_square_density
#print axioms retained_volume_of_pair_density
end CubeSections
