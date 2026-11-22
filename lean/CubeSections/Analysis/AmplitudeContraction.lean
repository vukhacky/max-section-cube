import CubeSections.LinearAlgebra.Variance
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Pair-dependent amplitude contraction via interval profiles. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators

namespace CubeSections

def intervalProfile (b v : ℝ) : ℝ → ℝ :=
  (Ioc 0 b).indicator (fun _ => v / Real.sqrt b)

theorem intervalProfile_mul (b c v w : ℝ) :
    (fun x => intervalProfile b v x * intervalProfile c w x) =
      (Ioc 0 (min b c)).indicator (fun _ => (v / Real.sqrt b) * (w / Real.sqrt c)) := by
  funext x
  by_cases hx : 0 < x <;> by_cases hb : x ≤ b <;> by_cases hc : x ≤ c <;>
    simp [intervalProfile, Set.mem_Ioc, hx, hb, hc, le_min_iff]

theorem integrable_intervalProfile_mul (b c v w : ℝ) :
    Integrable (fun x => intervalProfile b v x * intervalProfile c w x) := by
  rw [intervalProfile_mul]
  have h : IntegrableOn (fun _ : ℝ => (v / Real.sqrt b) * (w / Real.sqrt c))
      (Ioc 0 (min b c)) volume := by
    exact integrableOn_const (by simp) (by finiteness)
  exact h.integrable_indicator measurableSet_Ioc

theorem integrable_intervalProfile_sq (b v : ℝ) :
    Integrable (fun x => intervalProfile b v x ^ 2) := by
  simpa only [pow_two] using integrable_intervalProfile_mul b b v v

theorem integral_intervalProfile_sq (b v : ℝ) (hb : 0 < b) :
    (∫ x, intervalProfile b v x ^ 2) = v ^ 2 := by
  have hf : (fun x => intervalProfile b v x ^ 2) =
      (Ioc 0 b).indicator (fun _ => (v / Real.sqrt b) ^ 2) := by
    funext x
    by_cases hx : x ∈ Ioc 0 b <;> simp [intervalProfile, hx]
  rw [hf, integral_indicator measurableSet_Ioc, setIntegral_const,
    Real.volume_real_Ioc_of_le hb.le]
  simp only [sub_zero, smul_eq_mul]
  rw [div_pow, Real.sq_sqrt hb.le]
  field_simp

theorem integrable_intervalProfile_diff_sq (b c v w : ℝ) :
    Integrable (fun x => (intervalProfile b v x - intervalProfile c w x) ^ 2) := by
  have hf : (fun x => (intervalProfile b v x - intervalProfile c w x) ^ 2) =
      (fun x => intervalProfile b v x ^ 2 + intervalProfile c w x ^ 2 -
        2 * (intervalProfile b v x * intervalProfile c w x)) := by
    funext x
    ring
  rw [hf]
  exact ((integrable_intervalProfile_sq b v).add (integrable_intervalProfile_sq c w)).sub
    ((integrable_intervalProfile_mul b c v w).const_mul 2)

def pairAmplitude (b c : ℝ) : ℝ := Real.sqrt (min b c / b)

theorem pairAmplitude_difference_le_integral (b c v w : ℝ) (hb : 0 < b) (hc : 0 < c) :
    (pairAmplitude b c * v - pairAmplitude c b * w) ^ 2 ≤
      ∫ x, (intervalProfile b v x - intervalProfile c w x) ^ 2 := by
  have hm : 0 < min b c := lt_min hb hc
  have hfactor : pairAmplitude b c * v - pairAmplitude c b * w =
      Real.sqrt (min b c) * (v / Real.sqrt b - w / Real.sqrt c) := by
    unfold pairAmplitude
    rw [min_comm c b, Real.sqrt_div hm.le b, Real.sqrt_div hm.le c]
    ring
  have hset : (∫ x in Ioc 0 (min b c),
      (intervalProfile b v x - intervalProfile c w x) ^ 2) =
      min b c * (v / Real.sqrt b - w / Real.sqrt c) ^ 2 := by
    calc
      _ = ∫ _ in Ioc 0 (min b c), (v / Real.sqrt b - w / Real.sqrt c) ^ 2 := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro x hx
        have hxb : x ∈ Ioc 0 b := ⟨hx.1, (le_min_iff.mp hx.2).1⟩
        have hxc : x ∈ Ioc 0 c := ⟨hx.1, (le_min_iff.mp hx.2).2⟩
        simp [intervalProfile, hxb, hxc]
      _ = _ := by
        rw [setIntegral_const, Real.volume_real_Ioc_of_le hm.le]
        simp only [sub_zero, smul_eq_mul]
  rw [hfactor, mul_pow, Real.sq_sqrt hm.le, ← hset]
  exact setIntegral_le_integral (integrable_intervalProfile_diff_sq b c v w)
    (Filter.Eventually.of_forall fun x => sq_nonneg _)

def amplitudeVariance {n k : ℕ} (U : Frame n k) (b v : Fin n → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, ∑ j, gramProjection U i j ^ 2 *
    (pairAmplitude (b i) (b j) * v i - pairAmplitude (b j) (b i) * v j) ^ 2

theorem amplitudeVariance_le {n k : ℕ} (U : Frame n k) (b v : Fin n → ℝ)
    (hb : ∀ i, 0 < b i) :
    amplitudeVariance U b v ≤ ∑ i, leverage U i * v i ^ 2 := by
  let f : ℝ → Fin n → ℝ := fun x i => intervalProfile (b i) (v i) x
  have hint (i j : Fin n) : Integrable
      (fun x => gramProjection U i j ^ 2 * (f x i - f x j) ^ 2) :=
    (integrable_intervalProfile_diff_sq (b i) (b j) (v i) (v j)).const_mul _
  have hintRow (i : Fin n) : Integrable
      (fun x => ∑ j, gramProjection U i j ^ 2 * (f x i - f x j) ^ 2) := by
    apply integrable_finsetSum
    intro j hj
    exact hint i j
  have hvarInt : Integrable (fun x => gramVariance U (f x)) := by
    apply Integrable.const_mul
    apply integrable_finsetSum
    intro i hi
    exact hintRow i
  have hnormRow (i : Fin n) : Integrable (fun x => leverage U i * (f x i) ^ 2) :=
    (integrable_intervalProfile_sq (b i) (v i)).const_mul _
  have hnormInt : Integrable (fun x => ∑ i, leverage U i * (f x i) ^ 2) := by
    apply integrable_finsetSum
    intro i hi
    exact hnormRow i
  have hvar : (∫ x, gramVariance U (f x)) =
      (1 / 2 : ℝ) * ∑ i, ∑ j, ∫ x, gramProjection U i j ^ 2 * (f x i - f x j) ^ 2 := by
    unfold gramVariance
    rw [integral_const_mul, integral_finsetSum Finset.univ (fun i _ => hintRow i)]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    exact integral_finsetSum Finset.univ (fun j _ => hint i j)
  have hnorm : (∫ x, ∑ i, leverage U i * (f x i) ^ 2) =
      ∑ i, leverage U i * v i ^ 2 := by
    rw [integral_finsetSum Finset.univ (fun i _ => hnormRow i)]
    apply Finset.sum_congr rfl
    intro i hi
    rw [integral_const_mul]
    congr 1
    exact integral_intervalProfile_sq (b i) (v i) (hb i)
  have hlow : amplitudeVariance U b v ≤
      (1 / 2 : ℝ) * ∑ i, ∑ j, ∫ x, gramProjection U i j ^ 2 * (f x i - f x j) ^ 2 := by
    unfold amplitudeVariance
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left
      (pairAmplitude_difference_le_integral (b i) (b j) (v i) (v j) (hb i) (hb j)) (sq_nonneg _)
  calc
    _ ≤ _ := hlow
    _ = ∫ x, gramVariance U (f x) := hvar.symm
    _ ≤ ∫ x, ∑ i, leverage U i * (f x i) ^ 2 :=
      integral_mono hvarInt hnormInt (fun x => gramVariance_le U (f x))
    _ = _ := hnorm

end CubeSections
