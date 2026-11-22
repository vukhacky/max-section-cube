import CubeSections.Geometry.CentralDomination
import CubeSections.Geometry.LowDimensionalCentral
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.Order.Compact

/-! The standard midpoint Brunn--Minkowski proposition in dimensions zero and
one. The one-dimensional proof uses arbitrary compact convex sets, represented
as closed intervals by the measure-preserving scalar coordinate. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace CubeSections

theorem midpointBrunnMinkowski_zero : MidpointBrunnMinkowski 0 := by
  intro A B hA hB hAc hBc hAn hBn
  norm_num

def lineCoordinate : E 1 →ₗ[ℝ] ℝ where
  toFun x := x 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem lineCoordinate_continuous : Continuous lineCoordinate :=
  PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) 0

theorem lineCoordinate_injective : Function.Injective lineCoordinate := by
  intro x y h
  ext i
  have hi : i=0 := Fin.eq_zero i
  subst i
  exact h

theorem volume_lineCoordinate_image {S : Set (E 1)} (hS : IsCompact S) :
    volume S = volume (lineCoordinate '' S) := by
  have hm := lineScalar_measurePreserving.measure_preimage
    (hS.image lineCoordinate_continuous).isClosed.measurableSet.nullMeasurableSet
  change volume (lineCoordinate ⁻¹' (lineCoordinate '' S)) = _ at hm
  rw [Set.preimage_image_eq _ lineCoordinate_injective] at hm
  exact hm

theorem exists_lineCoordinate_interval {S : Set (E 1)}
    (hS : IsCompact S) (hSc : Convex ℝ S) (hSn : S.Nonempty) :
    ∃ a b : ℝ, a ≤ b ∧ lineCoordinate '' S = Icc a b := by
  have hc : IsCompact (lineCoordinate '' S) := hS.image lineCoordinate_continuous
  have hv : Convex ℝ (lineCoordinate '' S) := hSc.linear_image lineCoordinate
  have hn := hSn.image lineCoordinate
  have heq := eq_Icc_of_connected_compact
    ⟨hn, Real.convex_iff_isPreconnected.mp hv⟩ hc
  refine ⟨sInf (lineCoordinate '' S), sSup (lineCoordinate '' S), ?_, heq⟩
  exact nonempty_Icc.mp (heq ▸ hn)

theorem midpointMinkowski_convex {k : ℕ} {A B : Set (E k)}
    (hA : Convex ℝ A) (hB : Convex ℝ B) : Convex ℝ (midpointMinkowski A B) := by
  let L : E k × E k →ₗ[ℝ] E k := (1/2 : ℝ) •
    (LinearMap.fst ℝ (E k) (E k) + LinearMap.snd ℝ (E k) (E k))
  exact (hA.prod hB).linear_image L

theorem midpointBrunnMinkowski_one : MidpointBrunnMinkowski 1 := by
  intro A B hA hB hAc hBc hAn hBn
  obtain ⟨a,b,hab,hAB⟩ := exists_lineCoordinate_interval hA hAc hAn
  obtain ⟨c,d,hcd,hCD⟩ := exists_lineCoordinate_interval hB hBc hBn
  have hma : (a+c)/2 ∈ lineCoordinate '' midpointMinkowski A B := by
    obtain ⟨x,hx,hax⟩ : a ∈ lineCoordinate '' A := by rw [hAB]; exact left_mem_Icc.mpr hab
    obtain ⟨y,hy,hcy⟩ : c ∈ lineCoordinate '' B := by rw [hCD]; exact left_mem_Icc.mpr hcd
    refine ⟨(1/2 : ℝ) • (x+y), ⟨(x,y), ⟨hx,hy⟩, rfl⟩, ?_⟩
    rw [map_smul, map_add, hax, hcy]
    simp only [smul_eq_mul]
    ring
  have hmb : (b+d)/2 ∈ lineCoordinate '' midpointMinkowski A B := by
    obtain ⟨x,hx,hbx⟩ : b ∈ lineCoordinate '' A := by rw [hAB]; exact right_mem_Icc.mpr hab
    obtain ⟨y,hy,hdy⟩ : d ∈ lineCoordinate '' B := by rw [hCD]; exact right_mem_Icc.mpr hcd
    refine ⟨(1/2 : ℝ) • (x+y), ⟨(x,y), ⟨hx,hy⟩, rfl⟩, ?_⟩
    rw [map_smul, map_add, hbx, hdy]
    simp only [smul_eq_mul]
    ring
  have hsub : Icc ((a+c)/2) ((b+d)/2) ⊆ lineCoordinate '' midpointMinkowski A B :=
    ((midpointMinkowski_convex hAc hBc).linear_image lineCoordinate).ordConnected.out hma hmb
  have hM := midpointMinkowski_compact hA hB
  have hlow : (volume (Icc ((a+c)/2) ((b+d)/2))).toReal ≤
      (volume (lineCoordinate '' midpointMinkowski A B)).toReal :=
    ENNReal.toReal_mono ((hM.image lineCoordinate_continuous).measure_ne_top) (measure_mono hsub)
  rw [← volume_lineCoordinate_image hM, Real.volume_Icc,
    ENNReal.toReal_ofReal (by linarith : 0 ≤ (b+d)/2-(a+c)/2)] at hlow
  have hva : (volume A).toReal = b-a := by
    rw [volume_lineCoordinate_image hA, hAB, Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]
  have hvb : (volume B).toReal = d-c := by
    rw [volume_lineCoordinate_image hB, hCD, Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr hcd)]
  norm_num only [Nat.cast_one, div_one, Real.rpow_one]
  rw [hva,hvb]
  linarith

/-- Only dimensions at least two remain in the standard geometric premise. -/
theorem midpointBrunnMinkowski_of_ge_two
    (hBM : ∀ d : ℕ, 2 ≤ d → MidpointBrunnMinkowski d) :
    ∀ d : ℕ, MidpointBrunnMinkowski d := by
  intro d
  rcases d with _ | d
  · exact midpointBrunnMinkowski_zero
  rcases d with _ | d
  · exact midpointBrunnMinkowski_one
  · exact hBM _ (by omega)

#print axioms midpointBrunnMinkowski_zero
#print axioms midpointBrunnMinkowski_one
#print axioms midpointBrunnMinkowski_of_ge_two
end CubeSections
