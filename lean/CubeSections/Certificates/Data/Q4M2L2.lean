import CubeSections.Certificates.Coverage

/-! Generated from computation/data/pair_trees.json; all arithmetic is proved in Lean. -/
namespace CubeSections.Certificates.Data.Q4M2L2

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def parameters : Parameters := ⟨4, 2, 2⟩

private def box_4 : Rectangle := ⟨(1 / 5 : ℚ), (17 / 80 : ℚ), (1 / 5 : ℚ), (17 / 80 : ℚ)⟩
private def node_4 : Tree := .leaf (.strip (91 / 512 : ℚ))
private theorem node_4_accepts : node_4.Accepts parameters box_4 := by
  norm_num [Tree.Accepts, node_4, box_4, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_5 : Rectangle := ⟨(1 / 5 : ℚ), (17 / 80 : ℚ), (17 / 80 : ℚ), (9 / 40 : ℚ)⟩
private def node_5 : Tree := .leaf (.strip (201 / 1024 : ℚ))
private theorem node_5_accepts : node_5.Accepts parameters box_5 := by
  norm_num [Tree.Accepts, node_5, box_5, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_3 : Rectangle := ⟨(1 / 5 : ℚ), (17 / 80 : ℚ), (1 / 5 : ℚ), (9 / 40 : ℚ)⟩
private def node_3 : Tree := .splitD (17 / 80 : ℚ) node_4 node_5
private theorem node_3_accepts : node_3.Accepts parameters box_3 := by
  change SplitDValid box_3 (17 / 80 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_3], node_4_accepts, node_5_accepts⟩

private def box_7 : Rectangle := ⟨(17 / 80 : ℚ), (9 / 40 : ℚ), (1 / 5 : ℚ), (17 / 80 : ℚ)⟩
private def node_7 : Tree := .leaf (.strip (201 / 1024 : ℚ))
private theorem node_7_accepts : node_7.Accepts parameters box_7 := by
  norm_num [Tree.Accepts, node_7, box_7, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_8 : Rectangle := ⟨(17 / 80 : ℚ), (9 / 40 : ℚ), (17 / 80 : ℚ), (9 / 40 : ℚ)⟩
private def node_8 : Tree := .leaf (.strip (219 / 1024 : ℚ))
private theorem node_8_accepts : node_8.Accepts parameters box_8 := by
  norm_num [Tree.Accepts, node_8, box_8, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_6 : Rectangle := ⟨(17 / 80 : ℚ), (9 / 40 : ℚ), (1 / 5 : ℚ), (9 / 40 : ℚ)⟩
private def node_6 : Tree := .splitD (17 / 80 : ℚ) node_7 node_8
private theorem node_6_accepts : node_6.Accepts parameters box_6 := by
  change SplitDValid box_6 (17 / 80 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_6], node_7_accepts, node_8_accepts⟩

private def box_2 : Rectangle := ⟨(1 / 5 : ℚ), (9 / 40 : ℚ), (1 / 5 : ℚ), (9 / 40 : ℚ)⟩
private def node_2 : Tree := .splitC (17 / 80 : ℚ) node_3 node_6
private theorem node_2_accepts : node_2.Accepts parameters box_2 := by
  change SplitCValid box_2 (17 / 80 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_2], node_3_accepts, node_6_accepts⟩

private def box_11 : Rectangle := ⟨(1 / 5 : ℚ), (17 / 80 : ℚ), (9 / 40 : ℚ), (19 / 80 : ℚ)⟩
private def node_11 : Tree := .leaf (.strip (99 / 512 : ℚ))
private theorem node_11_accepts : node_11.Accepts parameters box_11 := by
  norm_num [Tree.Accepts, node_11, box_11, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_12 : Rectangle := ⟨(1 / 5 : ℚ), (17 / 80 : ℚ), (19 / 80 : ℚ), (1 / 4 : ℚ)⟩
private def node_12 : Tree := .leaf (.strip (175 / 1024 : ℚ))
private theorem node_12_accepts : node_12.Accepts parameters box_12 := by
  norm_num [Tree.Accepts, node_12, box_12, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_10 : Rectangle := ⟨(1 / 5 : ℚ), (17 / 80 : ℚ), (9 / 40 : ℚ), (1 / 4 : ℚ)⟩
private def node_10 : Tree := .splitD (19 / 80 : ℚ) node_11 node_12
private theorem node_10_accepts : node_10.Accepts parameters box_10 := by
  change SplitDValid box_10 (19 / 80 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_10], node_11_accepts, node_12_accepts⟩

private def box_14 : Rectangle := ⟨(17 / 80 : ℚ), (9 / 40 : ℚ), (9 / 40 : ℚ), (19 / 80 : ℚ)⟩
private def node_14 : Tree := .leaf (.strip (27 / 128 : ℚ))
private theorem node_14_accepts : node_14.Accepts parameters box_14 := by
  norm_num [Tree.Accepts, node_14, box_14, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_15 : Rectangle := ⟨(17 / 80 : ℚ), (9 / 40 : ℚ), (19 / 80 : ℚ), (1 / 4 : ℚ)⟩
private def node_15 : Tree := .leaf (.strip (97 / 512 : ℚ))
private theorem node_15_accepts : node_15.Accepts parameters box_15 := by
  norm_num [Tree.Accepts, node_15, box_15, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_13 : Rectangle := ⟨(17 / 80 : ℚ), (9 / 40 : ℚ), (9 / 40 : ℚ), (1 / 4 : ℚ)⟩
private def node_13 : Tree := .splitD (19 / 80 : ℚ) node_14 node_15
private theorem node_13_accepts : node_13.Accepts parameters box_13 := by
  change SplitDValid box_13 (19 / 80 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_13], node_14_accepts, node_15_accepts⟩

private def box_9 : Rectangle := ⟨(1 / 5 : ℚ), (9 / 40 : ℚ), (9 / 40 : ℚ), (1 / 4 : ℚ)⟩
private def node_9 : Tree := .splitC (17 / 80 : ℚ) node_10 node_13
private theorem node_9_accepts : node_9.Accepts parameters box_9 := by
  change SplitCValid box_9 (17 / 80 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_9], node_10_accepts, node_13_accepts⟩

private def box_1 : Rectangle := ⟨(1 / 5 : ℚ), (9 / 40 : ℚ), (1 / 5 : ℚ), (1 / 4 : ℚ)⟩
private def node_1 : Tree := .splitD (9 / 40 : ℚ) node_2 node_9
private theorem node_1_accepts : node_1.Accepts parameters box_1 := by
  change SplitDValid box_1 (9 / 40 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_1], node_2_accepts, node_9_accepts⟩

private def box_19 : Rectangle := ⟨(9 / 40 : ℚ), (19 / 80 : ℚ), (1 / 5 : ℚ), (17 / 80 : ℚ)⟩
private def node_19 : Tree := .leaf (.strip (99 / 512 : ℚ))
private theorem node_19_accepts : node_19.Accepts parameters box_19 := by
  norm_num [Tree.Accepts, node_19, box_19, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_20 : Rectangle := ⟨(9 / 40 : ℚ), (19 / 80 : ℚ), (17 / 80 : ℚ), (9 / 40 : ℚ)⟩
private def node_20 : Tree := .leaf (.strip (27 / 128 : ℚ))
private theorem node_20_accepts : node_20.Accepts parameters box_20 := by
  norm_num [Tree.Accepts, node_20, box_20, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_18 : Rectangle := ⟨(9 / 40 : ℚ), (19 / 80 : ℚ), (1 / 5 : ℚ), (9 / 40 : ℚ)⟩
private def node_18 : Tree := .splitD (17 / 80 : ℚ) node_19 node_20
private theorem node_18_accepts : node_18.Accepts parameters box_18 := by
  change SplitDValid box_18 (17 / 80 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_18], node_19_accepts, node_20_accepts⟩

private def box_21 : Rectangle := ⟨(19 / 80 : ℚ), (1 / 4 : ℚ), (1 / 5 : ℚ), (9 / 40 : ℚ)⟩
private def node_21 : Tree := .leaf (.strip (107 / 512 : ℚ))
private theorem node_21_accepts : node_21.Accepts parameters box_21 := by
  norm_num [Tree.Accepts, node_21, box_21, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_17 : Rectangle := ⟨(9 / 40 : ℚ), (1 / 4 : ℚ), (1 / 5 : ℚ), (9 / 40 : ℚ)⟩
private def node_17 : Tree := .splitC (19 / 80 : ℚ) node_18 node_21
private theorem node_17_accepts : node_17.Accepts parameters box_17 := by
  change SplitCValid box_17 (19 / 80 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_17], node_18_accepts, node_21_accepts⟩

private def box_22 : Rectangle := ⟨(9 / 40 : ℚ), (1 / 4 : ℚ), (9 / 40 : ℚ), (1 / 4 : ℚ)⟩
private def node_22 : Tree := .leaf (.strip (121 / 512 : ℚ))
private theorem node_22_accepts : node_22.Accepts parameters box_22 := by
  norm_num [Tree.Accepts, node_22, box_22, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_16 : Rectangle := ⟨(9 / 40 : ℚ), (1 / 4 : ℚ), (1 / 5 : ℚ), (1 / 4 : ℚ)⟩
private def node_16 : Tree := .splitD (9 / 40 : ℚ) node_17 node_22
private theorem node_16_accepts : node_16.Accepts parameters box_16 := by
  change SplitDValid box_16 (9 / 40 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_16], node_17_accepts, node_22_accepts⟩

private def box_0 : Rectangle := ⟨(1 / 5 : ℚ), (1 / 4 : ℚ), (1 / 5 : ℚ), (1 / 4 : ℚ)⟩
private def node_0 : Tree := .splitC (9 / 40 : ℚ) node_1 node_16
private theorem node_0_accepts : node_0.Accepts parameters box_0 := by
  change SplitCValid box_0 (9 / 40 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_0], node_1_accepts, node_16_accepts⟩

def tree : Tree := node_0
theorem accepted : tree.Accepts parameters (rootRectangle parameters.q) := by
  have hb : box_0 = rootRectangle parameters.q := by
    norm_num [box_0, rootRectangle, parameters]
  simpa only [tree, ← hb] using node_0_accepts

theorem checked : tree.check parameters (rootRectangle parameters.q) = true :=
  (tree.check_eq_true_iff parameters (rootRectangle parameters.q)).mpr accepted

#print axioms accepted
#print axioms checked

end CubeSections.Certificates.Data.Q4M2L2
