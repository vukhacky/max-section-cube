import CubeSections.Certificates.Coverage

/-! Generated from computation/data/pair_trees.json; all arithmetic is proved in Lean. -/
namespace CubeSections.Certificates.Data.Q2M1L2.C072

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def parameters : Parameters := ⟨2, 1, 2⟩

private def box_4 : Rectangle := ⟨(3 / 8 : ℚ), (37 / 96 : ℚ), (11 / 24 : ℚ), (15 / 32 : ℚ)⟩
private def node_4 : Tree := .leaf .projection
private theorem node_4_accepts : node_4.Accepts parameters box_4 := by
  norm_num [Tree.Accepts, node_4, box_4, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_5 : Rectangle := ⟨(3 / 8 : ℚ), (37 / 96 : ℚ), (15 / 32 : ℚ), (23 / 48 : ℚ)⟩
private def node_5 : Tree := .leaf .projection
private theorem node_5_accepts : node_5.Accepts parameters box_5 := by
  norm_num [Tree.Accepts, node_5, box_5, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_3 : Rectangle := ⟨(3 / 8 : ℚ), (37 / 96 : ℚ), (11 / 24 : ℚ), (23 / 48 : ℚ)⟩
private def node_3 : Tree := .splitD (15 / 32 : ℚ) node_4 node_5
private theorem node_3_accepts : node_3.Accepts parameters box_3 := by
  change SplitDValid box_3 (15 / 32 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_3], node_4_accepts, node_5_accepts⟩

private def box_7 : Rectangle := ⟨(37 / 96 : ℚ), (19 / 48 : ℚ), (11 / 24 : ℚ), (15 / 32 : ℚ)⟩
private def node_7 : Tree := .leaf .projection
private theorem node_7_accepts : node_7.Accepts parameters box_7 := by
  norm_num [Tree.Accepts, node_7, box_7, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_8 : Rectangle := ⟨(37 / 96 : ℚ), (19 / 48 : ℚ), (15 / 32 : ℚ), (23 / 48 : ℚ)⟩
private def node_8 : Tree := .leaf .projection
private theorem node_8_accepts : node_8.Accepts parameters box_8 := by
  norm_num [Tree.Accepts, node_8, box_8, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_6 : Rectangle := ⟨(37 / 96 : ℚ), (19 / 48 : ℚ), (11 / 24 : ℚ), (23 / 48 : ℚ)⟩
private def node_6 : Tree := .splitD (15 / 32 : ℚ) node_7 node_8
private theorem node_6_accepts : node_6.Accepts parameters box_6 := by
  change SplitDValid box_6 (15 / 32 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_6], node_7_accepts, node_8_accepts⟩

private def box_2 : Rectangle := ⟨(3 / 8 : ℚ), (19 / 48 : ℚ), (11 / 24 : ℚ), (23 / 48 : ℚ)⟩
private def node_2 : Tree := .splitC (37 / 96 : ℚ) node_3 node_6
private theorem node_2_accepts : node_2.Accepts parameters box_2 := by
  change SplitCValid box_2 (37 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_2], node_3_accepts, node_6_accepts⟩

private def box_10 : Rectangle := ⟨(3 / 8 : ℚ), (37 / 96 : ℚ), (23 / 48 : ℚ), (1 / 2 : ℚ)⟩
private def node_10 : Tree := .leaf .projection
private theorem node_10_accepts : node_10.Accepts parameters box_10 := by
  norm_num [Tree.Accepts, node_10, box_10, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_11 : Rectangle := ⟨(37 / 96 : ℚ), (19 / 48 : ℚ), (23 / 48 : ℚ), (1 / 2 : ℚ)⟩
private def node_11 : Tree := .leaf .projection
private theorem node_11_accepts : node_11.Accepts parameters box_11 := by
  norm_num [Tree.Accepts, node_11, box_11, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_9 : Rectangle := ⟨(3 / 8 : ℚ), (19 / 48 : ℚ), (23 / 48 : ℚ), (1 / 2 : ℚ)⟩
private def node_9 : Tree := .splitC (37 / 96 : ℚ) node_10 node_11
private theorem node_9_accepts : node_9.Accepts parameters box_9 := by
  change SplitCValid box_9 (37 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_9], node_10_accepts, node_11_accepts⟩

private def box_1 : Rectangle := ⟨(3 / 8 : ℚ), (19 / 48 : ℚ), (11 / 24 : ℚ), (1 / 2 : ℚ)⟩
private def node_1 : Tree := .splitD (23 / 48 : ℚ) node_2 node_9
private theorem node_1_accepts : node_1.Accepts parameters box_1 := by
  change SplitDValid box_1 (23 / 48 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_1], node_2_accepts, node_9_accepts⟩

private def box_15 : Rectangle := ⟨(19 / 48 : ℚ), (13 / 32 : ℚ), (11 / 24 : ℚ), (15 / 32 : ℚ)⟩
private def node_15 : Tree := .leaf .projection
private theorem node_15_accepts : node_15.Accepts parameters box_15 := by
  norm_num [Tree.Accepts, node_15, box_15, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_16 : Rectangle := ⟨(19 / 48 : ℚ), (13 / 32 : ℚ), (15 / 32 : ℚ), (23 / 48 : ℚ)⟩
private def node_16 : Tree := .leaf .projection
private theorem node_16_accepts : node_16.Accepts parameters box_16 := by
  norm_num [Tree.Accepts, node_16, box_16, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_14 : Rectangle := ⟨(19 / 48 : ℚ), (13 / 32 : ℚ), (11 / 24 : ℚ), (23 / 48 : ℚ)⟩
private def node_14 : Tree := .splitD (15 / 32 : ℚ) node_15 node_16
private theorem node_14_accepts : node_14.Accepts parameters box_14 := by
  change SplitDValid box_14 (15 / 32 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_14], node_15_accepts, node_16_accepts⟩

private def box_18 : Rectangle := ⟨(13 / 32 : ℚ), (5 / 12 : ℚ), (11 / 24 : ℚ), (15 / 32 : ℚ)⟩
private def node_18 : Tree := .leaf .projection
private theorem node_18_accepts : node_18.Accepts parameters box_18 := by
  norm_num [Tree.Accepts, node_18, box_18, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_19 : Rectangle := ⟨(13 / 32 : ℚ), (5 / 12 : ℚ), (15 / 32 : ℚ), (23 / 48 : ℚ)⟩
private def node_19 : Tree := .leaf .projection
private theorem node_19_accepts : node_19.Accepts parameters box_19 := by
  norm_num [Tree.Accepts, node_19, box_19, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_17 : Rectangle := ⟨(13 / 32 : ℚ), (5 / 12 : ℚ), (11 / 24 : ℚ), (23 / 48 : ℚ)⟩
private def node_17 : Tree := .splitD (15 / 32 : ℚ) node_18 node_19
private theorem node_17_accepts : node_17.Accepts parameters box_17 := by
  change SplitDValid box_17 (15 / 32 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_17], node_18_accepts, node_19_accepts⟩

private def box_13 : Rectangle := ⟨(19 / 48 : ℚ), (5 / 12 : ℚ), (11 / 24 : ℚ), (23 / 48 : ℚ)⟩
private def node_13 : Tree := .splitC (13 / 32 : ℚ) node_14 node_17
private theorem node_13_accepts : node_13.Accepts parameters box_13 := by
  change SplitCValid box_13 (13 / 32 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_13], node_14_accepts, node_17_accepts⟩

private def box_20 : Rectangle := ⟨(19 / 48 : ℚ), (5 / 12 : ℚ), (23 / 48 : ℚ), (1 / 2 : ℚ)⟩
private def node_20 : Tree := .leaf .projection
private theorem node_20_accepts : node_20.Accepts parameters box_20 := by
  norm_num [Tree.Accepts, node_20, box_20, parameters, Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta]

private def box_12 : Rectangle := ⟨(19 / 48 : ℚ), (5 / 12 : ℚ), (11 / 24 : ℚ), (1 / 2 : ℚ)⟩
private def node_12 : Tree := .splitD (23 / 48 : ℚ) node_13 node_20
private theorem node_12_accepts : node_12.Accepts parameters box_12 := by
  change SplitDValid box_12 (23 / 48 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_12], node_13_accepts, node_20_accepts⟩

private def box_0 : Rectangle := ⟨(3 / 8 : ℚ), (5 / 12 : ℚ), (11 / 24 : ℚ), (1 / 2 : ℚ)⟩
private def node_0 : Tree := .splitC (19 / 48 : ℚ) node_1 node_12
private theorem node_0_accepts : node_0.Accepts parameters box_0 := by
  change SplitCValid box_0 (19 / 48 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_0], node_1_accepts, node_12_accepts⟩

def tree : Tree := node_0
def rootBox : Rectangle := box_0
theorem accepted : tree.Accepts parameters rootBox := node_0_accepts

end CubeSections.Certificates.Data.Q2M1L2.C072
