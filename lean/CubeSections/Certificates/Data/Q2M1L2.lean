import CubeSections.Certificates.Coverage
import CubeSections.Certificates.Data.Q2M1L2.C000
import CubeSections.Certificates.Data.Q2M1L2.C001
import CubeSections.Certificates.Data.Q2M1L2.C002
import CubeSections.Certificates.Data.Q2M1L2.C003
import CubeSections.Certificates.Data.Q2M1L2.C004
import CubeSections.Certificates.Data.Q2M1L2.C005
import CubeSections.Certificates.Data.Q2M1L2.C006
import CubeSections.Certificates.Data.Q2M1L2.C007
import CubeSections.Certificates.Data.Q2M1L2.C008
import CubeSections.Certificates.Data.Q2M1L2.C009
import CubeSections.Certificates.Data.Q2M1L2.C010
import CubeSections.Certificates.Data.Q2M1L2.C011
import CubeSections.Certificates.Data.Q2M1L2.C012
import CubeSections.Certificates.Data.Q2M1L2.C013
import CubeSections.Certificates.Data.Q2M1L2.C014
import CubeSections.Certificates.Data.Q2M1L2.C015
import CubeSections.Certificates.Data.Q2M1L2.C016
import CubeSections.Certificates.Data.Q2M1L2.C017
import CubeSections.Certificates.Data.Q2M1L2.C018
import CubeSections.Certificates.Data.Q2M1L2.C019
import CubeSections.Certificates.Data.Q2M1L2.C020
import CubeSections.Certificates.Data.Q2M1L2.C021
import CubeSections.Certificates.Data.Q2M1L2.C022
import CubeSections.Certificates.Data.Q2M1L2.C023
import CubeSections.Certificates.Data.Q2M1L2.C024
import CubeSections.Certificates.Data.Q2M1L2.C025
import CubeSections.Certificates.Data.Q2M1L2.C026
import CubeSections.Certificates.Data.Q2M1L2.C027
import CubeSections.Certificates.Data.Q2M1L2.C028
import CubeSections.Certificates.Data.Q2M1L2.C029
import CubeSections.Certificates.Data.Q2M1L2.C030
import CubeSections.Certificates.Data.Q2M1L2.C031
import CubeSections.Certificates.Data.Q2M1L2.C032
import CubeSections.Certificates.Data.Q2M1L2.C033
import CubeSections.Certificates.Data.Q2M1L2.C034
import CubeSections.Certificates.Data.Q2M1L2.C035
import CubeSections.Certificates.Data.Q2M1L2.C036
import CubeSections.Certificates.Data.Q2M1L2.C037
import CubeSections.Certificates.Data.Q2M1L2.C038
import CubeSections.Certificates.Data.Q2M1L2.C039
import CubeSections.Certificates.Data.Q2M1L2.C040
import CubeSections.Certificates.Data.Q2M1L2.C041
import CubeSections.Certificates.Data.Q2M1L2.C042
import CubeSections.Certificates.Data.Q2M1L2.C043
import CubeSections.Certificates.Data.Q2M1L2.C044
import CubeSections.Certificates.Data.Q2M1L2.C045
import CubeSections.Certificates.Data.Q2M1L2.C046
import CubeSections.Certificates.Data.Q2M1L2.C047
import CubeSections.Certificates.Data.Q2M1L2.C048
import CubeSections.Certificates.Data.Q2M1L2.C049
import CubeSections.Certificates.Data.Q2M1L2.C050
import CubeSections.Certificates.Data.Q2M1L2.C051
import CubeSections.Certificates.Data.Q2M1L2.C052
import CubeSections.Certificates.Data.Q2M1L2.C053
import CubeSections.Certificates.Data.Q2M1L2.C054
import CubeSections.Certificates.Data.Q2M1L2.C055
import CubeSections.Certificates.Data.Q2M1L2.C056
import CubeSections.Certificates.Data.Q2M1L2.C057
import CubeSections.Certificates.Data.Q2M1L2.C058
import CubeSections.Certificates.Data.Q2M1L2.C059
import CubeSections.Certificates.Data.Q2M1L2.C060
import CubeSections.Certificates.Data.Q2M1L2.C061
import CubeSections.Certificates.Data.Q2M1L2.C062
import CubeSections.Certificates.Data.Q2M1L2.C063
import CubeSections.Certificates.Data.Q2M1L2.C064
import CubeSections.Certificates.Data.Q2M1L2.C065
import CubeSections.Certificates.Data.Q2M1L2.C066
import CubeSections.Certificates.Data.Q2M1L2.C067
import CubeSections.Certificates.Data.Q2M1L2.C068
import CubeSections.Certificates.Data.Q2M1L2.C069
import CubeSections.Certificates.Data.Q2M1L2.C070
import CubeSections.Certificates.Data.Q2M1L2.C071
import CubeSections.Certificates.Data.Q2M1L2.C072
import CubeSections.Certificates.Data.Q2M1L2.C073

/-! Generated from computation/data/pair_trees.json; all arithmetic is proved in Lean. -/
namespace CubeSections.Certificates.Data.Q2M1L2

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def parameters : Parameters := ⟨2, 1, 2⟩

private def box_6 : Rectangle := ⟨(1 / 3 : ℚ), (17 / 48 : ℚ), (1 / 3 : ℚ), (17 / 48 : ℚ)⟩
private def node_6 : Tree := C000.tree
private theorem node_6_accepts : node_6.Accepts parameters box_6 := C000.accepted

private def box_8 : Rectangle := ⟨(1 / 3 : ℚ), (11 / 32 : ℚ), (17 / 48 : ℚ), (3 / 8 : ℚ)⟩
private def node_8 : Tree := C001.tree
private theorem node_8_accepts : node_8.Accepts parameters box_8 := C001.accepted

private def box_10 : Rectangle := ⟨(11 / 32 : ℚ), (17 / 48 : ℚ), (17 / 48 : ℚ), (35 / 96 : ℚ)⟩
private def node_10 : Tree := C002.tree
private theorem node_10_accepts : node_10.Accepts parameters box_10 := C002.accepted

private def box_12 : Rectangle := ⟨(11 / 32 : ℚ), (67 / 192 : ℚ), (35 / 96 : ℚ), (3 / 8 : ℚ)⟩
private def node_12 : Tree := C003.tree
private theorem node_12_accepts : node_12.Accepts parameters box_12 := C003.accepted

private def box_14 : Rectangle := ⟨(67 / 192 : ℚ), (17 / 48 : ℚ), (35 / 96 : ℚ), (71 / 192 : ℚ)⟩
private def node_14 : Tree := C004.tree
private theorem node_14_accepts : node_14.Accepts parameters box_14 := C004.accepted

private def box_16 : Rectangle := ⟨(67 / 192 : ℚ), (45 / 128 : ℚ), (71 / 192 : ℚ), (3 / 8 : ℚ)⟩
private def node_16 : Tree := C005.tree
private theorem node_16_accepts : node_16.Accepts parameters box_16 := C005.accepted

private def box_17 : Rectangle := ⟨(45 / 128 : ℚ), (17 / 48 : ℚ), (71 / 192 : ℚ), (3 / 8 : ℚ)⟩
private def node_17 : Tree := C006.tree
private theorem node_17_accepts : node_17.Accepts parameters box_17 := C006.accepted

private def box_15 : Rectangle := ⟨(67 / 192 : ℚ), (17 / 48 : ℚ), (71 / 192 : ℚ), (3 / 8 : ℚ)⟩
private def node_15 : Tree := .splitC (45 / 128 : ℚ) node_16 node_17
private theorem node_15_accepts : node_15.Accepts parameters box_15 := by
  change SplitCValid box_15 (45 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_15], node_16_accepts, node_17_accepts⟩

private def box_13 : Rectangle := ⟨(67 / 192 : ℚ), (17 / 48 : ℚ), (35 / 96 : ℚ), (3 / 8 : ℚ)⟩
private def node_13 : Tree := .splitD (71 / 192 : ℚ) node_14 node_15
private theorem node_13_accepts : node_13.Accepts parameters box_13 := by
  change SplitDValid box_13 (71 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_13], node_14_accepts, node_15_accepts⟩

private def box_11 : Rectangle := ⟨(11 / 32 : ℚ), (17 / 48 : ℚ), (35 / 96 : ℚ), (3 / 8 : ℚ)⟩
private def node_11 : Tree := .splitC (67 / 192 : ℚ) node_12 node_13
private theorem node_11_accepts : node_11.Accepts parameters box_11 := by
  change SplitCValid box_11 (67 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_11], node_12_accepts, node_13_accepts⟩

private def box_9 : Rectangle := ⟨(11 / 32 : ℚ), (17 / 48 : ℚ), (17 / 48 : ℚ), (3 / 8 : ℚ)⟩
private def node_9 : Tree := .splitD (35 / 96 : ℚ) node_10 node_11
private theorem node_9_accepts : node_9.Accepts parameters box_9 := by
  change SplitDValid box_9 (35 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_9], node_10_accepts, node_11_accepts⟩

private def box_7 : Rectangle := ⟨(1 / 3 : ℚ), (17 / 48 : ℚ), (17 / 48 : ℚ), (3 / 8 : ℚ)⟩
private def node_7 : Tree := .splitC (11 / 32 : ℚ) node_8 node_9
private theorem node_7_accepts : node_7.Accepts parameters box_7 := by
  change SplitCValid box_7 (11 / 32 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_7], node_8_accepts, node_9_accepts⟩

private def box_5 : Rectangle := ⟨(1 / 3 : ℚ), (17 / 48 : ℚ), (1 / 3 : ℚ), (3 / 8 : ℚ)⟩
private def node_5 : Tree := .splitD (17 / 48 : ℚ) node_6 node_7
private theorem node_5_accepts : node_5.Accepts parameters box_5 := by
  change SplitDValid box_5 (17 / 48 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_5], node_6_accepts, node_7_accepts⟩

private def box_19 : Rectangle := ⟨(17 / 48 : ℚ), (3 / 8 : ℚ), (1 / 3 : ℚ), (17 / 48 : ℚ)⟩
private def node_19 : Tree := C007.tree
private theorem node_19_accepts : node_19.Accepts parameters box_19 := C007.accepted

private def box_22 : Rectangle := ⟨(17 / 48 : ℚ), (35 / 96 : ℚ), (17 / 48 : ℚ), (35 / 96 : ℚ)⟩
private def node_22 : Tree := C008.tree
private theorem node_22_accepts : node_22.Accepts parameters box_22 := C008.accepted

private def box_25 : Rectangle := ⟨(17 / 48 : ℚ), (23 / 64 : ℚ), (35 / 96 : ℚ), (71 / 192 : ℚ)⟩
private def node_25 : Tree := C009.tree
private theorem node_25_accepts : node_25.Accepts parameters box_25 := C009.accepted

private def box_28 : Rectangle := ⟨(17 / 48 : ℚ), (137 / 384 : ℚ), (71 / 192 : ℚ), (143 / 384 : ℚ)⟩
private def node_28 : Tree := C010.tree
private theorem node_28_accepts : node_28.Accepts parameters box_28 := C010.accepted

private def box_29 : Rectangle := ⟨(17 / 48 : ℚ), (137 / 384 : ℚ), (143 / 384 : ℚ), (3 / 8 : ℚ)⟩
private def node_29 : Tree := C011.tree
private theorem node_29_accepts : node_29.Accepts parameters box_29 := C011.accepted

private def box_27 : Rectangle := ⟨(17 / 48 : ℚ), (137 / 384 : ℚ), (71 / 192 : ℚ), (3 / 8 : ℚ)⟩
private def node_27 : Tree := .splitD (143 / 384 : ℚ) node_28 node_29
private theorem node_27_accepts : node_27.Accepts parameters box_27 := by
  change SplitDValid box_27 (143 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_27], node_28_accepts, node_29_accepts⟩

private def box_31 : Rectangle := ⟨(137 / 384 : ℚ), (23 / 64 : ℚ), (71 / 192 : ℚ), (143 / 384 : ℚ)⟩
private def node_31 : Tree := C012.tree
private theorem node_31_accepts : node_31.Accepts parameters box_31 := C012.accepted

private def box_32 : Rectangle := ⟨(137 / 384 : ℚ), (23 / 64 : ℚ), (143 / 384 : ℚ), (3 / 8 : ℚ)⟩
private def node_32 : Tree := C013.tree
private theorem node_32_accepts : node_32.Accepts parameters box_32 := C013.accepted

private def box_30 : Rectangle := ⟨(137 / 384 : ℚ), (23 / 64 : ℚ), (71 / 192 : ℚ), (3 / 8 : ℚ)⟩
private def node_30 : Tree := .splitD (143 / 384 : ℚ) node_31 node_32
private theorem node_30_accepts : node_30.Accepts parameters box_30 := by
  change SplitDValid box_30 (143 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_30], node_31_accepts, node_32_accepts⟩

private def box_26 : Rectangle := ⟨(17 / 48 : ℚ), (23 / 64 : ℚ), (71 / 192 : ℚ), (3 / 8 : ℚ)⟩
private def node_26 : Tree := .splitC (137 / 384 : ℚ) node_27 node_30
private theorem node_26_accepts : node_26.Accepts parameters box_26 := by
  change SplitCValid box_26 (137 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_26], node_27_accepts, node_30_accepts⟩

private def box_24 : Rectangle := ⟨(17 / 48 : ℚ), (23 / 64 : ℚ), (35 / 96 : ℚ), (3 / 8 : ℚ)⟩
private def node_24 : Tree := .splitD (71 / 192 : ℚ) node_25 node_26
private theorem node_24_accepts : node_24.Accepts parameters box_24 := by
  change SplitDValid box_24 (71 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_24], node_25_accepts, node_26_accepts⟩

private def box_34 : Rectangle := ⟨(23 / 64 : ℚ), (35 / 96 : ℚ), (35 / 96 : ℚ), (71 / 192 : ℚ)⟩
private def node_34 : Tree := C014.tree
private theorem node_34_accepts : node_34.Accepts parameters box_34 := C014.accepted

private def box_37 : Rectangle := ⟨(23 / 64 : ℚ), (139 / 384 : ℚ), (71 / 192 : ℚ), (143 / 384 : ℚ)⟩
private def node_37 : Tree := C015.tree
private theorem node_37_accepts : node_37.Accepts parameters box_37 := C015.accepted

private def box_38 : Rectangle := ⟨(23 / 64 : ℚ), (139 / 384 : ℚ), (143 / 384 : ℚ), (3 / 8 : ℚ)⟩
private def node_38 : Tree := C016.tree
private theorem node_38_accepts : node_38.Accepts parameters box_38 := C016.accepted

private def box_36 : Rectangle := ⟨(23 / 64 : ℚ), (139 / 384 : ℚ), (71 / 192 : ℚ), (3 / 8 : ℚ)⟩
private def node_36 : Tree := .splitD (143 / 384 : ℚ) node_37 node_38
private theorem node_36_accepts : node_36.Accepts parameters box_36 := by
  change SplitDValid box_36 (143 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_36], node_37_accepts, node_38_accepts⟩

private def box_40 : Rectangle := ⟨(139 / 384 : ℚ), (35 / 96 : ℚ), (71 / 192 : ℚ), (143 / 384 : ℚ)⟩
private def node_40 : Tree := C017.tree
private theorem node_40_accepts : node_40.Accepts parameters box_40 := C017.accepted

private def box_41 : Rectangle := ⟨(139 / 384 : ℚ), (35 / 96 : ℚ), (143 / 384 : ℚ), (3 / 8 : ℚ)⟩
private def node_41 : Tree := C018.tree
private theorem node_41_accepts : node_41.Accepts parameters box_41 := C018.accepted

private def box_39 : Rectangle := ⟨(139 / 384 : ℚ), (35 / 96 : ℚ), (71 / 192 : ℚ), (3 / 8 : ℚ)⟩
private def node_39 : Tree := .splitD (143 / 384 : ℚ) node_40 node_41
private theorem node_39_accepts : node_39.Accepts parameters box_39 := by
  change SplitDValid box_39 (143 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_39], node_40_accepts, node_41_accepts⟩

private def box_35 : Rectangle := ⟨(23 / 64 : ℚ), (35 / 96 : ℚ), (71 / 192 : ℚ), (3 / 8 : ℚ)⟩
private def node_35 : Tree := .splitC (139 / 384 : ℚ) node_36 node_39
private theorem node_35_accepts : node_35.Accepts parameters box_35 := by
  change SplitCValid box_35 (139 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_35], node_36_accepts, node_39_accepts⟩

private def box_33 : Rectangle := ⟨(23 / 64 : ℚ), (35 / 96 : ℚ), (35 / 96 : ℚ), (3 / 8 : ℚ)⟩
private def node_33 : Tree := .splitD (71 / 192 : ℚ) node_34 node_35
private theorem node_33_accepts : node_33.Accepts parameters box_33 := by
  change SplitDValid box_33 (71 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_33], node_34_accepts, node_35_accepts⟩

private def box_23 : Rectangle := ⟨(17 / 48 : ℚ), (35 / 96 : ℚ), (35 / 96 : ℚ), (3 / 8 : ℚ)⟩
private def node_23 : Tree := .splitC (23 / 64 : ℚ) node_24 node_33
private theorem node_23_accepts : node_23.Accepts parameters box_23 := by
  change SplitCValid box_23 (23 / 64 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_23], node_24_accepts, node_33_accepts⟩

private def box_21 : Rectangle := ⟨(17 / 48 : ℚ), (35 / 96 : ℚ), (17 / 48 : ℚ), (3 / 8 : ℚ)⟩
private def node_21 : Tree := .splitD (35 / 96 : ℚ) node_22 node_23
private theorem node_21_accepts : node_21.Accepts parameters box_21 := by
  change SplitDValid box_21 (35 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_21], node_22_accepts, node_23_accepts⟩

private def box_43 : Rectangle := ⟨(35 / 96 : ℚ), (3 / 8 : ℚ), (17 / 48 : ℚ), (35 / 96 : ℚ)⟩
private def node_43 : Tree := C019.tree
private theorem node_43_accepts : node_43.Accepts parameters box_43 := C019.accepted

private def box_46 : Rectangle := ⟨(35 / 96 : ℚ), (71 / 192 : ℚ), (35 / 96 : ℚ), (71 / 192 : ℚ)⟩
private def node_46 : Tree := C020.tree
private theorem node_46_accepts : node_46.Accepts parameters box_46 := C020.accepted

private def box_48 : Rectangle := ⟨(35 / 96 : ℚ), (47 / 128 : ℚ), (71 / 192 : ℚ), (3 / 8 : ℚ)⟩
private def node_48 : Tree := C021.tree
private theorem node_48_accepts : node_48.Accepts parameters box_48 := C021.accepted

private def box_49 : Rectangle := ⟨(47 / 128 : ℚ), (71 / 192 : ℚ), (71 / 192 : ℚ), (3 / 8 : ℚ)⟩
private def node_49 : Tree := C022.tree
private theorem node_49_accepts : node_49.Accepts parameters box_49 := C022.accepted

private def box_47 : Rectangle := ⟨(35 / 96 : ℚ), (71 / 192 : ℚ), (71 / 192 : ℚ), (3 / 8 : ℚ)⟩
private def node_47 : Tree := .splitC (47 / 128 : ℚ) node_48 node_49
private theorem node_47_accepts : node_47.Accepts parameters box_47 := by
  change SplitCValid box_47 (47 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_47], node_48_accepts, node_49_accepts⟩

private def box_45 : Rectangle := ⟨(35 / 96 : ℚ), (71 / 192 : ℚ), (35 / 96 : ℚ), (3 / 8 : ℚ)⟩
private def node_45 : Tree := .splitD (71 / 192 : ℚ) node_46 node_47
private theorem node_45_accepts : node_45.Accepts parameters box_45 := by
  change SplitDValid box_45 (71 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_45], node_46_accepts, node_47_accepts⟩

private def box_50 : Rectangle := ⟨(71 / 192 : ℚ), (3 / 8 : ℚ), (35 / 96 : ℚ), (3 / 8 : ℚ)⟩
private def node_50 : Tree := C023.tree
private theorem node_50_accepts : node_50.Accepts parameters box_50 := C023.accepted

private def box_44 : Rectangle := ⟨(35 / 96 : ℚ), (3 / 8 : ℚ), (35 / 96 : ℚ), (3 / 8 : ℚ)⟩
private def node_44 : Tree := .splitC (71 / 192 : ℚ) node_45 node_50
private theorem node_44_accepts : node_44.Accepts parameters box_44 := by
  change SplitCValid box_44 (71 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_44], node_45_accepts, node_50_accepts⟩

private def box_42 : Rectangle := ⟨(35 / 96 : ℚ), (3 / 8 : ℚ), (17 / 48 : ℚ), (3 / 8 : ℚ)⟩
private def node_42 : Tree := .splitD (35 / 96 : ℚ) node_43 node_44
private theorem node_42_accepts : node_42.Accepts parameters box_42 := by
  change SplitDValid box_42 (35 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_42], node_43_accepts, node_44_accepts⟩

private def box_20 : Rectangle := ⟨(17 / 48 : ℚ), (3 / 8 : ℚ), (17 / 48 : ℚ), (3 / 8 : ℚ)⟩
private def node_20 : Tree := .splitC (35 / 96 : ℚ) node_21 node_42
private theorem node_20_accepts : node_20.Accepts parameters box_20 := by
  change SplitCValid box_20 (35 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_20], node_21_accepts, node_42_accepts⟩

private def box_18 : Rectangle := ⟨(17 / 48 : ℚ), (3 / 8 : ℚ), (1 / 3 : ℚ), (3 / 8 : ℚ)⟩
private def node_18 : Tree := .splitD (17 / 48 : ℚ) node_19 node_20
private theorem node_18_accepts : node_18.Accepts parameters box_18 := by
  change SplitDValid box_18 (17 / 48 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_18], node_19_accepts, node_20_accepts⟩

private def box_4 : Rectangle := ⟨(1 / 3 : ℚ), (3 / 8 : ℚ), (1 / 3 : ℚ), (3 / 8 : ℚ)⟩
private def node_4 : Tree := .splitC (17 / 48 : ℚ) node_5 node_18
private theorem node_4_accepts : node_4.Accepts parameters box_4 := by
  change SplitCValid box_4 (17 / 48 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_4], node_5_accepts, node_18_accepts⟩

private def box_56 : Rectangle := ⟨(1 / 3 : ℚ), (65 / 192 : ℚ), (3 / 8 : ℚ), (37 / 96 : ℚ)⟩
private def node_56 : Tree := C024.tree
private theorem node_56_accepts : node_56.Accepts parameters box_56 := C024.accepted

private def box_57 : Rectangle := ⟨(65 / 192 : ℚ), (11 / 32 : ℚ), (3 / 8 : ℚ), (37 / 96 : ℚ)⟩
private def node_57 : Tree := C025.tree
private theorem node_57_accepts : node_57.Accepts parameters box_57 := C025.accepted

private def box_55 : Rectangle := ⟨(1 / 3 : ℚ), (11 / 32 : ℚ), (3 / 8 : ℚ), (37 / 96 : ℚ)⟩
private def node_55 : Tree := .splitC (65 / 192 : ℚ) node_56 node_57
private theorem node_55_accepts : node_55.Accepts parameters box_55 := by
  change SplitCValid box_55 (65 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_55], node_56_accepts, node_57_accepts⟩

private def box_58 : Rectangle := ⟨(1 / 3 : ℚ), (11 / 32 : ℚ), (37 / 96 : ℚ), (19 / 48 : ℚ)⟩
private def node_58 : Tree := C026.tree
private theorem node_58_accepts : node_58.Accepts parameters box_58 := C026.accepted

private def box_54 : Rectangle := ⟨(1 / 3 : ℚ), (11 / 32 : ℚ), (3 / 8 : ℚ), (19 / 48 : ℚ)⟩
private def node_54 : Tree := .splitD (37 / 96 : ℚ) node_55 node_58
private theorem node_54_accepts : node_54.Accepts parameters box_54 := by
  change SplitDValid box_54 (37 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_54], node_55_accepts, node_58_accepts⟩

private def box_63 : Rectangle := ⟨(11 / 32 : ℚ), (133 / 384 : ℚ), (3 / 8 : ℚ), (73 / 192 : ℚ)⟩
private def node_63 : Tree := C027.tree
private theorem node_63_accepts : node_63.Accepts parameters box_63 := C027.accepted

private def box_64 : Rectangle := ⟨(133 / 384 : ℚ), (67 / 192 : ℚ), (3 / 8 : ℚ), (73 / 192 : ℚ)⟩
private def node_64 : Tree := C028.tree
private theorem node_64_accepts : node_64.Accepts parameters box_64 := C028.accepted

private def box_62 : Rectangle := ⟨(11 / 32 : ℚ), (67 / 192 : ℚ), (3 / 8 : ℚ), (73 / 192 : ℚ)⟩
private def node_62 : Tree := .splitC (133 / 384 : ℚ) node_63 node_64
private theorem node_62_accepts : node_62.Accepts parameters box_62 := by
  change SplitCValid box_62 (133 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_62], node_63_accepts, node_64_accepts⟩

private def box_65 : Rectangle := ⟨(11 / 32 : ℚ), (67 / 192 : ℚ), (73 / 192 : ℚ), (37 / 96 : ℚ)⟩
private def node_65 : Tree := C029.tree
private theorem node_65_accepts : node_65.Accepts parameters box_65 := C029.accepted

private def box_61 : Rectangle := ⟨(11 / 32 : ℚ), (67 / 192 : ℚ), (3 / 8 : ℚ), (37 / 96 : ℚ)⟩
private def node_61 : Tree := .splitD (73 / 192 : ℚ) node_62 node_65
private theorem node_61_accepts : node_61.Accepts parameters box_61 := by
  change SplitDValid box_61 (73 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_61], node_62_accepts, node_65_accepts⟩

private def box_68 : Rectangle := ⟨(67 / 192 : ℚ), (45 / 128 : ℚ), (3 / 8 : ℚ), (73 / 192 : ℚ)⟩
private def node_68 : Tree := C030.tree
private theorem node_68_accepts : node_68.Accepts parameters box_68 := C030.accepted

private def box_70 : Rectangle := ⟨(45 / 128 : ℚ), (17 / 48 : ℚ), (3 / 8 : ℚ), (145 / 384 : ℚ)⟩
private def node_70 : Tree := C031.tree
private theorem node_70_accepts : node_70.Accepts parameters box_70 := C031.accepted

private def box_71 : Rectangle := ⟨(45 / 128 : ℚ), (17 / 48 : ℚ), (145 / 384 : ℚ), (73 / 192 : ℚ)⟩
private def node_71 : Tree := C032.tree
private theorem node_71_accepts : node_71.Accepts parameters box_71 := C032.accepted

private def box_69 : Rectangle := ⟨(45 / 128 : ℚ), (17 / 48 : ℚ), (3 / 8 : ℚ), (73 / 192 : ℚ)⟩
private def node_69 : Tree := .splitD (145 / 384 : ℚ) node_70 node_71
private theorem node_69_accepts : node_69.Accepts parameters box_69 := by
  change SplitDValid box_69 (145 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_69], node_70_accepts, node_71_accepts⟩

private def box_67 : Rectangle := ⟨(67 / 192 : ℚ), (17 / 48 : ℚ), (3 / 8 : ℚ), (73 / 192 : ℚ)⟩
private def node_67 : Tree := .splitC (45 / 128 : ℚ) node_68 node_69
private theorem node_67_accepts : node_67.Accepts parameters box_67 := by
  change SplitCValid box_67 (45 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_67], node_68_accepts, node_69_accepts⟩

private def box_72 : Rectangle := ⟨(67 / 192 : ℚ), (17 / 48 : ℚ), (73 / 192 : ℚ), (37 / 96 : ℚ)⟩
private def node_72 : Tree := C033.tree
private theorem node_72_accepts : node_72.Accepts parameters box_72 := C033.accepted

private def box_66 : Rectangle := ⟨(67 / 192 : ℚ), (17 / 48 : ℚ), (3 / 8 : ℚ), (37 / 96 : ℚ)⟩
private def node_66 : Tree := .splitD (73 / 192 : ℚ) node_67 node_72
private theorem node_66_accepts : node_66.Accepts parameters box_66 := by
  change SplitDValid box_66 (73 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_66], node_67_accepts, node_72_accepts⟩

private def box_60 : Rectangle := ⟨(11 / 32 : ℚ), (17 / 48 : ℚ), (3 / 8 : ℚ), (37 / 96 : ℚ)⟩
private def node_60 : Tree := .splitC (67 / 192 : ℚ) node_61 node_66
private theorem node_60_accepts : node_60.Accepts parameters box_60 := by
  change SplitCValid box_60 (67 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_60], node_61_accepts, node_66_accepts⟩

private def box_74 : Rectangle := ⟨(11 / 32 : ℚ), (67 / 192 : ℚ), (37 / 96 : ℚ), (19 / 48 : ℚ)⟩
private def node_74 : Tree := C034.tree
private theorem node_74_accepts : node_74.Accepts parameters box_74 := C034.accepted

private def box_75 : Rectangle := ⟨(67 / 192 : ℚ), (17 / 48 : ℚ), (37 / 96 : ℚ), (19 / 48 : ℚ)⟩
private def node_75 : Tree := C035.tree
private theorem node_75_accepts : node_75.Accepts parameters box_75 := C035.accepted

private def box_73 : Rectangle := ⟨(11 / 32 : ℚ), (17 / 48 : ℚ), (37 / 96 : ℚ), (19 / 48 : ℚ)⟩
private def node_73 : Tree := .splitC (67 / 192 : ℚ) node_74 node_75
private theorem node_73_accepts : node_73.Accepts parameters box_73 := by
  change SplitCValid box_73 (67 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_73], node_74_accepts, node_75_accepts⟩

private def box_59 : Rectangle := ⟨(11 / 32 : ℚ), (17 / 48 : ℚ), (3 / 8 : ℚ), (19 / 48 : ℚ)⟩
private def node_59 : Tree := .splitD (37 / 96 : ℚ) node_60 node_73
private theorem node_59_accepts : node_59.Accepts parameters box_59 := by
  change SplitDValid box_59 (37 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_59], node_60_accepts, node_73_accepts⟩

private def box_53 : Rectangle := ⟨(1 / 3 : ℚ), (17 / 48 : ℚ), (3 / 8 : ℚ), (19 / 48 : ℚ)⟩
private def node_53 : Tree := .splitC (11 / 32 : ℚ) node_54 node_59
private theorem node_53_accepts : node_53.Accepts parameters box_53 := by
  change SplitCValid box_53 (11 / 32 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_53], node_54_accepts, node_59_accepts⟩

private def box_76 : Rectangle := ⟨(1 / 3 : ℚ), (17 / 48 : ℚ), (19 / 48 : ℚ), (5 / 12 : ℚ)⟩
private def node_76 : Tree := C036.tree
private theorem node_76_accepts : node_76.Accepts parameters box_76 := C036.accepted

private def box_52 : Rectangle := ⟨(1 / 3 : ℚ), (17 / 48 : ℚ), (3 / 8 : ℚ), (5 / 12 : ℚ)⟩
private def node_52 : Tree := .splitD (19 / 48 : ℚ) node_53 node_76
private theorem node_52_accepts : node_52.Accepts parameters box_52 := by
  change SplitDValid box_52 (19 / 48 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_52], node_53_accepts, node_76_accepts⟩

private def box_84 : Rectangle := ⟨(17 / 48 : ℚ), (137 / 384 : ℚ), (3 / 8 : ℚ), (145 / 384 : ℚ)⟩
private def node_84 : Tree := C037.tree
private theorem node_84_accepts : node_84.Accepts parameters box_84 := C037.accepted

private def box_85 : Rectangle := ⟨(17 / 48 : ℚ), (137 / 384 : ℚ), (145 / 384 : ℚ), (73 / 192 : ℚ)⟩
private def node_85 : Tree := C038.tree
private theorem node_85_accepts : node_85.Accepts parameters box_85 := C038.accepted

private def box_83 : Rectangle := ⟨(17 / 48 : ℚ), (137 / 384 : ℚ), (3 / 8 : ℚ), (73 / 192 : ℚ)⟩
private def node_83 : Tree := .splitD (145 / 384 : ℚ) node_84 node_85
private theorem node_83_accepts : node_83.Accepts parameters box_83 := by
  change SplitDValid box_83 (145 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_83], node_84_accepts, node_85_accepts⟩

private def box_87 : Rectangle := ⟨(137 / 384 : ℚ), (23 / 64 : ℚ), (3 / 8 : ℚ), (145 / 384 : ℚ)⟩
private def node_87 : Tree := C039.tree
private theorem node_87_accepts : node_87.Accepts parameters box_87 := C039.accepted

private def box_88 : Rectangle := ⟨(137 / 384 : ℚ), (23 / 64 : ℚ), (145 / 384 : ℚ), (73 / 192 : ℚ)⟩
private def node_88 : Tree := C040.tree
private theorem node_88_accepts : node_88.Accepts parameters box_88 := C040.accepted

private def box_86 : Rectangle := ⟨(137 / 384 : ℚ), (23 / 64 : ℚ), (3 / 8 : ℚ), (73 / 192 : ℚ)⟩
private def node_86 : Tree := .splitD (145 / 384 : ℚ) node_87 node_88
private theorem node_86_accepts : node_86.Accepts parameters box_86 := by
  change SplitDValid box_86 (145 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_86], node_87_accepts, node_88_accepts⟩

private def box_82 : Rectangle := ⟨(17 / 48 : ℚ), (23 / 64 : ℚ), (3 / 8 : ℚ), (73 / 192 : ℚ)⟩
private def node_82 : Tree := .splitC (137 / 384 : ℚ) node_83 node_86
private theorem node_82_accepts : node_82.Accepts parameters box_82 := by
  change SplitCValid box_82 (137 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_82], node_83_accepts, node_86_accepts⟩

private def box_89 : Rectangle := ⟨(17 / 48 : ℚ), (23 / 64 : ℚ), (73 / 192 : ℚ), (37 / 96 : ℚ)⟩
private def node_89 : Tree := C041.tree
private theorem node_89_accepts : node_89.Accepts parameters box_89 := C041.accepted

private def box_81 : Rectangle := ⟨(17 / 48 : ℚ), (23 / 64 : ℚ), (3 / 8 : ℚ), (37 / 96 : ℚ)⟩
private def node_81 : Tree := .splitD (73 / 192 : ℚ) node_82 node_89
private theorem node_81_accepts : node_81.Accepts parameters box_81 := by
  change SplitDValid box_81 (73 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_81], node_82_accepts, node_89_accepts⟩

private def box_93 : Rectangle := ⟨(23 / 64 : ℚ), (139 / 384 : ℚ), (3 / 8 : ℚ), (145 / 384 : ℚ)⟩
private def node_93 : Tree := C042.tree
private theorem node_93_accepts : node_93.Accepts parameters box_93 := C042.accepted

private def box_94 : Rectangle := ⟨(23 / 64 : ℚ), (139 / 384 : ℚ), (145 / 384 : ℚ), (73 / 192 : ℚ)⟩
private def node_94 : Tree := C043.tree
private theorem node_94_accepts : node_94.Accepts parameters box_94 := C043.accepted

private def box_92 : Rectangle := ⟨(23 / 64 : ℚ), (139 / 384 : ℚ), (3 / 8 : ℚ), (73 / 192 : ℚ)⟩
private def node_92 : Tree := .splitD (145 / 384 : ℚ) node_93 node_94
private theorem node_92_accepts : node_92.Accepts parameters box_92 := by
  change SplitDValid box_92 (145 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_92], node_93_accepts, node_94_accepts⟩

private def box_96 : Rectangle := ⟨(139 / 384 : ℚ), (35 / 96 : ℚ), (3 / 8 : ℚ), (145 / 384 : ℚ)⟩
private def node_96 : Tree := C044.tree
private theorem node_96_accepts : node_96.Accepts parameters box_96 := C044.accepted

private def box_97 : Rectangle := ⟨(139 / 384 : ℚ), (35 / 96 : ℚ), (145 / 384 : ℚ), (73 / 192 : ℚ)⟩
private def node_97 : Tree := C045.tree
private theorem node_97_accepts : node_97.Accepts parameters box_97 := C045.accepted

private def box_95 : Rectangle := ⟨(139 / 384 : ℚ), (35 / 96 : ℚ), (3 / 8 : ℚ), (73 / 192 : ℚ)⟩
private def node_95 : Tree := .splitD (145 / 384 : ℚ) node_96 node_97
private theorem node_95_accepts : node_95.Accepts parameters box_95 := by
  change SplitDValid box_95 (145 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_95], node_96_accepts, node_97_accepts⟩

private def box_91 : Rectangle := ⟨(23 / 64 : ℚ), (35 / 96 : ℚ), (3 / 8 : ℚ), (73 / 192 : ℚ)⟩
private def node_91 : Tree := .splitC (139 / 384 : ℚ) node_92 node_95
private theorem node_91_accepts : node_91.Accepts parameters box_91 := by
  change SplitCValid box_91 (139 / 384 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_91], node_92_accepts, node_95_accepts⟩

private def box_98 : Rectangle := ⟨(23 / 64 : ℚ), (35 / 96 : ℚ), (73 / 192 : ℚ), (37 / 96 : ℚ)⟩
private def node_98 : Tree := C046.tree
private theorem node_98_accepts : node_98.Accepts parameters box_98 := C046.accepted

private def box_90 : Rectangle := ⟨(23 / 64 : ℚ), (35 / 96 : ℚ), (3 / 8 : ℚ), (37 / 96 : ℚ)⟩
private def node_90 : Tree := .splitD (73 / 192 : ℚ) node_91 node_98
private theorem node_90_accepts : node_90.Accepts parameters box_90 := by
  change SplitDValid box_90 (73 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_90], node_91_accepts, node_98_accepts⟩

private def box_80 : Rectangle := ⟨(17 / 48 : ℚ), (35 / 96 : ℚ), (3 / 8 : ℚ), (37 / 96 : ℚ)⟩
private def node_80 : Tree := .splitC (23 / 64 : ℚ) node_81 node_90
private theorem node_80_accepts : node_80.Accepts parameters box_80 := by
  change SplitCValid box_80 (23 / 64 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_80], node_81_accepts, node_90_accepts⟩

private def box_100 : Rectangle := ⟨(17 / 48 : ℚ), (23 / 64 : ℚ), (37 / 96 : ℚ), (19 / 48 : ℚ)⟩
private def node_100 : Tree := C047.tree
private theorem node_100_accepts : node_100.Accepts parameters box_100 := C047.accepted

private def box_102 : Rectangle := ⟨(23 / 64 : ℚ), (35 / 96 : ℚ), (37 / 96 : ℚ), (25 / 64 : ℚ)⟩
private def node_102 : Tree := C048.tree
private theorem node_102_accepts : node_102.Accepts parameters box_102 := C048.accepted

private def box_103 : Rectangle := ⟨(23 / 64 : ℚ), (35 / 96 : ℚ), (25 / 64 : ℚ), (19 / 48 : ℚ)⟩
private def node_103 : Tree := C049.tree
private theorem node_103_accepts : node_103.Accepts parameters box_103 := C049.accepted

private def box_101 : Rectangle := ⟨(23 / 64 : ℚ), (35 / 96 : ℚ), (37 / 96 : ℚ), (19 / 48 : ℚ)⟩
private def node_101 : Tree := .splitD (25 / 64 : ℚ) node_102 node_103
private theorem node_101_accepts : node_101.Accepts parameters box_101 := by
  change SplitDValid box_101 (25 / 64 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_101], node_102_accepts, node_103_accepts⟩

private def box_99 : Rectangle := ⟨(17 / 48 : ℚ), (35 / 96 : ℚ), (37 / 96 : ℚ), (19 / 48 : ℚ)⟩
private def node_99 : Tree := .splitC (23 / 64 : ℚ) node_100 node_101
private theorem node_99_accepts : node_99.Accepts parameters box_99 := by
  change SplitCValid box_99 (23 / 64 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_99], node_100_accepts, node_101_accepts⟩

private def box_79 : Rectangle := ⟨(17 / 48 : ℚ), (35 / 96 : ℚ), (3 / 8 : ℚ), (19 / 48 : ℚ)⟩
private def node_79 : Tree := .splitD (37 / 96 : ℚ) node_80 node_99
private theorem node_79_accepts : node_79.Accepts parameters box_79 := by
  change SplitDValid box_79 (37 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_79], node_80_accepts, node_99_accepts⟩

private def box_108 : Rectangle := ⟨(35 / 96 : ℚ), (47 / 128 : ℚ), (3 / 8 : ℚ), (73 / 192 : ℚ)⟩
private def node_108 : Tree := C050.tree
private theorem node_108_accepts : node_108.Accepts parameters box_108 := C050.accepted

private def box_109 : Rectangle := ⟨(47 / 128 : ℚ), (71 / 192 : ℚ), (3 / 8 : ℚ), (73 / 192 : ℚ)⟩
private def node_109 : Tree := C051.tree
private theorem node_109_accepts : node_109.Accepts parameters box_109 := C051.accepted

private def box_107 : Rectangle := ⟨(35 / 96 : ℚ), (71 / 192 : ℚ), (3 / 8 : ℚ), (73 / 192 : ℚ)⟩
private def node_107 : Tree := .splitC (47 / 128 : ℚ) node_108 node_109
private theorem node_107_accepts : node_107.Accepts parameters box_107 := by
  change SplitCValid box_107 (47 / 128 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_107], node_108_accepts, node_109_accepts⟩

private def box_110 : Rectangle := ⟨(35 / 96 : ℚ), (71 / 192 : ℚ), (73 / 192 : ℚ), (37 / 96 : ℚ)⟩
private def node_110 : Tree := C052.tree
private theorem node_110_accepts : node_110.Accepts parameters box_110 := C052.accepted

private def box_106 : Rectangle := ⟨(35 / 96 : ℚ), (71 / 192 : ℚ), (3 / 8 : ℚ), (37 / 96 : ℚ)⟩
private def node_106 : Tree := .splitD (73 / 192 : ℚ) node_107 node_110
private theorem node_106_accepts : node_106.Accepts parameters box_106 := by
  change SplitDValid box_106 (73 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_106], node_107_accepts, node_110_accepts⟩

private def box_112 : Rectangle := ⟨(71 / 192 : ℚ), (3 / 8 : ℚ), (3 / 8 : ℚ), (73 / 192 : ℚ)⟩
private def node_112 : Tree := C053.tree
private theorem node_112_accepts : node_112.Accepts parameters box_112 := C053.accepted

private def box_113 : Rectangle := ⟨(71 / 192 : ℚ), (3 / 8 : ℚ), (73 / 192 : ℚ), (37 / 96 : ℚ)⟩
private def node_113 : Tree := C054.tree
private theorem node_113_accepts : node_113.Accepts parameters box_113 := C054.accepted

private def box_111 : Rectangle := ⟨(71 / 192 : ℚ), (3 / 8 : ℚ), (3 / 8 : ℚ), (37 / 96 : ℚ)⟩
private def node_111 : Tree := .splitD (73 / 192 : ℚ) node_112 node_113
private theorem node_111_accepts : node_111.Accepts parameters box_111 := by
  change SplitDValid box_111 (73 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_111], node_112_accepts, node_113_accepts⟩

private def box_105 : Rectangle := ⟨(35 / 96 : ℚ), (3 / 8 : ℚ), (3 / 8 : ℚ), (37 / 96 : ℚ)⟩
private def node_105 : Tree := .splitC (71 / 192 : ℚ) node_106 node_111
private theorem node_105_accepts : node_105.Accepts parameters box_105 := by
  change SplitCValid box_105 (71 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_105], node_106_accepts, node_111_accepts⟩

private def box_115 : Rectangle := ⟨(35 / 96 : ℚ), (71 / 192 : ℚ), (37 / 96 : ℚ), (19 / 48 : ℚ)⟩
private def node_115 : Tree := C055.tree
private theorem node_115_accepts : node_115.Accepts parameters box_115 := C055.accepted

private def box_116 : Rectangle := ⟨(71 / 192 : ℚ), (3 / 8 : ℚ), (37 / 96 : ℚ), (19 / 48 : ℚ)⟩
private def node_116 : Tree := C056.tree
private theorem node_116_accepts : node_116.Accepts parameters box_116 := C056.accepted

private def box_114 : Rectangle := ⟨(35 / 96 : ℚ), (3 / 8 : ℚ), (37 / 96 : ℚ), (19 / 48 : ℚ)⟩
private def node_114 : Tree := .splitC (71 / 192 : ℚ) node_115 node_116
private theorem node_114_accepts : node_114.Accepts parameters box_114 := by
  change SplitCValid box_114 (71 / 192 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_114], node_115_accepts, node_116_accepts⟩

private def box_104 : Rectangle := ⟨(35 / 96 : ℚ), (3 / 8 : ℚ), (3 / 8 : ℚ), (19 / 48 : ℚ)⟩
private def node_104 : Tree := .splitD (37 / 96 : ℚ) node_105 node_114
private theorem node_104_accepts : node_104.Accepts parameters box_104 := by
  change SplitDValid box_104 (37 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_104], node_105_accepts, node_114_accepts⟩

private def box_78 : Rectangle := ⟨(17 / 48 : ℚ), (3 / 8 : ℚ), (3 / 8 : ℚ), (19 / 48 : ℚ)⟩
private def node_78 : Tree := .splitC (35 / 96 : ℚ) node_79 node_104
private theorem node_78_accepts : node_78.Accepts parameters box_78 := by
  change SplitCValid box_78 (35 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_78], node_79_accepts, node_104_accepts⟩

private def box_118 : Rectangle := ⟨(17 / 48 : ℚ), (35 / 96 : ℚ), (19 / 48 : ℚ), (5 / 12 : ℚ)⟩
private def node_118 : Tree := C057.tree
private theorem node_118_accepts : node_118.Accepts parameters box_118 := C057.accepted

private def box_120 : Rectangle := ⟨(35 / 96 : ℚ), (3 / 8 : ℚ), (19 / 48 : ℚ), (13 / 32 : ℚ)⟩
private def node_120 : Tree := C058.tree
private theorem node_120_accepts : node_120.Accepts parameters box_120 := C058.accepted

private def box_121 : Rectangle := ⟨(35 / 96 : ℚ), (3 / 8 : ℚ), (13 / 32 : ℚ), (5 / 12 : ℚ)⟩
private def node_121 : Tree := C059.tree
private theorem node_121_accepts : node_121.Accepts parameters box_121 := C059.accepted

private def box_119 : Rectangle := ⟨(35 / 96 : ℚ), (3 / 8 : ℚ), (19 / 48 : ℚ), (5 / 12 : ℚ)⟩
private def node_119 : Tree := .splitD (13 / 32 : ℚ) node_120 node_121
private theorem node_119_accepts : node_119.Accepts parameters box_119 := by
  change SplitDValid box_119 (13 / 32 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_119], node_120_accepts, node_121_accepts⟩

private def box_117 : Rectangle := ⟨(17 / 48 : ℚ), (3 / 8 : ℚ), (19 / 48 : ℚ), (5 / 12 : ℚ)⟩
private def node_117 : Tree := .splitC (35 / 96 : ℚ) node_118 node_119
private theorem node_117_accepts : node_117.Accepts parameters box_117 := by
  change SplitCValid box_117 (35 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_117], node_118_accepts, node_119_accepts⟩

private def box_77 : Rectangle := ⟨(17 / 48 : ℚ), (3 / 8 : ℚ), (3 / 8 : ℚ), (5 / 12 : ℚ)⟩
private def node_77 : Tree := .splitD (19 / 48 : ℚ) node_78 node_117
private theorem node_77_accepts : node_77.Accepts parameters box_77 := by
  change SplitDValid box_77 (19 / 48 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_77], node_78_accepts, node_117_accepts⟩

private def box_51 : Rectangle := ⟨(1 / 3 : ℚ), (3 / 8 : ℚ), (3 / 8 : ℚ), (5 / 12 : ℚ)⟩
private def node_51 : Tree := .splitC (17 / 48 : ℚ) node_52 node_77
private theorem node_51_accepts : node_51.Accepts parameters box_51 := by
  change SplitCValid box_51 (17 / 48 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_51], node_52_accepts, node_77_accepts⟩

private def box_3 : Rectangle := ⟨(1 / 3 : ℚ), (3 / 8 : ℚ), (1 / 3 : ℚ), (5 / 12 : ℚ)⟩
private def node_3 : Tree := .splitD (3 / 8 : ℚ) node_4 node_51
private theorem node_3_accepts : node_3.Accepts parameters box_3 := by
  change SplitDValid box_3 (3 / 8 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_3], node_4_accepts, node_51_accepts⟩

private def box_125 : Rectangle := ⟨(3 / 8 : ℚ), (19 / 48 : ℚ), (1 / 3 : ℚ), (17 / 48 : ℚ)⟩
private def node_125 : Tree := C060.tree
private theorem node_125_accepts : node_125.Accepts parameters box_125 := C060.accepted

private def box_127 : Rectangle := ⟨(3 / 8 : ℚ), (37 / 96 : ℚ), (17 / 48 : ℚ), (3 / 8 : ℚ)⟩
private def node_127 : Tree := C061.tree
private theorem node_127_accepts : node_127.Accepts parameters box_127 := C061.accepted

private def box_128 : Rectangle := ⟨(37 / 96 : ℚ), (19 / 48 : ℚ), (17 / 48 : ℚ), (3 / 8 : ℚ)⟩
private def node_128 : Tree := C062.tree
private theorem node_128_accepts : node_128.Accepts parameters box_128 := C062.accepted

private def box_126 : Rectangle := ⟨(3 / 8 : ℚ), (19 / 48 : ℚ), (17 / 48 : ℚ), (3 / 8 : ℚ)⟩
private def node_126 : Tree := .splitC (37 / 96 : ℚ) node_127 node_128
private theorem node_126_accepts : node_126.Accepts parameters box_126 := by
  change SplitCValid box_126 (37 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_126], node_127_accepts, node_128_accepts⟩

private def box_124 : Rectangle := ⟨(3 / 8 : ℚ), (19 / 48 : ℚ), (1 / 3 : ℚ), (3 / 8 : ℚ)⟩
private def node_124 : Tree := .splitD (17 / 48 : ℚ) node_125 node_126
private theorem node_124_accepts : node_124.Accepts parameters box_124 := by
  change SplitDValid box_124 (17 / 48 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_124], node_125_accepts, node_126_accepts⟩

private def box_129 : Rectangle := ⟨(19 / 48 : ℚ), (5 / 12 : ℚ), (1 / 3 : ℚ), (3 / 8 : ℚ)⟩
private def node_129 : Tree := C063.tree
private theorem node_129_accepts : node_129.Accepts parameters box_129 := C063.accepted

private def box_123 : Rectangle := ⟨(3 / 8 : ℚ), (5 / 12 : ℚ), (1 / 3 : ℚ), (3 / 8 : ℚ)⟩
private def node_123 : Tree := .splitC (19 / 48 : ℚ) node_124 node_129
private theorem node_123_accepts : node_123.Accepts parameters box_123 := by
  change SplitCValid box_123 (19 / 48 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_123], node_124_accepts, node_129_accepts⟩

private def box_134 : Rectangle := ⟨(3 / 8 : ℚ), (37 / 96 : ℚ), (3 / 8 : ℚ), (37 / 96 : ℚ)⟩
private def node_134 : Tree := C064.tree
private theorem node_134_accepts : node_134.Accepts parameters box_134 := C064.accepted

private def box_135 : Rectangle := ⟨(3 / 8 : ℚ), (37 / 96 : ℚ), (37 / 96 : ℚ), (19 / 48 : ℚ)⟩
private def node_135 : Tree := C065.tree
private theorem node_135_accepts : node_135.Accepts parameters box_135 := C065.accepted

private def box_133 : Rectangle := ⟨(3 / 8 : ℚ), (37 / 96 : ℚ), (3 / 8 : ℚ), (19 / 48 : ℚ)⟩
private def node_133 : Tree := .splitD (37 / 96 : ℚ) node_134 node_135
private theorem node_133_accepts : node_133.Accepts parameters box_133 := by
  change SplitDValid box_133 (37 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_133], node_134_accepts, node_135_accepts⟩

private def box_136 : Rectangle := ⟨(37 / 96 : ℚ), (19 / 48 : ℚ), (3 / 8 : ℚ), (19 / 48 : ℚ)⟩
private def node_136 : Tree := C066.tree
private theorem node_136_accepts : node_136.Accepts parameters box_136 := C066.accepted

private def box_132 : Rectangle := ⟨(3 / 8 : ℚ), (19 / 48 : ℚ), (3 / 8 : ℚ), (19 / 48 : ℚ)⟩
private def node_132 : Tree := .splitC (37 / 96 : ℚ) node_133 node_136
private theorem node_132_accepts : node_132.Accepts parameters box_132 := by
  change SplitCValid box_132 (37 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_132], node_133_accepts, node_136_accepts⟩

private def box_138 : Rectangle := ⟨(3 / 8 : ℚ), (37 / 96 : ℚ), (19 / 48 : ℚ), (5 / 12 : ℚ)⟩
private def node_138 : Tree := C067.tree
private theorem node_138_accepts : node_138.Accepts parameters box_138 := C067.accepted

private def box_139 : Rectangle := ⟨(37 / 96 : ℚ), (19 / 48 : ℚ), (19 / 48 : ℚ), (5 / 12 : ℚ)⟩
private def node_139 : Tree := C068.tree
private theorem node_139_accepts : node_139.Accepts parameters box_139 := C068.accepted

private def box_137 : Rectangle := ⟨(3 / 8 : ℚ), (19 / 48 : ℚ), (19 / 48 : ℚ), (5 / 12 : ℚ)⟩
private def node_137 : Tree := .splitC (37 / 96 : ℚ) node_138 node_139
private theorem node_137_accepts : node_137.Accepts parameters box_137 := by
  change SplitCValid box_137 (37 / 96 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_137], node_138_accepts, node_139_accepts⟩

private def box_131 : Rectangle := ⟨(3 / 8 : ℚ), (19 / 48 : ℚ), (3 / 8 : ℚ), (5 / 12 : ℚ)⟩
private def node_131 : Tree := .splitD (19 / 48 : ℚ) node_132 node_137
private theorem node_131_accepts : node_131.Accepts parameters box_131 := by
  change SplitDValid box_131 (19 / 48 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_131], node_132_accepts, node_137_accepts⟩

private def box_140 : Rectangle := ⟨(19 / 48 : ℚ), (5 / 12 : ℚ), (3 / 8 : ℚ), (5 / 12 : ℚ)⟩
private def node_140 : Tree := C069.tree
private theorem node_140_accepts : node_140.Accepts parameters box_140 := C069.accepted

private def box_130 : Rectangle := ⟨(3 / 8 : ℚ), (5 / 12 : ℚ), (3 / 8 : ℚ), (5 / 12 : ℚ)⟩
private def node_130 : Tree := .splitC (19 / 48 : ℚ) node_131 node_140
private theorem node_130_accepts : node_130.Accepts parameters box_130 := by
  change SplitCValid box_130 (19 / 48 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_130], node_131_accepts, node_140_accepts⟩

private def box_122 : Rectangle := ⟨(3 / 8 : ℚ), (5 / 12 : ℚ), (1 / 3 : ℚ), (5 / 12 : ℚ)⟩
private def node_122 : Tree := .splitD (3 / 8 : ℚ) node_123 node_130
private theorem node_122_accepts : node_122.Accepts parameters box_122 := by
  change SplitDValid box_122 (3 / 8 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_122], node_123_accepts, node_130_accepts⟩

private def box_2 : Rectangle := ⟨(1 / 3 : ℚ), (5 / 12 : ℚ), (1 / 3 : ℚ), (5 / 12 : ℚ)⟩
private def node_2 : Tree := .splitC (3 / 8 : ℚ) node_3 node_122
private theorem node_2_accepts : node_2.Accepts parameters box_2 := by
  change SplitCValid box_2 (3 / 8 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_2], node_3_accepts, node_122_accepts⟩

private def box_142 : Rectangle := ⟨(1 / 3 : ℚ), (3 / 8 : ℚ), (5 / 12 : ℚ), (1 / 2 : ℚ)⟩
private def node_142 : Tree := C070.tree
private theorem node_142_accepts : node_142.Accepts parameters box_142 := C070.accepted

private def box_144 : Rectangle := ⟨(3 / 8 : ℚ), (5 / 12 : ℚ), (5 / 12 : ℚ), (11 / 24 : ℚ)⟩
private def node_144 : Tree := C071.tree
private theorem node_144_accepts : node_144.Accepts parameters box_144 := C071.accepted

private def box_145 : Rectangle := ⟨(3 / 8 : ℚ), (5 / 12 : ℚ), (11 / 24 : ℚ), (1 / 2 : ℚ)⟩
private def node_145 : Tree := C072.tree
private theorem node_145_accepts : node_145.Accepts parameters box_145 := C072.accepted

private def box_143 : Rectangle := ⟨(3 / 8 : ℚ), (5 / 12 : ℚ), (5 / 12 : ℚ), (1 / 2 : ℚ)⟩
private def node_143 : Tree := .splitD (11 / 24 : ℚ) node_144 node_145
private theorem node_143_accepts : node_143.Accepts parameters box_143 := by
  change SplitDValid box_143 (11 / 24 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_143], node_144_accepts, node_145_accepts⟩

private def box_141 : Rectangle := ⟨(1 / 3 : ℚ), (5 / 12 : ℚ), (5 / 12 : ℚ), (1 / 2 : ℚ)⟩
private def node_141 : Tree := .splitC (3 / 8 : ℚ) node_142 node_143
private theorem node_141_accepts : node_141.Accepts parameters box_141 := by
  change SplitCValid box_141 (3 / 8 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_141], node_142_accepts, node_143_accepts⟩

private def box_1 : Rectangle := ⟨(1 / 3 : ℚ), (5 / 12 : ℚ), (1 / 3 : ℚ), (1 / 2 : ℚ)⟩
private def node_1 : Tree := .splitD (5 / 12 : ℚ) node_2 node_141
private theorem node_1_accepts : node_1.Accepts parameters box_1 := by
  change SplitDValid box_1 (5 / 12 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitDValid, box_1], node_2_accepts, node_141_accepts⟩

private def box_146 : Rectangle := ⟨(5 / 12 : ℚ), (1 / 2 : ℚ), (1 / 3 : ℚ), (1 / 2 : ℚ)⟩
private def node_146 : Tree := C073.tree
private theorem node_146_accepts : node_146.Accepts parameters box_146 := C073.accepted

private def box_0 : Rectangle := ⟨(1 / 3 : ℚ), (1 / 2 : ℚ), (1 / 3 : ℚ), (1 / 2 : ℚ)⟩
private def node_0 : Tree := .splitC (5 / 12 : ℚ) node_1 node_146
private theorem node_0_accepts : node_0.Accepts parameters box_0 := by
  change SplitCValid box_0 (5 / 12 : ℚ) ∧ _ ∧ _
  exact ⟨by norm_num [SplitCValid, box_0], node_1_accepts, node_146_accepts⟩

def tree : Tree := node_0
theorem accepted : tree.Accepts parameters (rootRectangle parameters.q) := by
  have hb : box_0 = rootRectangle parameters.q := by
    norm_num [box_0, rootRectangle, parameters]
  simpa only [tree, ← hb] using node_0_accepts

theorem checked : tree.check parameters (rootRectangle parameters.q) = true :=
  (tree.check_eq_true_iff parameters (rootRectangle parameters.q)).mpr accepted

#print axioms accepted
#print axioms checked

end CubeSections.Certificates.Data.Q2M1L2
