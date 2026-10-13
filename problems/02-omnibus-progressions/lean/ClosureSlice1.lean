import ClosureDefinitions
import EdgeSlice0
import EdgeSlice1
import EdgeSlice2
import EdgeSlice3
import EdgeSlice4
import EdgeSlice5
import EdgeSlice6

namespace Omnibus
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 100000
def closure_8 : List Shape := [⟨0,5,9⟩]
theorem closure_certificate_8 : closureCertificate ⟨0,5,9⟩ closure_8 = true := by
  simp only [closureCertificate, closure_8, List.all_cons, List.all_nil,
    List.filter_cons, List.filter_nil, successor_0, successor_1, successor_2, successor_3, successor_4, successor_5, successor_6, successor_7, successor_8, successor_9, successor_10, successor_11, successor_12, successor_13, successor_14, successor_15, successor_16, successor_17, successor_18, successor_19, successor_20, successor_21, successor_22, successor_23, successor_24, successor_25, successor_26, successor_27, successor_28, successor_29, successor_30, successor_31, successor_32, successor_33, successor_34, successor_35, successor_36, successor_37, successor_38, successor_39, successor_40, successor_41, successor_42, successor_43, successor_44, successor_45, successor_46, successor_47, successor_48, successor_49, successor_50, successor_51, successor_52, successor_53, successor_54]
  decide
#print axioms closure_certificate_8

def closure_9 : List Shape := [⟨0,6,9⟩]
theorem closure_certificate_9 : closureCertificate ⟨0,6,9⟩ closure_9 = true := by
  simp only [closureCertificate, closure_9, List.all_cons, List.all_nil,
    List.filter_cons, List.filter_nil, successor_0, successor_1, successor_2, successor_3, successor_4, successor_5, successor_6, successor_7, successor_8, successor_9, successor_10, successor_11, successor_12, successor_13, successor_14, successor_15, successor_16, successor_17, successor_18, successor_19, successor_20, successor_21, successor_22, successor_23, successor_24, successor_25, successor_26, successor_27, successor_28, successor_29, successor_30, successor_31, successor_32, successor_33, successor_34, successor_35, successor_36, successor_37, successor_38, successor_39, successor_40, successor_41, successor_42, successor_43, successor_44, successor_45, successor_46, successor_47, successor_48, successor_49, successor_50, successor_51, successor_52, successor_53, successor_54]
  decide
#print axioms closure_certificate_9

def closure_10 : List Shape := [⟨0,4,9⟩,⟨0,5,8⟩,⟨1,4,8⟩,⟨2,6,9⟩,⟨3,5,9⟩,⟨3,7,11⟩,⟨4,7,10⟩]
theorem closure_certificate_10 : closureCertificate ⟨1,4,8⟩ closure_10 = true := by
  simp only [closureCertificate, closure_10, List.all_cons, List.all_nil,
    List.filter_cons, List.filter_nil, successor_0, successor_1, successor_2, successor_3, successor_4, successor_5, successor_6, successor_7, successor_8, successor_9, successor_10, successor_11, successor_12, successor_13, successor_14, successor_15, successor_16, successor_17, successor_18, successor_19, successor_20, successor_21, successor_22, successor_23, successor_24, successor_25, successor_26, successor_27, successor_28, successor_29, successor_30, successor_31, successor_32, successor_33, successor_34, successor_35, successor_36, successor_37, successor_38, successor_39, successor_40, successor_41, successor_42, successor_43, successor_44, successor_45, successor_46, successor_47, successor_48, successor_49, successor_50, successor_51, successor_52, successor_53, successor_54]
  decide
#print axioms closure_certificate_10

def closure_11 : List Shape := [⟨0,5,9⟩,⟨1,5,8⟩,⟨3,6,9⟩,⟨4,7,11⟩]
theorem closure_certificate_11 : closureCertificate ⟨1,5,8⟩ closure_11 = true := by
  simp only [closureCertificate, closure_11, List.all_cons, List.all_nil,
    List.filter_cons, List.filter_nil, successor_0, successor_1, successor_2, successor_3, successor_4, successor_5, successor_6, successor_7, successor_8, successor_9, successor_10, successor_11, successor_12, successor_13, successor_14, successor_15, successor_16, successor_17, successor_18, successor_19, successor_20, successor_21, successor_22, successor_23, successor_24, successor_25, successor_26, successor_27, successor_28, successor_29, successor_30, successor_31, successor_32, successor_33, successor_34, successor_35, successor_36, successor_37, successor_38, successor_39, successor_40, successor_41, successor_42, successor_43, successor_44, successor_45, successor_46, successor_47, successor_48, successor_49, successor_50, successor_51, successor_52, successor_53, successor_54]
  decide
#print axioms closure_certificate_11

def closure_12 : List Shape := [⟨0,4,7⟩,⟨0,6,9⟩,⟨1,5,9⟩,⟨2,5,8⟩,⟨3,6,10⟩,⟨3,7,9⟩,⟨4,6,9⟩,⟨4,8,11⟩]
theorem closure_certificate_12 : closureCertificate ⟨1,5,9⟩ closure_12 = true := by
  simp only [closureCertificate, closure_12, List.all_cons, List.all_nil,
    List.filter_cons, List.filter_nil, successor_0, successor_1, successor_2, successor_3, successor_4, successor_5, successor_6, successor_7, successor_8, successor_9, successor_10, successor_11, successor_12, successor_13, successor_14, successor_15, successor_16, successor_17, successor_18, successor_19, successor_20, successor_21, successor_22, successor_23, successor_24, successor_25, successor_26, successor_27, successor_28, successor_29, successor_30, successor_31, successor_32, successor_33, successor_34, successor_35, successor_36, successor_37, successor_38, successor_39, successor_40, successor_41, successor_42, successor_43, successor_44, successor_45, successor_46, successor_47, successor_48, successor_49, successor_50, successor_51, successor_52, successor_53, successor_54]
  decide
#print axioms closure_certificate_12

def closure_13 : List Shape := [⟨0,4,7⟩,⟨0,6,9⟩,⟨1,5,9⟩,⟨2,5,8⟩,⟨3,6,10⟩,⟨3,7,9⟩,⟨4,6,9⟩,⟨4,8,11⟩]
theorem closure_certificate_13 : closureCertificate ⟨2,5,8⟩ closure_13 = true := by
  simp only [closureCertificate, closure_13, List.all_cons, List.all_nil,
    List.filter_cons, List.filter_nil, successor_0, successor_1, successor_2, successor_3, successor_4, successor_5, successor_6, successor_7, successor_8, successor_9, successor_10, successor_11, successor_12, successor_13, successor_14, successor_15, successor_16, successor_17, successor_18, successor_19, successor_20, successor_21, successor_22, successor_23, successor_24, successor_25, successor_26, successor_27, successor_28, successor_29, successor_30, successor_31, successor_32, successor_33, successor_34, successor_35, successor_36, successor_37, successor_38, successor_39, successor_40, successor_41, successor_42, successor_43, successor_44, successor_45, successor_46, successor_47, successor_48, successor_49, successor_50, successor_51, successor_52, successor_53, successor_54]
  decide
#print axioms closure_certificate_13

def closure_14 : List Shape := [⟨0,4,8⟩,⟨2,5,9⟩,⟨3,7,10⟩]
theorem closure_certificate_14 : closureCertificate ⟨2,5,9⟩ closure_14 = true := by
  simp only [closureCertificate, closure_14, List.all_cons, List.all_nil,
    List.filter_cons, List.filter_nil, successor_0, successor_1, successor_2, successor_3, successor_4, successor_5, successor_6, successor_7, successor_8, successor_9, successor_10, successor_11, successor_12, successor_13, successor_14, successor_15, successor_16, successor_17, successor_18, successor_19, successor_20, successor_21, successor_22, successor_23, successor_24, successor_25, successor_26, successor_27, successor_28, successor_29, successor_30, successor_31, successor_32, successor_33, successor_34, successor_35, successor_36, successor_37, successor_38, successor_39, successor_40, successor_41, successor_42, successor_43, successor_44, successor_45, successor_46, successor_47, successor_48, successor_49, successor_50, successor_51, successor_52, successor_53, successor_54]
  decide
#print axioms closure_certificate_14

def closure_15 : List Shape := [⟨0,4,9⟩,⟨0,5,8⟩,⟨1,4,8⟩,⟨2,6,9⟩,⟨3,5,9⟩,⟨3,7,11⟩,⟨4,7,10⟩]
theorem closure_certificate_15 : closureCertificate ⟨2,6,9⟩ closure_15 = true := by
  simp only [closureCertificate, closure_15, List.all_cons, List.all_nil,
    List.filter_cons, List.filter_nil, successor_0, successor_1, successor_2, successor_3, successor_4, successor_5, successor_6, successor_7, successor_8, successor_9, successor_10, successor_11, successor_12, successor_13, successor_14, successor_15, successor_16, successor_17, successor_18, successor_19, successor_20, successor_21, successor_22, successor_23, successor_24, successor_25, successor_26, successor_27, successor_28, successor_29, successor_30, successor_31, successor_32, successor_33, successor_34, successor_35, successor_36, successor_37, successor_38, successor_39, successor_40, successor_41, successor_42, successor_43, successor_44, successor_45, successor_46, successor_47, successor_48, successor_49, successor_50, successor_51, successor_52, successor_53, successor_54]
  decide
#print axioms closure_certificate_15

end Omnibus
