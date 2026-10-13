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
def closure_0 : List Shape := [⟨0,3,6⟩,⟨0,4,9⟩,⟨0,5,8⟩,⟨1,4,8⟩,⟨2,6,9⟩,⟨3,5,9⟩,⟨3,7,11⟩,⟨4,7,10⟩]
theorem closure_certificate_0 : closureCertificate ⟨0,3,6⟩ closure_0 = true := by
  simp only [closureCertificate, closure_0, List.all_cons, List.all_nil,
    List.filter_cons, List.filter_nil, successor_0, successor_1, successor_2, successor_3, successor_4, successor_5, successor_6, successor_7, successor_8, successor_9, successor_10, successor_11, successor_12, successor_13, successor_14, successor_15, successor_16, successor_17, successor_18, successor_19, successor_20, successor_21, successor_22, successor_23, successor_24, successor_25, successor_26, successor_27, successor_28, successor_29, successor_30, successor_31, successor_32, successor_33, successor_34, successor_35, successor_36, successor_37, successor_38, successor_39, successor_40, successor_41, successor_42, successor_43, successor_44, successor_45, successor_46, successor_47, successor_48, successor_49, successor_50, successor_51, successor_52, successor_53, successor_54]
  decide
#print axioms closure_certificate_0

def closure_1 : List Shape := [⟨0,3,7⟩,⟨0,5,9⟩,⟨1,5,8⟩,⟨3,6,9⟩,⟨4,7,11⟩]
theorem closure_certificate_1 : closureCertificate ⟨0,3,7⟩ closure_1 = true := by
  simp only [closureCertificate, closure_1, List.all_cons, List.all_nil,
    List.filter_cons, List.filter_nil, successor_0, successor_1, successor_2, successor_3, successor_4, successor_5, successor_6, successor_7, successor_8, successor_9, successor_10, successor_11, successor_12, successor_13, successor_14, successor_15, successor_16, successor_17, successor_18, successor_19, successor_20, successor_21, successor_22, successor_23, successor_24, successor_25, successor_26, successor_27, successor_28, successor_29, successor_30, successor_31, successor_32, successor_33, successor_34, successor_35, successor_36, successor_37, successor_38, successor_39, successor_40, successor_41, successor_42, successor_43, successor_44, successor_45, successor_46, successor_47, successor_48, successor_49, successor_50, successor_51, successor_52, successor_53, successor_54]
  decide
#print axioms closure_certificate_1

def closure_2 : List Shape := [⟨0,3,8⟩,⟨0,4,7⟩,⟨0,6,9⟩,⟨1,5,9⟩,⟨2,5,8⟩,⟨3,6,10⟩,⟨3,7,9⟩,⟨4,6,9⟩,⟨4,8,11⟩]
theorem closure_certificate_2 : closureCertificate ⟨0,3,8⟩ closure_2 = true := by
  simp only [closureCertificate, closure_2, List.all_cons, List.all_nil,
    List.filter_cons, List.filter_nil, successor_0, successor_1, successor_2, successor_3, successor_4, successor_5, successor_6, successor_7, successor_8, successor_9, successor_10, successor_11, successor_12, successor_13, successor_14, successor_15, successor_16, successor_17, successor_18, successor_19, successor_20, successor_21, successor_22, successor_23, successor_24, successor_25, successor_26, successor_27, successor_28, successor_29, successor_30, successor_31, successor_32, successor_33, successor_34, successor_35, successor_36, successor_37, successor_38, successor_39, successor_40, successor_41, successor_42, successor_43, successor_44, successor_45, successor_46, successor_47, successor_48, successor_49, successor_50, successor_51, successor_52, successor_53, successor_54]
  decide
#print axioms closure_certificate_2

def closure_3 : List Shape := [⟨0,3,9⟩]
theorem closure_certificate_3 : closureCertificate ⟨0,3,9⟩ closure_3 = true := by
  simp only [closureCertificate, closure_3, List.all_cons, List.all_nil,
    List.filter_cons, List.filter_nil, successor_0, successor_1, successor_2, successor_3, successor_4, successor_5, successor_6, successor_7, successor_8, successor_9, successor_10, successor_11, successor_12, successor_13, successor_14, successor_15, successor_16, successor_17, successor_18, successor_19, successor_20, successor_21, successor_22, successor_23, successor_24, successor_25, successor_26, successor_27, successor_28, successor_29, successor_30, successor_31, successor_32, successor_33, successor_34, successor_35, successor_36, successor_37, successor_38, successor_39, successor_40, successor_41, successor_42, successor_43, successor_44, successor_45, successor_46, successor_47, successor_48, successor_49, successor_50, successor_51, successor_52, successor_53, successor_54]
  decide
#print axioms closure_certificate_3

def closure_4 : List Shape := [⟨0,4,7⟩,⟨0,6,9⟩,⟨1,5,9⟩,⟨2,5,8⟩,⟨3,6,10⟩,⟨3,7,9⟩,⟨4,6,9⟩,⟨4,8,11⟩]
theorem closure_certificate_4 : closureCertificate ⟨0,4,7⟩ closure_4 = true := by
  simp only [closureCertificate, closure_4, List.all_cons, List.all_nil,
    List.filter_cons, List.filter_nil, successor_0, successor_1, successor_2, successor_3, successor_4, successor_5, successor_6, successor_7, successor_8, successor_9, successor_10, successor_11, successor_12, successor_13, successor_14, successor_15, successor_16, successor_17, successor_18, successor_19, successor_20, successor_21, successor_22, successor_23, successor_24, successor_25, successor_26, successor_27, successor_28, successor_29, successor_30, successor_31, successor_32, successor_33, successor_34, successor_35, successor_36, successor_37, successor_38, successor_39, successor_40, successor_41, successor_42, successor_43, successor_44, successor_45, successor_46, successor_47, successor_48, successor_49, successor_50, successor_51, successor_52, successor_53, successor_54]
  decide
#print axioms closure_certificate_4

def closure_5 : List Shape := [⟨0,4,8⟩,⟨2,5,9⟩,⟨3,7,10⟩]
theorem closure_certificate_5 : closureCertificate ⟨0,4,8⟩ closure_5 = true := by
  simp only [closureCertificate, closure_5, List.all_cons, List.all_nil,
    List.filter_cons, List.filter_nil, successor_0, successor_1, successor_2, successor_3, successor_4, successor_5, successor_6, successor_7, successor_8, successor_9, successor_10, successor_11, successor_12, successor_13, successor_14, successor_15, successor_16, successor_17, successor_18, successor_19, successor_20, successor_21, successor_22, successor_23, successor_24, successor_25, successor_26, successor_27, successor_28, successor_29, successor_30, successor_31, successor_32, successor_33, successor_34, successor_35, successor_36, successor_37, successor_38, successor_39, successor_40, successor_41, successor_42, successor_43, successor_44, successor_45, successor_46, successor_47, successor_48, successor_49, successor_50, successor_51, successor_52, successor_53, successor_54]
  decide
#print axioms closure_certificate_5

def closure_6 : List Shape := [⟨0,4,9⟩]
theorem closure_certificate_6 : closureCertificate ⟨0,4,9⟩ closure_6 = true := by
  simp only [closureCertificate, closure_6, List.all_cons, List.all_nil,
    List.filter_cons, List.filter_nil, successor_0, successor_1, successor_2, successor_3, successor_4, successor_5, successor_6, successor_7, successor_8, successor_9, successor_10, successor_11, successor_12, successor_13, successor_14, successor_15, successor_16, successor_17, successor_18, successor_19, successor_20, successor_21, successor_22, successor_23, successor_24, successor_25, successor_26, successor_27, successor_28, successor_29, successor_30, successor_31, successor_32, successor_33, successor_34, successor_35, successor_36, successor_37, successor_38, successor_39, successor_40, successor_41, successor_42, successor_43, successor_44, successor_45, successor_46, successor_47, successor_48, successor_49, successor_50, successor_51, successor_52, successor_53, successor_54]
  decide
#print axioms closure_certificate_6

def closure_7 : List Shape := [⟨0,4,9⟩,⟨0,5,8⟩,⟨1,4,8⟩,⟨2,6,9⟩,⟨3,5,9⟩,⟨3,7,11⟩,⟨4,7,10⟩]
theorem closure_certificate_7 : closureCertificate ⟨0,5,8⟩ closure_7 = true := by
  simp only [closureCertificate, closure_7, List.all_cons, List.all_nil,
    List.filter_cons, List.filter_nil, successor_0, successor_1, successor_2, successor_3, successor_4, successor_5, successor_6, successor_7, successor_8, successor_9, successor_10, successor_11, successor_12, successor_13, successor_14, successor_15, successor_16, successor_17, successor_18, successor_19, successor_20, successor_21, successor_22, successor_23, successor_24, successor_25, successor_26, successor_27, successor_28, successor_29, successor_30, successor_31, successor_32, successor_33, successor_34, successor_35, successor_36, successor_37, successor_38, successor_39, successor_40, successor_41, successor_42, successor_43, successor_44, successor_45, successor_46, successor_47, successor_48, successor_49, successor_50, successor_51, successor_52, successor_53, successor_54]
  decide
#print axioms closure_certificate_7

end Omnibus
