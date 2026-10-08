import Quartic.FiniteEndpointMetadata18Data
import Quartic.FiniteEndpointCoefficientMinor
import Quartic.FiniteEndpointLookup

/-! Checked coefficient minor for the actual supplied 18-variable quadrics. -/
namespace Quartic.FiniteEndpointMinor18
noncomputable section
open FiniteEndpointChecker FiniteEndpointLookup
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000

private def columnTable : Table (Fin 171) := (.node 20 (.node 10 (.node 5 (.node 2 (.node 1 (.leaf 170) (.leaf 167)) (.node 3 (.leaf 169) (.node 4 (.leaf 165) (.leaf 168)))) (.node 7 (.node 6 (.leaf 162) (.leaf 166)) (.node 8 (.leaf 161) (.node 9 (.leaf 159) (.leaf 164))))) (.node 15 (.node 12 (.node 11 (.leaf 157) (.leaf 163)) (.node 13 (.leaf 160) (.node 14 (.leaf 158) (.leaf 155)))) (.node 17 (.node 16 (.leaf 154) (.leaf 151)) (.node 18 (.leaf 152) (.node 19 (.leaf 156) (.leaf 150)))))) (.node 30 (.node 25 (.node 22 (.node 21 (.leaf 148) (.leaf 153)) (.node 23 (.leaf 144) (.node 24 (.leaf 147) (.leaf 149)))) (.node 27 (.node 26 (.leaf 143) (.leaf 145)) (.node 28 (.leaf 142) (.node 29 (.leaf 146) (.leaf 141))))) (.node 35 (.node 32 (.node 31 (.leaf 140) (.leaf 139)) (.node 33 (.leaf 137) (.node 34 (.leaf 136) (.leaf 133)))) (.node 37 (.node 36 (.leaf 132) (.leaf 135)) (.node 38 (.leaf 138) (.node 39 (.leaf 134) (.leaf 131)))))))
private def inverseTable : Table Nat := (.node 20 (.node 10 (.node 5 (.node 2 (.node 1 (.leaf 403867679245) (.leaf 94112754210)) (.node 3 (.leaf 1082501876456) (.node 4 (.leaf 279321244459) (.leaf 1058897155505)))) (.node 7 (.node 6 (.leaf 623778402926) (.leaf 726856292116)) (.node 8 (.leaf 788847590732) (.node 9 (.leaf 102486533093) (.leaf 243916525439))))) (.node 15 (.node 12 (.node 11 (.leaf 779521862332) (.leaf 598222374361)) (.node 13 (.leaf 841893125320) (.node 14 (.leaf 122501617680) (.leaf 596154155680)))) (.node 17 (.node 16 (.leaf 641923532458) (.leaf 1076919543362)) (.node 18 (.leaf 771972120276) (.node 19 (.leaf 34191385340) (.leaf 436056777235)))))) (.node 30 (.node 25 (.node 22 (.node 21 (.leaf 81198444674) (.leaf 979144074831)) (.node 23 (.leaf 1073345924633) (.node 24 (.leaf 1082078366860) (.leaf 102275346652)))) (.node 27 (.node 26 (.leaf 1090046958508) (.leaf 538629794848)) (.node 28 (.leaf 421258130611) (.node 29 (.leaf 946893966604) (.leaf 892398694343))))) (.node 35 (.node 32 (.node 31 (.leaf 387362845154) (.leaf 326405983824)) (.node 33 (.leaf 125019698502) (.node 34 (.leaf 647725677879) (.leaf 61015543144)))) (.node 37 (.node 36 (.leaf 41239714785) (.leaf 859317699061)) (.node 38 (.leaf 501579311045) (.node 39 (.leaf 309414167637) (.leaf 952451378810)))))))
def columns (i : Fin 40) : Fin 171 := columnTable.get i.val
def rows (i : Fin 40) : List (Fin 40) :=
  FiniteEndpointCoefficientMinor.rows
    (fun k : Fin 40 => FiniteEndpointMetadata18Data.coefficients.get k.val) columns i
def inverse (i : Fin 40) : Nat := inverseTable.get i.val

theorem inverse_checked : checkInverse rows inverse = true := by decide +kernel

theorem counts (i j : Fin 40) :
    (FiniteEndpointMetadata18Data.quadSupport i).count (columns j) = (rows i).count j :=
  FiniteEndpointCoefficientMinor.counts
    (fun k : Fin 40 => FiniteEndpointMetadata18Data.coefficients.get k.val) columns i j

end
end Quartic.FiniteEndpointMinor18
