import Quartic.FiniteEndpointMetadata17Data
import Quartic.FiniteEndpointCoefficientMinor
import Quartic.FiniteEndpointLookup

/-! Checked coefficient minor for the actual supplied 17-variable quadrics. -/
namespace Quartic.FiniteEndpointMinor17
noncomputable section
open FiniteEndpointChecker FiniteEndpointLookup
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000

private def columnTable : Table (Fin 153) := (.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf 152) (.leaf 151)) (.node 3 (.leaf 148) (.leaf 150))) (.node 6 (.node 5 (.leaf 147) (.leaf 149)) (.node 7 (.leaf 146) (.node 8 (.leaf 145) (.leaf 144))))) (.node 13 (.node 11 (.node 10 (.leaf 140) (.leaf 138)) (.node 12 (.leaf 139) (.leaf 137))) (.node 15 (.node 14 (.leaf 143) (.leaf 142)) (.node 16 (.leaf 141) (.node 17 (.leaf 133) (.leaf 136)))))) (.node 27 (.node 22 (.node 20 (.node 19 (.leaf 134) (.leaf 131)) (.node 21 (.leaf 130) (.leaf 135))) (.node 24 (.node 23 (.leaf 132) (.leaf 129)) (.node 25 (.leaf 126) (.node 26 (.leaf 127) (.leaf 128))))) (.node 31 (.node 29 (.node 28 (.leaf 124) (.leaf 118)) (.node 30 (.leaf 125) (.leaf 123))) (.node 33 (.node 32 (.leaf 122) (.leaf 120)) (.node 34 (.leaf 119) (.node 35 (.leaf 117) (.leaf 115)))))))
private def inverseTable : Table Nat := (.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf 54714560227) (.leaf 61261710847)) (.node 3 (.leaf 22488817179) (.leaf 65372433645))) (.node 6 (.node 5 (.leaf 37787009055) (.leaf 66727745558)) (.node 7 (.leaf 42922658405) (.node 8 (.leaf 13281076712) (.leaf 56697754039))))) (.node 13 (.node 11 (.node 10 (.leaf 44147759903) (.leaf 52263470635)) (.node 12 (.leaf 25699949701) (.leaf 67248837387))) (.node 15 (.node 14 (.leaf 56335408019) (.leaf 61955458289)) (.node 16 (.leaf 8465198069) (.node 17 (.leaf 30320803292) (.leaf 58185600764)))))) (.node 27 (.node 22 (.node 20 (.node 19 (.leaf 59520535680) (.leaf 24855026375)) (.node 21 (.leaf 42780626498) (.leaf 58074830687))) (.node 24 (.node 23 (.leaf 62647275341) (.leaf 30256705438)) (.node 25 (.leaf 262595017) (.node 26 (.leaf 21758615822) (.leaf 18398578032))))) (.node 31 (.node 29 (.node 28 (.leaf 33506289551) (.leaf 488724724)) (.node 30 (.leaf 26130565727) (.leaf 61324638016))) (.node 33 (.node 32 (.leaf 56758748935) (.leaf 43329195986)) (.node 34 (.leaf 63227541748) (.node 35 (.leaf 47412642388) (.leaf 54502315927)))))))
def columns (i : Fin 36) : Fin 153 := columnTable.get i.val
def rows (i : Fin 36) : List (Fin 36) :=
  FiniteEndpointCoefficientMinor.rows
    (fun k : Fin 36 => FiniteEndpointMetadata17Data.coefficients.get k.val) columns i
def inverse (i : Fin 36) : Nat := inverseTable.get i.val

theorem inverse_checked : checkInverse rows inverse = true := by decide +kernel

theorem counts (i j : Fin 36) :
    (FiniteEndpointMetadata17Data.quadSupport i).count (columns j) = (rows i).count j :=
  FiniteEndpointCoefficientMinor.counts
    (fun k : Fin 36 => FiniteEndpointMetadata17Data.coefficients.get k.val) columns i j

end
end Quartic.FiniteEndpointMinor17
