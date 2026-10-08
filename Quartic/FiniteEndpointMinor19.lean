import Quartic.FiniteEndpointMetadata19Data
import Quartic.FiniteEndpointCoefficientMinor
import Quartic.FiniteEndpointLookup

/-! Checked coefficient minor for the actual supplied 19-variable quadrics. -/
namespace Quartic.FiniteEndpointMinor19
noncomputable section
open FiniteEndpointChecker FiniteEndpointLookup
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000

private def columnTable : Table (Fin 190) := (.node 22 (.node 11 (.node 5 (.node 2 (.node 1 (.leaf 189) (.leaf 188)) (.node 3 (.leaf 187) (.node 4 (.leaf 185) (.leaf 182)))) (.node 8 (.node 6 (.leaf 186) (.node 7 (.leaf 183) (.leaf 184))) (.node 9 (.leaf 177) (.node 10 (.leaf 180) (.leaf 178))))) (.node 16 (.node 13 (.node 12 (.leaf 181) (.leaf 176)) (.node 14 (.leaf 179) (.node 15 (.leaf 175) (.leaf 173)))) (.node 19 (.node 17 (.leaf 174) (.node 18 (.leaf 166) (.leaf 172))) (.node 20 (.leaf 171) (.node 21 (.leaf 170) (.leaf 169)))))) (.node 33 (.node 27 (.node 24 (.node 23 (.leaf 165) (.leaf 168)) (.node 25 (.leaf 167) (.node 26 (.leaf 162) (.leaf 161)))) (.node 30 (.node 28 (.leaf 164) (.node 29 (.leaf 158) (.leaf 163))) (.node 31 (.leaf 155) (.node 32 (.leaf 159) (.leaf 156))))) (.node 38 (.node 35 (.node 34 (.leaf 154) (.leaf 160)) (.node 36 (.leaf 157) (.node 37 (.leaf 153) (.leaf 152)))) (.node 41 (.node 39 (.leaf 150) (.node 40 (.leaf 151) (.leaf 147))) (.node 42 (.leaf 148) (.node 43 (.leaf 146) (.leaf 149)))))))
private def inverseTable : Table Nat := (.node 22 (.node 11 (.node 5 (.node 2 (.node 1 (.leaf 8088529280439) (.leaf 6925247025610)) (.node 3 (.leaf 1966755979187) (.node 4 (.leaf 12790052608312) (.leaf 16023893401003)))) (.node 8 (.node 6 (.leaf 14752104201076) (.node 7 (.leaf 1923140986107) (.leaf 7413715159008))) (.node 9 (.leaf 11273867938388) (.node 10 (.leaf 15739515253409) (.leaf 7086138915659))))) (.node 16 (.node 13 (.node 12 (.leaf 1674697854355) (.leaf 8348727056563)) (.node 14 (.leaf 14678689580478) (.node 15 (.leaf 8490135925717) (.leaf 8245534793966)))) (.node 19 (.node 17 (.leaf 7421933002872) (.node 18 (.leaf 16102180939457) (.leaf 9604359522062))) (.node 20 (.leaf 14314265429103) (.node 21 (.leaf 14405596824805) (.leaf 15621107827525)))))) (.node 33 (.node 27 (.node 24 (.node 23 (.leaf 28460511537) (.leaf 4110101447879)) (.node 25 (.leaf 14746520752984) (.node 26 (.leaf 4501446952353) (.leaf 14727177416494)))) (.node 30 (.node 28 (.leaf 1252461859176) (.node 29 (.leaf 14850068883210) (.leaf 16841257399356))) (.node 31 (.leaf 12919046272579) (.node 32 (.leaf 2500803622913) (.leaf 1223181169228))))) (.node 38 (.node 35 (.node 34 (.leaf 799116422279) (.leaf 9039747540334)) (.node 36 (.leaf 2010542857203) (.node 37 (.leaf 9455228018169) (.leaf 5038500513782)))) (.node 41 (.node 39 (.leaf 1402575117378) (.node 40 (.leaf 1804183051287) (.leaf 1108039977564))) (.node 42 (.leaf 5588999123208) (.node 43 (.leaf 7501525249993) (.leaf 17269006716007)))))))
def columns (i : Fin 44) : Fin 190 := columnTable.get i.val
def rows (i : Fin 44) : List (Fin 44) :=
  FiniteEndpointCoefficientMinor.rows
    (fun k : Fin 44 => FiniteEndpointMetadata19Data.coefficients.get k.val) columns i
def inverse (i : Fin 44) : Nat := inverseTable.get i.val

theorem inverse_checked : checkInverse rows inverse = true := by decide +kernel

theorem counts (i j : Fin 44) :
    (FiniteEndpointMetadata19Data.quadSupport i).count (columns j) = (rows i).count j :=
  FiniteEndpointCoefficientMinor.counts
    (fun k : Fin 44 => FiniteEndpointMetadata19Data.coefficients.get k.val) columns i j

end
end Quartic.FiniteEndpointMinor19
