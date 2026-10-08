import Quartic.FiniteEndpointMetadata23Data
import Quartic.FiniteEndpointCoefficientMinor
import Quartic.FiniteEndpointLookup

/-! Checked coefficient minor for the actual supplied 23-variable quadrics. -/
namespace Quartic.FiniteEndpointMinor23
noncomputable section
open FiniteEndpointChecker FiniteEndpointLookup
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000

private def columnTable : Table (Fin 276) := (.node 30 (.node 15 (.node 7 (.node 3 (.node 1 (.leaf 275) (.node 2 (.leaf 271) (.leaf 274))) (.node 5 (.node 4 (.leaf 269) (.leaf 272)) (.node 6 (.leaf 270) (.leaf 273)))) (.node 11 (.node 9 (.node 8 (.leaf 267) (.leaf 266)) (.node 10 (.leaf 265) (.leaf 264))) (.node 13 (.node 12 (.leaf 263) (.leaf 262)) (.node 14 (.leaf 261) (.leaf 268))))) (.node 22 (.node 18 (.node 16 (.leaf 260) (.node 17 (.leaf 256) (.leaf 257))) (.node 20 (.node 19 (.leaf 254) (.leaf 252)) (.node 21 (.leaf 259) (.leaf 258)))) (.node 26 (.node 24 (.node 23 (.leaf 253) (.leaf 251)) (.node 25 (.leaf 250) (.leaf 248))) (.node 28 (.node 27 (.leaf 247) (.leaf 255)) (.node 29 (.leaf 249) (.leaf 244)))))) (.node 45 (.node 37 (.node 33 (.node 31 (.leaf 243) (.node 32 (.leaf 246) (.leaf 241))) (.node 35 (.node 34 (.leaf 235) (.leaf 245)) (.node 36 (.leaf 240) (.leaf 238)))) (.node 41 (.node 39 (.node 38 (.leaf 242) (.leaf 237)) (.node 40 (.leaf 236) (.leaf 234))) (.node 43 (.node 42 (.leaf 231) (.leaf 239)) (.node 44 (.leaf 233) (.leaf 232))))) (.node 53 (.node 49 (.node 47 (.node 46 (.leaf 230) (.leaf 226)) (.node 48 (.leaf 225) (.leaf 229))) (.node 51 (.node 50 (.leaf 228) (.leaf 227)) (.node 52 (.leaf 224) (.leaf 223)))) (.node 57 (.node 55 (.node 54 (.leaf 222) (.leaf 219)) (.node 56 (.leaf 221) (.leaf 218))) (.node 59 (.node 58 (.leaf 216) (.leaf 217)) (.node 60 (.leaf 220) (.leaf 215)))))))
private def inverseTable : Table Nat := (.node 30 (.node 15 (.node 7 (.node 3 (.node 1 (.leaf 1103073843902501703) (.node 2 (.leaf 1833506155085715467) (.leaf 1525945069258828000))) (.node 5 (.node 4 (.leaf 1701625770025935456) (.leaf 1039415440279187239)) (.node 6 (.leaf 1152933965644601192) (.leaf 173123374190542229)))) (.node 11 (.node 9 (.node 8 (.leaf 935940674859358610) (.leaf 1164255821991905804)) (.node 10 (.leaf 1855346835439691230) (.leaf 1657567538887862760))) (.node 13 (.node 12 (.leaf 786148381773279690) (.leaf 1446713529029727159)) (.node 14 (.leaf 567542339301237894) (.leaf 748120185647696030))))) (.node 22 (.node 18 (.node 16 (.leaf 1336713947359231992) (.node 17 (.leaf 1685451878263797379) (.leaf 480444560555888303))) (.node 20 (.node 19 (.leaf 1304757658502589203) (.leaf 687959675595452056)) (.node 21 (.leaf 220613522585118278) (.leaf 2123635692864554663)))) (.node 26 (.node 24 (.node 23 (.leaf 1372784837321228371) (.leaf 165451380907784363)) (.node 25 (.leaf 2202108769672631938) (.leaf 2151316750583247774))) (.node 28 (.node 27 (.leaf 2232767375586734316) (.leaf 2037762954295608092)) (.node 29 (.leaf 494362910629888494) (.leaf 298600476538230638)))))) (.node 45 (.node 37 (.node 33 (.node 31 (.leaf 1114384864888066237) (.node 32 (.leaf 1217656053201686222) (.leaf 660498814420777628))) (.node 35 (.node 34 (.leaf 2013623364620324473) (.leaf 1342261147689761124)) (.node 36 (.leaf 1696979563871674071) (.leaf 712938552017316320)))) (.node 41 (.node 39 (.node 38 (.leaf 972912419198487734) (.leaf 1122883281044729693)) (.node 40 (.leaf 631921210669647973) (.leaf 1885621492706280335))) (.node 43 (.node 42 (.leaf 2203215360187756682) (.leaf 1406482970153414764)) (.node 44 (.leaf 1262723273061943120) (.leaf 1277846431578272596))))) (.node 53 (.node 49 (.node 47 (.node 46 (.leaf 30420250804336736) (.leaf 109880670726461891)) (.node 48 (.leaf 217997152345361983) (.leaf 297785891413090775))) (.node 51 (.node 50 (.leaf 1931006861197845453) (.leaf 1061687829355438607)) (.node 52 (.leaf 1234660767800143715) (.leaf 1039527686012894459)))) (.node 57 (.node 55 (.node 54 (.leaf 1377157082683497409) (.leaf 180417028191828804)) (.node 56 (.leaf 1700708981386655624) (.leaf 1436006122475016337))) (.node 59 (.node 58 (.leaf 1304717572431814236) (.leaf 1649413870423024539)) (.node 60 (.leaf 974355523943748528) (.leaf 1237542860924252893)))))))
def columns (i : Fin 61) : Fin 276 := columnTable.get i.val
def rows (i : Fin 61) : List (Fin 61) :=
  FiniteEndpointCoefficientMinor.rows
    (fun k : Fin 61 => FiniteEndpointMetadata23Data.coefficients.get k.val) columns i
def inverse (i : Fin 61) : Nat := inverseTable.get i.val

theorem inverse_checked : checkInverse rows inverse = true := by decide +kernel

theorem counts (i j : Fin 61) :
    (FiniteEndpointMetadata23Data.quadSupport i).count (columns j) = (rows i).count j :=
  FiniteEndpointCoefficientMinor.counts
    (fun k : Fin 61 => FiniteEndpointMetadata23Data.coefficients.get k.val) columns i j

end
end Quartic.FiniteEndpointMinor23
