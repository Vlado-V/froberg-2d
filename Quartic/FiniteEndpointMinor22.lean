import Quartic.FiniteEndpointMetadata22Data
import Quartic.FiniteEndpointCoefficientMinor
import Quartic.FiniteEndpointLookup

/-! Checked coefficient minor for the actual supplied 22-variable quadrics. -/
namespace Quartic.FiniteEndpointMinor22
noncomputable section
open FiniteEndpointChecker FiniteEndpointLookup
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000

private def columnTable : Table (Fin 253) := (.node 28 (.node 14 (.node 7 (.node 3 (.node 1 (.leaf 252) (.node 2 (.leaf 251) (.leaf 248))) (.node 5 (.node 4 (.leaf 249) (.leaf 250)) (.node 6 (.leaf 245) (.leaf 246)))) (.node 10 (.node 8 (.leaf 247) (.node 9 (.leaf 244) (.leaf 243))) (.node 12 (.node 11 (.leaf 241) (.leaf 242)) (.node 13 (.leaf 238) (.leaf 240))))) (.node 21 (.node 17 (.node 15 (.leaf 236) (.node 16 (.leaf 237) (.leaf 233))) (.node 19 (.node 18 (.leaf 235) (.leaf 239)) (.node 20 (.leaf 231) (.leaf 234)))) (.node 24 (.node 22 (.leaf 232) (.node 23 (.leaf 230) (.leaf 226))) (.node 26 (.node 25 (.leaf 225) (.leaf 228)) (.node 27 (.leaf 227) (.leaf 229)))))) (.node 42 (.node 35 (.node 31 (.node 29 (.leaf 224) (.node 30 (.leaf 223) (.leaf 219))) (.node 33 (.node 32 (.leaf 222) (.leaf 218)) (.node 34 (.leaf 221) (.leaf 220)))) (.node 38 (.node 36 (.leaf 215) (.node 37 (.leaf 217) (.leaf 216))) (.node 40 (.node 39 (.leaf 214) (.leaf 207)) (.node 41 (.leaf 212) (.leaf 213))))) (.node 49 (.node 45 (.node 43 (.leaf 210) (.node 44 (.leaf 206) (.leaf 205))) (.node 47 (.node 46 (.leaf 211) (.leaf 208)) (.node 48 (.leaf 209) (.leaf 204)))) (.node 53 (.node 51 (.node 50 (.leaf 202) (.leaf 200)) (.node 52 (.leaf 201) (.leaf 203))) (.node 55 (.node 54 (.leaf 198) (.leaf 199)) (.node 56 (.leaf 197) (.leaf 196)))))))
private def inverseTable : Table Nat := (.node 28 (.node 14 (.node 7 (.node 3 (.node 1 (.leaf 106645137956677681) (.node 2 (.leaf 55357740815749405) (.leaf 105941208123982504))) (.node 5 (.node 4 (.leaf 45556947017195298) (.leaf 137907787934251967)) (.node 6 (.leaf 113230355770080602) (.leaf 137014989870873258)))) (.node 10 (.node 8 (.leaf 47497445193789055) (.node 9 (.leaf 119374771031404400) (.leaf 81908413806142569))) (.node 12 (.node 11 (.leaf 132022208662657320) (.leaf 107057694191211197)) (.node 13 (.leaf 11577882341683941) (.leaf 100863512530940063))))) (.node 21 (.node 17 (.node 15 (.leaf 86595575680773688) (.node 16 (.leaf 122255348802311803) (.leaf 3220147747172095))) (.node 19 (.node 18 (.leaf 119487125550758220) (.leaf 103338559585754555)) (.node 20 (.leaf 2750008317511377) (.leaf 136899429319361945)))) (.node 24 (.node 22 (.leaf 13636056756918702) (.node 23 (.leaf 59107711193043667) (.leaf 70783678167652107))) (.node 26 (.node 25 (.leaf 119055296211484092) (.leaf 123046999834041582)) (.node 27 (.leaf 72809235613773304) (.leaf 114374134816835521)))))) (.node 42 (.node 35 (.node 31 (.node 29 (.leaf 63138835398327650) (.node 30 (.leaf 37005074487718951) (.leaf 36653994863812085))) (.node 33 (.node 32 (.leaf 131539554867553918) (.leaf 29372428234164934)) (.node 34 (.leaf 108317476790917425) (.leaf 47357657778182285)))) (.node 38 (.node 36 (.leaf 63669715395818708) (.node 37 (.leaf 139912308851518092) (.leaf 52416994897659587))) (.node 40 (.node 39 (.leaf 124516409110895705) (.leaf 74557147792343105)) (.node 41 (.leaf 74347696291157539) (.leaf 87905727315072995))))) (.node 49 (.node 45 (.node 43 (.leaf 124571150972924325) (.node 44 (.leaf 83713075502449653) (.leaf 81967226802475503))) (.node 47 (.node 46 (.leaf 101015337226150289) (.leaf 100367724089525510)) (.node 48 (.leaf 9818958119176609) (.leaf 127513274807879368)))) (.node 53 (.node 51 (.node 50 (.leaf 87909609564508799) (.leaf 141229143289988739)) (.node 52 (.leaf 64433760066925776) (.leaf 93971524654825786))) (.node 55 (.node 54 (.leaf 10818202861727776) (.leaf 98805833981676675)) (.node 56 (.leaf 48549971580298551) (.leaf 114777749162333877)))))))
def columns (i : Fin 57) : Fin 253 := columnTable.get i.val
def rows (i : Fin 57) : List (Fin 57) :=
  FiniteEndpointCoefficientMinor.rows
    (fun k : Fin 57 => FiniteEndpointMetadata22Data.coefficients.get k.val) columns i
def inverse (i : Fin 57) : Nat := inverseTable.get i.val

theorem inverse_checked : checkInverse rows inverse = true := by decide +kernel

theorem counts (i j : Fin 57) :
    (FiniteEndpointMetadata22Data.quadSupport i).count (columns j) = (rows i).count j :=
  FiniteEndpointCoefficientMinor.counts
    (fun k : Fin 57 => FiniteEndpointMetadata22Data.coefficients.get k.val) columns i j

end
end Quartic.FiniteEndpointMinor22
