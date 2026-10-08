import Quartic.FiniteEndpointMetadata21Data
import Quartic.FiniteEndpointCoefficientMinor
import Quartic.FiniteEndpointLookup

/-! Checked coefficient minor for the actual supplied 21-variable quadrics. -/
namespace Quartic.FiniteEndpointMinor21
noncomputable section
open FiniteEndpointChecker FiniteEndpointLookup
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000

private def columnTable : Table (Fin 231) := (.node 26 (.node 13 (.node 6 (.node 3 (.node 1 (.leaf 230) (.node 2 (.leaf 228) (.leaf 226))) (.node 4 (.leaf 224) (.node 5 (.leaf 227) (.leaf 222)))) (.node 9 (.node 7 (.leaf 225) (.node 8 (.leaf 223) (.leaf 218))) (.node 11 (.node 10 (.leaf 221) (.leaf 219)) (.node 12 (.leaf 216) (.leaf 229))))) (.node 19 (.node 16 (.node 14 (.leaf 217) (.node 15 (.leaf 215) (.leaf 220))) (.node 17 (.leaf 213) (.node 18 (.leaf 212) (.leaf 214)))) (.node 22 (.node 20 (.leaf 210) (.node 21 (.leaf 208) (.leaf 206))) (.node 24 (.node 23 (.leaf 204) (.leaf 207)) (.node 25 (.leaf 211) (.leaf 205)))))) (.node 39 (.node 32 (.node 29 (.node 27 (.leaf 203) (.node 28 (.leaf 202) (.leaf 209))) (.node 30 (.leaf 201) (.node 31 (.leaf 200) (.leaf 199)))) (.node 35 (.node 33 (.leaf 197) (.node 34 (.leaf 194) (.leaf 196))) (.node 37 (.node 36 (.leaf 198) (.leaf 192)) (.node 38 (.leaf 191) (.leaf 195))))) (.node 45 (.node 42 (.node 40 (.leaf 193) (.node 41 (.leaf 190) (.leaf 186))) (.node 43 (.leaf 189) (.node 44 (.leaf 185) (.leaf 180)))) (.node 48 (.node 46 (.leaf 188) (.node 47 (.leaf 184) (.leaf 183))) (.node 50 (.node 49 (.leaf 181) (.leaf 182)) (.node 51 (.leaf 187) (.leaf 178)))))))
private def inverseTable : Table Nat := (.node 26 (.node 13 (.node 6 (.node 3 (.node 1 (.leaf 2615487797337814) (.node 2 (.leaf 209269578735791) (.leaf 678874982347202))) (.node 4 (.leaf 3841800289004537) (.node 5 (.leaf 1713726830175178) (.leaf 1502073925670471)))) (.node 9 (.node 7 (.leaf 90508482808863) (.node 8 (.leaf 3056784644421015) (.leaf 1227517343019796))) (.node 11 (.node 10 (.leaf 1778246808306263) (.leaf 1894600503447050)) (.node 12 (.leaf 241800624340764) (.leaf 4322211953813118))))) (.node 19 (.node 16 (.node 14 (.leaf 4253435032697856) (.node 15 (.leaf 3522249286415683) (.leaf 1455426478000289))) (.node 17 (.leaf 382369729017701) (.node 18 (.leaf 2639998340039403) (.leaf 3699941229029)))) (.node 22 (.node 20 (.leaf 2450230186332478) (.node 21 (.leaf 8795219344307) (.leaf 3966596177011347))) (.node 24 (.node 23 (.leaf 2832522714173825) (.leaf 595943422715899)) (.node 25 (.leaf 3088974271450902) (.leaf 2945341918323339)))))) (.node 39 (.node 32 (.node 29 (.node 27 (.leaf 3437534448072695) (.node 28 (.leaf 1278671676381875) (.leaf 2063956316661836))) (.node 30 (.leaf 3572177335026716) (.node 31 (.leaf 1036292829335972) (.leaf 2173122269066498)))) (.node 35 (.node 33 (.leaf 3489373373858614) (.node 34 (.leaf 586026819251864) (.leaf 1492261732466107))) (.node 37 (.node 36 (.leaf 3879584627417704) (.leaf 2288489835481952)) (.node 38 (.leaf 1225433453999598) (.leaf 3527383659761395))))) (.node 45 (.node 42 (.node 40 (.leaf 3016605210510560) (.node 41 (.leaf 1798226792402995) (.leaf 4488294284320245))) (.node 43 (.leaf 3298559905134083) (.node 44 (.leaf 213977539471494) (.leaf 4079230391410561)))) (.node 48 (.node 46 (.leaf 3971497541773774) (.node 47 (.leaf 1073745885044855) (.leaf 4214607790947294))) (.node 50 (.node 49 (.leaf 4481361278328814) (.leaf 3648837534549182)) (.node 51 (.leaf 1371942720976228) (.leaf 4051617658924853)))))))
def columns (i : Fin 52) : Fin 231 := columnTable.get i.val
def rows (i : Fin 52) : List (Fin 52) :=
  FiniteEndpointCoefficientMinor.rows
    (fun k : Fin 52 => FiniteEndpointMetadata21Data.coefficients.get k.val) columns i
def inverse (i : Fin 52) : Nat := inverseTable.get i.val

theorem inverse_checked : checkInverse rows inverse = true := by decide +kernel

theorem counts (i j : Fin 52) :
    (FiniteEndpointMetadata21Data.quadSupport i).count (columns j) = (rows i).count j :=
  FiniteEndpointCoefficientMinor.counts
    (fun k : Fin 52 => FiniteEndpointMetadata21Data.coefficients.get k.val) columns i j

end
end Quartic.FiniteEndpointMinor21
