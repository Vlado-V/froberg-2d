import Quartic.FiniteEndpointMetadata25Data
import Quartic.FiniteEndpointCoefficientMinor
import Quartic.FiniteEndpointLookup

/-! Checked coefficient minor for the actual supplied 25-variable quadrics. -/
namespace Quartic.FiniteEndpointMinor25
noncomputable section
open FiniteEndpointChecker FiniteEndpointLookup
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000

private def columnTable : Table (Fin 325) := (.node 35 (.node 17 (.node 8 (.node 4 (.node 2 (.node 1 (.leaf 324) (.leaf 323)) (.node 3 (.leaf 321) (.leaf 319))) (.node 6 (.node 5 (.leaf 318) (.leaf 317)) (.node 7 (.leaf 315) (.leaf 322)))) (.node 12 (.node 10 (.node 9 (.leaf 320) (.leaf 312)) (.node 11 (.leaf 314) (.leaf 311))) (.node 14 (.node 13 (.leaf 307) (.leaf 316)) (.node 15 (.leaf 309) (.node 16 (.leaf 310) (.leaf 313)))))) (.node 26 (.node 21 (.node 19 (.node 18 (.leaf 306) (.leaf 303)) (.node 20 (.leaf 308) (.leaf 305))) (.node 23 (.node 22 (.leaf 304) (.leaf 302)) (.node 24 (.leaf 299) (.node 25 (.leaf 301) (.leaf 300))))) (.node 30 (.node 28 (.node 27 (.leaf 298) (.leaf 297)) (.node 29 (.leaf 296) (.leaf 294))) (.node 32 (.node 31 (.leaf 291) (.leaf 295)) (.node 33 (.leaf 292) (.node 34 (.leaf 293) (.leaf 289))))))) (.node 53 (.node 44 (.node 39 (.node 37 (.node 36 (.leaf 287) (.leaf 286)) (.node 38 (.leaf 290) (.leaf 288))) (.node 41 (.node 40 (.leaf 285) (.leaf 279)) (.node 42 (.leaf 283) (.node 43 (.leaf 284) (.leaf 282))))) (.node 48 (.node 46 (.node 45 (.leaf 280) (.leaf 278)) (.node 47 (.leaf 281) (.leaf 277))) (.node 50 (.node 49 (.leaf 275) (.leaf 276)) (.node 51 (.leaf 274) (.node 52 (.leaf 273) (.leaf 272)))))) (.node 62 (.node 57 (.node 55 (.node 54 (.leaf 271) (.leaf 270)) (.node 56 (.leaf 269) (.leaf 264))) (.node 59 (.node 58 (.leaf 268) (.leaf 267)) (.node 60 (.leaf 262) (.node 61 (.leaf 265) (.leaf 266))))) (.node 66 (.node 64 (.node 63 (.leaf 263) (.leaf 261)) (.node 65 (.leaf 259) (.leaf 256))) (.node 68 (.node 67 (.leaf 257) (.leaf 260)) (.node 69 (.leaf 258) (.node 70 (.leaf 255) (.leaf 252))))))))
private def inverseTable : Table Nat := (.node 35 (.node 17 (.node 8 (.node 4 (.node 2 (.node 1 (.leaf 559124616581882708165) (.leaf 2343015571700810535289)) (.node 3 (.leaf 832210572781613030049) (.leaf 147986738627630271971))) (.node 6 (.node 5 (.leaf 2320784781933596029564) (.leaf 835568913068350765009)) (.node 7 (.leaf 1577107835562739356395) (.leaf 1049214577060886537304)))) (.node 12 (.node 10 (.node 9 (.leaf 409848536158410387570) (.leaf 475205573568462030254)) (.node 11 (.leaf 1606753090709536303089) (.leaf 1765478271478996651846))) (.node 14 (.node 13 (.leaf 110546432776034372205) (.leaf 1047581009664792607497)) (.node 15 (.leaf 2092189163350088930570) (.node 16 (.leaf 451067934096218256880) (.leaf 1404135394588404211986)))))) (.node 26 (.node 21 (.node 19 (.node 18 (.leaf 577900663820159454427) (.leaf 672692862174821838996)) (.node 20 (.leaf 1748659947908589497710) (.leaf 1143687402243345878842))) (.node 23 (.node 22 (.leaf 1931692205890179188630) (.leaf 734323977220072040701)) (.node 24 (.leaf 2020880098006686327530) (.node 25 (.leaf 57290647306611999234) (.leaf 1685792162689435366148))))) (.node 30 (.node 28 (.node 27 (.leaf 1426448540537694354463) (.leaf 1277410485878100780731)) (.node 29 (.leaf 1893213620493534915912) (.leaf 134946800777838504857))) (.node 32 (.node 31 (.leaf 1692193983718971350129) (.leaf 169326632598303358399)) (.node 33 (.leaf 1241315770592596993421) (.node 34 (.leaf 2028101347136424355193) (.leaf 1967686886133203967481))))))) (.node 53 (.node 44 (.node 39 (.node 37 (.node 36 (.leaf 868674509507768589998) (.leaf 1951739162582600736120)) (.node 38 (.leaf 1890574388728406597527) (.leaf 2357597914880338672401))) (.node 41 (.node 40 (.leaf 1403377205452978012073) (.leaf 452732977302279027623)) (.node 42 (.leaf 1338635099290478533519) (.node 43 (.leaf 1815266241396065642708) (.leaf 1634864723207353352816))))) (.node 48 (.node 46 (.node 45 (.leaf 1097263590981812830951) (.leaf 2181499811768724287524)) (.node 47 (.leaf 12887777915372020522) (.leaf 283732639589523586731))) (.node 50 (.node 49 (.leaf 1166220519499288727044) (.leaf 2170120139026653799313)) (.node 51 (.leaf 561002858681303313887) (.node 52 (.leaf 562578806380475056288) (.leaf 1440379834462049595612)))))) (.node 62 (.node 57 (.node 55 (.node 54 (.leaf 1566587361097389614655) (.leaf 2073467892171008720105)) (.node 56 (.leaf 263149884107784280928) (.leaf 1180036701625759714840))) (.node 59 (.node 58 (.leaf 2180523686296229376944) (.leaf 2287658356609983399855)) (.node 60 (.leaf 1848174943772511888585) (.node 61 (.leaf 563268442328835779561) (.leaf 2166794590944794014798))))) (.node 66 (.node 64 (.node 63 (.leaf 1861393407847228723944) (.leaf 1938395460376537047233)) (.node 65 (.leaf 443802309375356914425) (.leaf 68065199906926616437))) (.node 68 (.node 67 (.leaf 1085232576843679323206) (.leaf 874241504209546779796)) (.node 69 (.leaf 657170692612600517041) (.node 70 (.leaf 1816808045490442716309) (.leaf 1699880806614045924273))))))))
def columns (i : Fin 71) : Fin 325 := columnTable.get i.val
def rows (i : Fin 71) : List (Fin 71) :=
  FiniteEndpointCoefficientMinor.rows
    (fun k : Fin 71 => FiniteEndpointMetadata25Data.coefficients.get k.val) columns i
def inverse (i : Fin 71) : Nat := inverseTable.get i.val

theorem inverse_checked : checkInverse rows inverse = true := by decide +kernel

theorem counts (i j : Fin 71) :
    (FiniteEndpointMetadata25Data.quadSupport i).count (columns j) = (rows i).count j :=
  FiniteEndpointCoefficientMinor.counts
    (fun k : Fin 71 => FiniteEndpointMetadata25Data.coefficients.get k.val) columns i j

end
end Quartic.FiniteEndpointMinor25
