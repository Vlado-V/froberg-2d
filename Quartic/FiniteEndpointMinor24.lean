import Quartic.FiniteEndpointMetadata24Data
import Quartic.FiniteEndpointCoefficientMinor
import Quartic.FiniteEndpointLookup

/-! Checked coefficient minor for the actual supplied 24-variable quadrics. -/
namespace Quartic.FiniteEndpointMinor24
noncomputable section
open FiniteEndpointChecker FiniteEndpointLookup
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000

private def columnTable : Table (Fin 300) := (.node 33 (.node 16 (.node 8 (.node 4 (.node 2 (.node 1 (.leaf 298) (.leaf 295)) (.node 3 (.leaf 296) (.leaf 294))) (.node 6 (.node 5 (.leaf 299) (.leaf 297)) (.node 7 (.leaf 292) (.leaf 291)))) (.node 12 (.node 10 (.node 9 (.leaf 293) (.leaf 290)) (.node 11 (.leaf 288) (.leaf 287))) (.node 14 (.node 13 (.leaf 286) (.leaf 285)) (.node 15 (.leaf 282) (.leaf 283))))) (.node 24 (.node 20 (.node 18 (.node 17 (.leaf 289) (.leaf 284)) (.node 19 (.leaf 279) (.leaf 281))) (.node 22 (.node 21 (.leaf 280) (.leaf 277)) (.node 23 (.leaf 278) (.leaf 275)))) (.node 28 (.node 26 (.node 25 (.leaf 272) (.leaf 276)) (.node 27 (.leaf 274) (.leaf 271))) (.node 30 (.node 29 (.leaf 273) (.leaf 270)) (.node 31 (.leaf 265) (.node 32 (.leaf 269) (.leaf 264))))))) (.node 49 (.node 41 (.node 37 (.node 35 (.node 34 (.leaf 266) (.leaf 267)) (.node 36 (.leaf 261) (.leaf 268))) (.node 39 (.node 38 (.leaf 263) (.leaf 262)) (.node 40 (.leaf 258) (.leaf 260)))) (.node 45 (.node 43 (.node 42 (.leaf 259) (.leaf 256)) (.node 44 (.leaf 257) (.leaf 255))) (.node 47 (.node 46 (.leaf 253) (.leaf 254)) (.node 48 (.leaf 252) (.leaf 251))))) (.node 57 (.node 53 (.node 51 (.node 50 (.leaf 249) (.leaf 250)) (.node 52 (.leaf 248) (.leaf 245))) (.node 55 (.node 54 (.leaf 247) (.leaf 246)) (.node 56 (.leaf 244) (.leaf 242)))) (.node 61 (.node 59 (.node 58 (.leaf 241) (.leaf 240)) (.node 60 (.leaf 243) (.leaf 239))) (.node 63 (.node 62 (.leaf 238) (.leaf 234)) (.node 64 (.leaf 236) (.node 65 (.leaf 237) (.leaf 235))))))))
private def inverseTable : Table Nat := (.node 33 (.node 16 (.node 8 (.node 4 (.node 2 (.node 1 (.leaf 18314921210986276165) (.leaf 38376831143580015912)) (.node 3 (.leaf 31808640282347222657) (.leaf 68724369364439294056))) (.node 6 (.node 5 (.leaf 21369506207077383646) (.leaf 52089499749956678602)) (.node 7 (.leaf 4364427333706267671) (.leaf 63455314897431936260)))) (.node 12 (.node 10 (.node 9 (.leaf 7816253086283771374) (.leaf 24459833215659549067)) (.node 11 (.leaf 35952518230251289477) (.leaf 13691893667137722320))) (.node 14 (.node 13 (.leaf 17653328279871033967) (.leaf 51914561570890746336)) (.node 15 (.leaf 54841437586394529113) (.leaf 52570898829939752663))))) (.node 24 (.node 20 (.node 18 (.node 17 (.leaf 18223221641772139600) (.leaf 54270475004249478208)) (.node 19 (.leaf 51023089521425314284) (.leaf 34879780267733677462))) (.node 22 (.node 21 (.leaf 69286775990795432394) (.leaf 50104831648914957019)) (.node 23 (.leaf 37179899245880879068) (.leaf 73183383482305341643)))) (.node 28 (.node 26 (.node 25 (.leaf 23343723171562923863) (.leaf 61378082268926159481)) (.node 27 (.leaf 63727939670689701962) (.leaf 5574810806011203837))) (.node 30 (.node 29 (.leaf 26028992773143099487) (.leaf 53833078933620064479)) (.node 31 (.leaf 67793318272450161850) (.node 32 (.leaf 2196505550582592214) (.leaf 51759790151459531500))))))) (.node 49 (.node 41 (.node 37 (.node 35 (.node 34 (.leaf 31063258434872772452) (.leaf 52474983466315370433)) (.node 36 (.leaf 1978233599791563699) (.leaf 4586161450217568928))) (.node 39 (.node 38 (.leaf 27840991098131176493) (.leaf 66202872690255840678)) (.node 40 (.leaf 39243404307764597690) (.leaf 16233305506282305800)))) (.node 45 (.node 43 (.node 42 (.leaf 18361340265176447344) (.leaf 47357513474663642667)) (.node 44 (.leaf 17482930724549033383) (.leaf 21670493672673896572))) (.node 47 (.node 46 (.leaf 54169708962261239540) (.leaf 45041520786501091495)) (.node 48 (.leaf 71198460116666126352) (.leaf 61268984531636222819))))) (.node 57 (.node 53 (.node 51 (.node 50 (.leaf 55364452329094323281) (.leaf 36509629625665384048)) (.node 52 (.leaf 67029128487455844150) (.leaf 44023964511916755664))) (.node 55 (.node 54 (.leaf 67904129284045187778) (.leaf 66922651538658550563)) (.node 56 (.leaf 63614373983666486254) (.leaf 37227599490913957761)))) (.node 61 (.node 59 (.node 58 (.leaf 15624238657042910689) (.leaf 60804697866274381304)) (.node 60 (.leaf 66748452015737741560) (.leaf 55929607175091839813))) (.node 63 (.node 62 (.leaf 54892782692627203605) (.leaf 6635006657875898337)) (.node 64 (.leaf 13449173477107544484) (.node 65 (.leaf 19530204209474907818) (.leaf 43835285089951714941))))))))
def columns (i : Fin 66) : Fin 300 := columnTable.get i.val
def rows (i : Fin 66) : List (Fin 66) :=
  FiniteEndpointCoefficientMinor.rows
    (fun k : Fin 66 => FiniteEndpointMetadata24Data.coefficients.get k.val) columns i
def inverse (i : Fin 66) : Nat := inverseTable.get i.val

theorem inverse_checked : checkInverse rows inverse = true := by decide +kernel

theorem counts (i j : Fin 66) :
    (FiniteEndpointMetadata24Data.quadSupport i).count (columns j) = (rows i).count j :=
  FiniteEndpointCoefficientMinor.counts
    (fun k : Fin 66 => FiniteEndpointMetadata24Data.coefficients.get k.val) columns i j

end
end Quartic.FiniteEndpointMinor24
