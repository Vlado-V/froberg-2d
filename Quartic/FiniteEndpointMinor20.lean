import Quartic.FiniteEndpointMetadata20Data
import Quartic.FiniteEndpointCoefficientMinor
import Quartic.FiniteEndpointLookup

/-! Checked coefficient minor for the actual supplied 20-variable quadrics. -/
namespace Quartic.FiniteEndpointMinor20
noncomputable section
open FiniteEndpointChecker FiniteEndpointLookup
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000

private def columnTable : Table (Fin 210) := (.node 24 (.node 12 (.node 6 (.node 3 (.node 1 (.leaf 208) (.node 2 (.leaf 209) (.leaf 207))) (.node 4 (.leaf 206) (.node 5 (.leaf 204) (.leaf 202)))) (.node 9 (.node 7 (.leaf 205) (.node 8 (.leaf 203) (.leaf 201))) (.node 10 (.leaf 200) (.node 11 (.leaf 199) (.leaf 196))))) (.node 18 (.node 15 (.node 13 (.leaf 198) (.node 14 (.leaf 197) (.leaf 194))) (.node 16 (.leaf 195) (.node 17 (.leaf 193) (.leaf 192)))) (.node 21 (.node 19 (.leaf 188) (.node 20 (.leaf 191) (.leaf 190))) (.node 22 (.leaf 183) (.node 23 (.leaf 189) (.leaf 187)))))) (.node 36 (.node 30 (.node 27 (.node 25 (.leaf 186) (.node 26 (.leaf 185) (.leaf 180))) (.node 28 (.leaf 184) (.node 29 (.leaf 181) (.leaf 182)))) (.node 33 (.node 31 (.leaf 178) (.node 32 (.leaf 177) (.leaf 175))) (.node 34 (.leaf 179) (.node 35 (.leaf 176) (.leaf 174))))) (.node 42 (.node 39 (.node 37 (.leaf 173) (.node 38 (.leaf 170) (.leaf 172))) (.node 40 (.leaf 171) (.node 41 (.leaf 168) (.leaf 167)))) (.node 45 (.node 43 (.leaf 169) (.node 44 (.leaf 165) (.leaf 163))) (.node 46 (.leaf 166) (.node 47 (.leaf 164) (.leaf 160)))))))
private def inverseTable : Table Nat := (.node 24 (.node 12 (.node 6 (.node 3 (.node 1 (.leaf 134137551661630) (.node 2 (.leaf 263085073319688) (.leaf 274518326130836))) (.node 4 (.leaf 235938545965208) (.node 5 (.leaf 187142224310080) (.leaf 80014464835982)))) (.node 9 (.node 7 (.leaf 107115204216623) (.node 8 (.leaf 31695794586793) (.leaf 164347084305400))) (.node 10 (.leaf 4377815132821) (.node 11 (.leaf 143478577602811) (.leaf 154292279722036))))) (.node 18 (.node 15 (.node 13 (.leaf 132021811997136) (.node 14 (.leaf 134540530449449) (.leaf 116104103910816))) (.node 16 (.leaf 215701779836070) (.node 17 (.leaf 253115534755544) (.leaf 253719689569905)))) (.node 21 (.node 19 (.leaf 122527626248425) (.node 20 (.leaf 249133422444720) (.leaf 252963165773141))) (.node 22 (.leaf 213554187898719) (.node 23 (.leaf 248321403449637) (.leaf 166847932149485)))))) (.node 36 (.node 30 (.node 27 (.node 25 (.leaf 216243446215301) (.node 26 (.leaf 265500503798838) (.leaf 151336245484478))) (.node 28 (.leaf 41528386863886) (.node 29 (.leaf 273553945382215) (.leaf 131259472933236)))) (.node 33 (.node 31 (.leaf 52431901772926) (.node 32 (.leaf 141825377829770) (.leaf 215725140099684))) (.node 34 (.leaf 19949478427480) (.node 35 (.leaf 92162446542919) (.leaf 107904426532871))))) (.node 42 (.node 39 (.node 37 (.leaf 39598408509079) (.node 38 (.leaf 52538394315654) (.leaf 67470529121193))) (.node 40 (.leaf 232196974775742) (.node 41 (.leaf 56835098700555) (.leaf 4262463042418)))) (.node 45 (.node 43 (.leaf 226656581038997) (.node 44 (.leaf 75209343710752) (.leaf 266635518941476))) (.node 46 (.leaf 148657920258487) (.node 47 (.leaf 85751854276833) (.leaf 260818924766222)))))))
def columns (i : Fin 48) : Fin 210 := columnTable.get i.val
def rows (i : Fin 48) : List (Fin 48) :=
  FiniteEndpointCoefficientMinor.rows
    (fun k : Fin 48 => FiniteEndpointMetadata20Data.coefficients.get k.val) columns i
def inverse (i : Fin 48) : Nat := inverseTable.get i.val

theorem inverse_checked : checkInverse rows inverse = true := by decide +kernel

theorem counts (i j : Fin 48) :
    (FiniteEndpointMetadata20Data.quadSupport i).count (columns j) = (rows i).count j :=
  FiniteEndpointCoefficientMinor.counts
    (fun k : Fin 48 => FiniteEndpointMetadata20Data.coefficients.get k.val) columns i j

end
end Quartic.FiniteEndpointMinor20
