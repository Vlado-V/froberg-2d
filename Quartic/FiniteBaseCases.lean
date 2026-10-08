import Quartic.SixVariables
import Quartic.FiniteEndpointCheckerSeven
import Quartic.FiniteEndpointCheckerEight
import Quartic.FiniteEndpointCheckerNine
import Quartic.FiniteEndpointCheckerTen
import Quartic.FiniteEndpointCheckerEleven
import Quartic.FiniteEndpointCheckerTwelve
import Quartic.FiniteEndpointCheckerThirteen
import Quartic.FiniteEndpointCheckerFourteen
import Quartic.FiniteEndpointCheckerFifteen
import Quartic.FiniteEndpointCheckerSixteen
import Quartic.FiniteEndpointCertified17
import Quartic.FiniteEndpointCertified18
import Quartic.FiniteEndpointCertified19
import Quartic.FiniteEndpointCertified20
import Quartic.FiniteEndpointCertified21
import Quartic.FiniteEndpointCertified22
import Quartic.FiniteEndpointCertified23
import Quartic.FiniteEndpointCertified24
import Quartic.FiniteEndpointCertified25
import Quartic.FiniteEndpointCertified26
import Quartic.FiniteEndpointCertified27
import Quartic.FiniteEndpointCertified28
import Quartic.FiniteEndpointCertified29
import Quartic.FiniteEndpointCertified30

/-! All required finite bases, with no certificate or rank premise. -/
noncomputable section
namespace Quartic.FiniteBaseCases
variable {K : Type*} [Field K] [CharZero K]

theorem generic (n : ℕ) (hn : 1 ≤ n) (hn30 : n ≤ 30) :
    ∀ r,r ≤ (n+1).choose 2 → GenericQuartic K n r := by
  intro r hr
  by_cases hn6 : n ≤ 6
  · exact SixVariables.generic_at_most_six n r hn hn6 hr
  · have hn7 : 7 ≤ n := by omega
    interval_cases n
    · exact FiniteEndpointCheckerSeven.generic_seven_variables r hr
    · exact FiniteEndpointCheckerEight.generic_eight_variables r hr
    · exact FiniteEndpointCheckerNine.generic_nine_variables r hr
    · exact FiniteEndpointCheckerTen.generic_ten_variables r hr
    · exact FiniteEndpointCheckerEleven.generic_eleven_variables r hr
    · exact FiniteEndpointCheckerTwelve.generic_twelve_variables r hr
    · exact FiniteEndpointCheckerThirteen.generic_thirteen_variables r hr
    · exact FiniteEndpointCheckerFourteen.generic_fourteen_variables r hr
    · exact FiniteEndpointCheckerFifteen.generic_fifteen_variables r hr
    · exact FiniteEndpointCheckerSixteen.generic_sixteen_variables r hr
    · exact FiniteEndpointCertified17.generic r hr
    · exact FiniteEndpointCertified18.generic r hr
    · exact FiniteEndpointCertified19.generic r hr
    · exact FiniteEndpointCertified20.generic r hr
    · exact FiniteEndpointCertified21.generic r hr
    · exact FiniteEndpointCertified22.generic r hr
    · exact FiniteEndpointCertified23.generic r hr
    · exact FiniteEndpointCertified24.generic r hr
    · exact FiniteEndpointCertified25.generic r hr
    · exact FiniteEndpointCertified26.generic r hr
    · exact FiniteEndpointCertified27.generic r hr
    · exact FiniteEndpointCertified28.generic r hr
    · exact FiniteEndpointCertified29.generic r hr
    · exact FiniteEndpointCertified30.generic r hr

end Quartic.FiniteBaseCases
