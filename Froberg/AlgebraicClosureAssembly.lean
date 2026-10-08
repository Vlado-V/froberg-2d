import Froberg.Assembly
import Froberg.EndpointFieldDescent
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! It suffices to construct the local comparison over algebraically closed
fields. The generic endpoint statement then descends to every characteristic
zero field before the Hilbert-function statement is assembled. -/
noncomputable section
namespace Froberg
variable {K : Type} [Field K] [CharZero K]

theorem mainStatement_of_algClosed_inductive_recurrence
    (hrec : ∀ (L : Type) [Field L] [CharZero L] [IsAlgClosed L],
      ∀ d : ℕ,3≤d →
      (∃ N : ℕ,1≤N ∧ ∀ n,N≤n → ∀ r,r≤(n+(d-1)-1).choose (d-1) →
        GenericEndpoint L n (d-1) r) →
      ∃ h start : ℕ,0<h ∧ ∀ n,start≤n → criticalDefect L (n+h) d≤criticalDefect L n d) :
    MainStatement K := by
  apply mainStatement_of_eventual_endpoints
  intro d hd
  apply eventual_endpoints_descend (algebraMap K (AlgebraicClosure K))
  exact eventual_endpoints_of_inductive_recurrence (hrec (AlgebraicClosure K)) d hd

end Froberg
