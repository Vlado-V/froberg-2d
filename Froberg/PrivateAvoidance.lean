import Froberg.PrivateSparseSeparation

/-! Private-power avoidance for the actual core-supported lower-row
terms. Arbitrary private-variable coefficients are allowed below the
private-power degree. -/
noncomputable section
namespace Froberg.PrivateColumns
open MvPolynomial Quartic.FreeCoefficients
variable {K : Type*} [Field K] [Infinite K] {a z s b c r : ℕ}

theorem avoidsPrivatePowers_add (ι : Fin b ↪ Fin z)
    (f g : Fin c → Poly K (a+z))
    (hf : avoidsPrivatePowers (s := s) ι f)
    (hg : avoidsPrivatePowers (s := s) ι g) :
    avoidsPrivatePowers (s := s) ι (f+g) := by
  intro k δ i hi
  simp only [Pi.add_apply,MvPolynomial.coeff_add,hf k δ i hi,hg k δ i hi,add_zero]

theorem avoidsPrivatePowers_sum {I : Type*} [Fintype I] (ι : Fin b ↪ Fin z)
    (f : I → Fin c → Poly K (a+z))
    (hf : ∀ i,avoidsPrivatePowers (s := s) ι (f i)) :
    avoidsPrivatePowers (s := s) ι (∑ i,f i) := by
  intro k δ j hj
  simp only [Finset.sum_apply,MvPolynomial.coeff_sum]
  exact Finset.sum_eq_zero (fun i _ => hf i k δ j hj)

theorem core_matrix_avoids_private_powers {I : Type*} [Fintype I]
    (ι : Fin b ↪ Fin z) (q : Fin c → I → Poly K a)
    (p : I → Forms K (a+z) r) (hr : r < s) :
    avoidsPrivatePowers (s := s) ι (extendedCorePolynomialMatrix q p) := by
  apply avoidsPrivatePowers_of_free_degree_lt
  intro k β hβ
  have hp (i : I) : freeCoeff β (p i).val=0 :=
    freeCoeff_eq_zero_of_degree_lt _ (p i).property β (by omega)
  simp only [extendedCorePolynomialMatrix,LinearMap.coe_mk,AddHom.coe_mk,
    map_sum,freeCoeff_rename_mul,hp,mul_zero,Finset.sum_const_zero]

end Froberg.PrivateColumns
