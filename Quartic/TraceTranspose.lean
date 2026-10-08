import Quartic.SplitBlock22Coordinates
import Quartic.SimultaneousBlockConditions
noncomputable section
namespace Quartic.TraceTranspose
open Module MvPolynomial
variable {K : Type*} [Field K] {n d m c : ℕ}
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

private theorem basis_transport_repr {V ι : Type*} [AddCommGroup V] [Module K V]
    (P Q : Submodule K V) (h : P = Q) (b : Basis ι K Q) (L : ι → V → K)
    (hb : ∀ p i, b.repr p i = L i p.val) (p : P) (i : ι) :
    ((congrArg (fun S : Submodule K V => Basis ι K S) h).mpr b).repr p i = L i p.val := by
  subst Q
  exact hb p i

theorem formsBasis_equivFun_coeff (p : Forms K n d) (s : Sym (Fin n) d) :
    (formsBasis K n d).equivFun p s = p.val.coeff (exponentEquiv n d s).val := by
  rw [Basis.equivFun_apply]
  simpa only [formsBasis,eq_mpr_eq_cast,cast_cast] using basis_transport_repr (Forms K n d) _
    (homogeneousSubmodule_eq_finsupp_supported (Fin n) K d)
    ((basisRestrictSupport K {e : Fin n →₀ ℕ | e.degree = d}).reindex (exponentEquiv n d).symm)
    (fun s p => p.coeff (exponentEquiv n d s).val) (fun _ _ => rfl) p s

theorem exponentEquiv_one (i : Fin n) :
    (exponentEquiv n 1 (Sym.oneEquiv i)).val = Finsupp.single i 1 := by
  classical
  ext j
  change (Sym.equivNatSum (Fin n) 1 (Sym.oneEquiv i) : Fin n →₀ ℕ) j = (Finsupp.single i 1) j
  rw [Sym.coe_equivNatSum_apply_apply]
  simp [Sym.oneEquiv_apply,Finsupp.single_apply,Multiset.count_singleton,eq_comm]

theorem formsBasis_equivFun_one (p : Forms K n 1) (i : Fin n) :
    (formsBasis K n 1).equivFun p (Sym.oneEquiv i) = p.val.coeff (Finsupp.single i 1) := by
  rw [formsBasis_equivFun_coeff,exponentEquiv_one]

open FreeCoefficients
private theorem child_rename_exponent (b : Fin m →₀ ℕ) :
    b.mapDomain (Fin.natAdd 3) = mergeExponent (0 : Fin 3 →₀ ℕ) b := by
  ext s
  refine Fin.addCases ?_ ?_ s
  · intro i
    rw [Finsupp.mapDomain_of_notMem_range]
    · simp
    · rintro ⟨l, hl⟩
      have h := congrArg Fin.val hl
      simp at h
      omega
  · intro i
    rw [Finsupp.mapDomain_apply_of_injective (Fin.natAdd_injective m 3)]
    simp

theorem freeCoeff_child_rename (p : Poly K m) (b : Fin m →₀ ℕ) :
    freeCoeff (t := 3) b (rename (Fin.natAdd 3) p) = C (p.coeff b) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial a c =>
    rw [rename_monomial,child_rename_exponent,freeCoeff_monomial]
    by_cases h : a = b <;> simp [h,coeff_monomial]
  | add p q hp hq =>
    rw [map_add,map_add,hp,hq]
    change C (p.coeff b) + C (q.coeff b) = C (p.coeff b + q.coeff b)
    exact (MvPolynomial.C_add (σ := Fin 3) (a := p.coeff b) (a' := q.coeff b)).symm

theorem traceCoordinates_val (g : MiddleCoordinates.Mixed K m) (l : Fin m) :
    (SplitBlock22.traceCoordinates g l).val =
      ∑ i : Fin 3, X i * C ((g i).val.coeff (Finsupp.single l 1)) := by
  change freeCoeff (Finsupp.single l 1) (SplitBlock22.mixedEmbedding g).val = _
  rw [SplitBlock22.mixedEmbedding_val,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [freeCoeff_core_X_mul,freeCoeff_child_rename]

theorem traceCoordinates_coeff (g : MiddleCoordinates.Mixed K m) (l : Fin m) (i : Fin 3) :
    (SplitBlock22.traceCoordinates g l).val.coeff (Finsupp.single i 1) =
      (g i).val.coeff (Finsupp.single l 1) := by
  classical
  rw [traceCoordinates_val,coeff_sum]
  simp [mul_comm (X _) (C _),coeff_C_mul,coeff_X,Finsupp.single_left_inj,eq_comm]

theorem traceCoordinates_eq_transpose (g : Fin c → MiddleCoordinates.Mixed K m) (j : Fin c) :
    SplitBlock22.traceCoordinates (g j) = SimultaneousBlockConditions.transposeMixed g j := by
  funext l
  apply (formsBasis K 3 1).equivFun.injective
  funext b
  obtain ⟨i,rfl⟩ := (Sym.oneEquiv (α := Fin 3)).surjective b
  rw [formsBasis_equivFun_one,traceCoordinates_coeff]
  change _ = (formsBasis K 3 1).equivFun ((formsBasis K 3 1).equivFun.symm
    (fun s => (formsBasis K m 1).equivFun (g j ((Sym.oneEquiv (α := Fin 3)).symm s))
      (Sym.oneEquiv l))) (Sym.oneEquiv i)
  rw [LinearEquiv.apply_symm_apply,Equiv.symm_apply_apply,formsBasis_equivFun_one]

end Quartic.TraceTranspose
