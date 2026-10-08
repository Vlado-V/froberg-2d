import Froberg.SparseCoreExtension
import Froberg.PrivateBiformRow

/-! Literal polynomial row exactness survives adjoining private variables.
The generators, product columns and scalar list are the same core witness. -/
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial AttachedMultiplication Quartic.FreeCoefficients
variable {K : Type} [Field K] [Infinite K]
variable {σ : Type*} [Fintype σ] {a z s d R m q : ℕ}
variable {W : Type*} [AddCommGroup W] [Module K W]

 theorem extended_polynomial_row_relation_constants (hs : 1 ≤ s) (hsd : s ≤ d)
    (o : Fin (finrank K (homogeneousSubmodule σ K R)) → MvPolynomial σ K)
    (ho : LinearIndependent K o) (hdeg : ∀ i,(o i).IsHomogeneous R)
    (e : Fin m → Fin a →₀ ℕ)
    (v : Fin m → Fin (finrank K (homogeneousSubmodule σ K R)) → K)
    (he : ∀ i,(e i).degree=s) (Q : Fin q → Forms K a d)
    (P : W →ₗ[K] MvPolynomial (σ ⊕ Fin a) K)
    (hfull : ∀ c ≤ d,Function.Injective (homogeneousMultiplication (d := c) e v he))
    (hker : (addRow (polynomialIntermediateRow o e v he Q) P).ker=
      ((LinearMap.inl K
        ((Fin q → Fin (finrank K (homogeneousSubmodule σ K R)) → Forms K a s) ×
          (Fin m → Forms K a d)) W).comp (intermediateKoszul e v he Q)).range)
    (ell : Fin 2 → Forms K a 1) (hell : LinearIndependent K ell)
    (U : Fin q → MvPolynomial (σ ⊕ Fin (a+z)) K)
    (hU : ∀ i,U i∈biformImage (homogeneousSubmodule σ K R) (Forms K (a+z) s))
    (B : Fin m → Forms K (a+z) d)
    (p : MvPolynomial (σ ⊕ Fin a) K) (hp : p∈P.range)
    (hpd : p∈biformImage (homogeneousSubmodule σ K R) (Forms K a (s+d)))
    (hrel : (∑ i,rename Sum.inr (rename (Fin.castAdd z) (Q i).val)*U i)+
      (∑ k,rename (Sum.map id (Fin.castAdd z)) (attachedPolynomialFamily o e v k)*
        rename Sum.inr (B k).val)+rename (Sum.map id (Fin.castAdd z)) p=0) :
    ∃ C : Fin q → Fin m → K,
      (∀ i,U i=∑ k,C i k • rename (Sum.map id (Fin.castAdd z)) (attachedPolynomialFamily o e v k)) ∧
      (∀ k,(B k).val = -∑ i,C i k • rename (Fin.castAdd z) (Q i).val) ∧ p=0 := by
  have hcoords (i : Fin q) : ∃ u : Fin (finrank K (homogeneousSubmodule σ K R)) → Forms K (a+z) s,
      polynomialFormVector o s u=U i := by
    change U i∈(polynomialFormVector o s).range
    rw [polynomialFormVector_range_complete o ho hdeg]
    exact hU i
  choose x hx using hcoords
  have hpc : ∃ c : Fin (finrank K (homogeneousSubmodule σ K R)) → Forms K a (s+d),
      polynomialFormVector o (s+d) c=p := by
    change p∈(polynomialFormVector o (s+d)).range
    rw [polynomialFormVector_range_complete o ho hdeg]
    exact hpd
  obtain ⟨pc,hpc⟩ := hpc
  have hcoord : ∀ j,(∑ i,rename (Fin.castAdd z) (Q i).val*(x i j).val)+
      (∑ k,rename (Fin.castAdd z) (monomial (e k) (v k j))*(B k).val)+
      rename (Fin.castAdd z) (pc j).val=0 := by
    have h : polynomialVector o
        (fun j => (∑ i,rename (Fin.castAdd z) (Q i).val*(x i j).val)+
          (∑ k,rename (Fin.castAdd z) (monomial (e k) (v k j))*(B k).val)+
          rename (Fin.castAdd z) (pc j).val)=0 := by
      calc
        _ = (∑ i,rename Sum.inr (rename (Fin.castAdd z) (Q i).val)*U i)+
            (∑ k,rename (Sum.map id (Fin.castAdd z)) (attachedPolynomialFamily o e v k)*
              rename Sum.inr (B k).val)+rename (Sum.map id (Fin.castAdd z)) p := by
          simp only [←hx,←hpc,polynomialFormVector_apply,attachedPolynomialFamily,
            polynomialVector_core_extension,polynomialVector_apply,map_sum,map_mul,
            Finset.sum_mul,Finset.mul_sum,Finset.sum_add_distrib,map_add,mul_add,rename_rename,Function.comp_def,Sum.map_inl,Sum.map_inr,id_eq]
          apply congrArg₂ (·+·)
          · apply congrArg₂ (·+·)
            · rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro i _
              apply Finset.sum_congr rfl
              intro j _
              ring
            · rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro k _
              apply Finset.sum_congr rfl
              intro j _
              ring
          · rfl
        _ = 0 := hrel
    have hh := polynomialVector_injective o ho (h.trans (map_zero _).symm)
    exact fun j => congrFun hh j
  obtain ⟨hxcore,hBcore,hcore⟩ := extended_sparse_relation_core hs hsd o e v he Q P
    hfull hker ell hell (fun j => (pc j).val) (fun i j => (x i j).val)
    (fun k => (B k).val) (fun i j => (x i j).property) (fun k => (B k).property) hcoord
  let x₀ : Fin q → Fin (finrank K (homogeneousSubmodule σ K R)) → Forms K a s :=
    fun i j => ⟨freeCoeff (0 : Fin z →₀ ℕ) (x i j).val,by
      change (freeCoeff (0 : Fin z →₀ ℕ) (x i j).val).IsHomogeneous s
      simpa only [map_zero,Nat.sub_zero] using freeCoeff_homogeneous _ (x i j).property (0 : Fin z →₀ ℕ)⟩
  let B₀ : Fin m → Forms K a d := fun k => ⟨freeCoeff (0 : Fin z →₀ ℕ) (B k).val,by
    change (freeCoeff (0 : Fin z →₀ ℕ) (B k).val).IsHomogeneous d
    simpa only [map_zero,Nat.sub_zero] using freeCoeff_homogeneous _ (B k).property (0 : Fin z →₀ ℕ)⟩
  have hcorepoly : (∑ i,rename Sum.inr (Q i).val*polynomialFormVector o s (x₀ i))+
      (∑ k,attachedPolynomialFamily o e v k*rename Sum.inr (B₀ k).val)+p=0 := by
    have hh : (fun j => (∑ i,(Q i).val*(x₀ i j).val)+
        (∑ k,monomial (e k) (v k j)*(B₀ k).val)+(pc j).val)=0 := funext hcore
    have h := congrArg (polynomialVector o) hh
    simp only [map_zero] at h
    calc
      _ = polynomialVector o (fun j => (∑ i,(Q i).val*(x₀ i j).val)+
          (∑ k,monomial (e k) (v k j)*(B₀ k).val)+(pc j).val) := by
        rw [←hpc]
        simp only [polynomialFormVector_apply,attachedPolynomialFamily,polynomialVector_apply,
          map_add,map_sum,map_mul,Finset.sum_add_distrib,Finset.sum_mul,Finset.mul_sum,mul_add]
        apply congrArg₂ (·+·)
        · apply congrArg₂ (·+·)
          · rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro j _
            apply Finset.sum_congr rfl
            intro i _
            ring
          · rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro j _
            apply Finset.sum_congr rfl
            intro i _
            ring
        · rfl
      _ = 0 := h
  obtain ⟨C,hCU,hCB,hpz⟩ := polynomial_row_relation_constants o ho hdeg e v he Q P hker
    (fun i => polynomialFormVector o s (x₀ i))
    (fun i => polynomialFormVector_mem_biform o _ _ hdeg _ (fun j => (x₀ i j).property))
    B₀ p hp hcorepoly
  refine ⟨C,?_,?_,hpz⟩
  · intro i
    have hUcore : U i=rename (Sum.map id (Fin.castAdd z)) (polynomialFormVector o s (x₀ i)) := by
      rw [←hx i]
      change polynomialVector o (fun j => (x i j).val)=_
      rw [polynomialFormVector_apply,polynomialVector_core_extension]
      congr 1
      funext j
      exact hxcore i j
    rw [hUcore,hCU i,map_sum]
    simp only [map_smul]
  · intro k
    rw [hBcore k]
    change rename (Fin.castAdd z) (B₀ k).val=_
    rw [hCB k,map_neg,map_sum]
    simp only [map_smul]

end Froberg
