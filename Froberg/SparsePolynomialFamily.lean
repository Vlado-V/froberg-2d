import Froberg.PolynomialIntermediateRow
import Froberg.SparseExactIntermediate

/-! Sparse attached vector families are literal homogeneous polynomial
families after selecting their output directions. -/
noncomputable section
namespace Froberg
open Module MvPolynomial
variable {K : Type} [Field K]
variable {σ I J : Type*} [Fintype I] [Fintype J] {n s d : ℕ}

def attachedPolynomialFamily (o : J → MvPolynomial σ K)
    (e : I → Fin n →₀ ℕ) (v : I → J → K) : I → MvPolynomial (σ ⊕ Fin n) K :=
  fun i => polynomialVector o (fun j => monomial (e i) (v i j))

theorem attachedPolynomialFamily_homogeneous (o : J → MvPolynomial σ K)
    {R : ℕ} (ho : ∀ j,(o j).IsHomogeneous R)
    (e : I → Fin n →₀ ℕ) (v : I → J → K) (he : ∀ i,(e i).degree=s) (i : I) :
    (attachedPolynomialFamily o e v i).IsHomogeneous (R+s) :=
  polynomialVector_homogeneous o _ ho (fun j => isHomogeneous_monomial _ (he i))

/-- Literal polynomial multiplication is exactly the transported vector map. -/
theorem attachedPolynomialFamily_multiplication (o : J → MvPolynomial σ K)
    (e : I → Fin n →₀ ℕ) (v : I → J → K) (p : I → Forms K n d) :
    (∑ i,attachedPolynomialFamily o e v i * rename Sum.inr (p i).val) =
      polynomialVector o (AttachedMultiplication.multiplication e v p) := by
  simp only [attachedPolynomialFamily,polynomialVector_apply,
    AttachedMultiplication.multiplication_apply,map_sum,map_mul,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Injectivity of the monomial-attached vector map proves injectivity of the
actual polynomial family with the same scalar coefficients. -/
theorem attachedPolynomialFamily_injective (o : J → MvPolynomial σ K)
    (ho : LinearIndependent K o) (e : I → Fin n →₀ ℕ) (v : I → J → K)
    (hv : Function.Injective (AttachedMultiplication.multiplication (d := d) e v)) :
    Function.Injective (fun p : I → Forms K n d =>
      ∑ i,attachedPolynomialFamily o e v i * rename Sum.inr (p i).val) := by
  intro p p' hp
  dsimp only at hp
  rw [attachedPolynomialFamily_multiplication,attachedPolynomialFamily_multiplication] at hp
  exact hv (polynomialVector_injective o ho hp)

/-- A basis of a prescribed homogeneous output subspace gives faithful output
coordinates without selecting a larger ambient polynomial space. -/
theorem homogeneous_output_basis [Infinite K]
    (O : Submodule K (MvPolynomial σ K)) [FiniteDimensional K O] {R : ℕ}
    (hO : O≤homogeneousSubmodule σ K R) :
    ∃ o : Fin (finrank K O) → MvPolynomial σ K,
      LinearIndependent K o ∧ (∀ j,o j∈O) ∧ (∀ j,(o j).IsHomogeneous R) := by
  let o := fun j => (Module.finBasis K O j).val
  refine ⟨o,?_,?_,?_⟩
  · exact (Module.finBasis K O).linearIndependent.map' O.subtype
      (LinearMap.ker_eq_bot.mpr O.subtype_injective)
  · exact fun j => (Module.finBasis K O j).property
  · exact fun j => hO (Module.finBasis K O j).property

/-- The complete finite sparse witness, expressed with actual homogeneous
polynomial generators and their exact scalar/new-layer kernel. -/
theorem exists_sparse_polynomial_row [Infinite K]
    {h b m q R : ℕ} (hn : 0<n) (hh : 0<h)
    (o : Fin h → MvPolynomial σ K) (ho : LinearIndependent K o)
    (hdegree : ∀ j,(o j).IsHomogeneous R)
    (hm : m≤b*(n+s-1).choose s) (hcap : b*(s+d).choose s≤h)
    (hcount : h*(s+d).choose s * (q+h*(n+s-1).choose s+(h*2^h)*(n+(d-1)-1).choose (d-1)) ≤
      (h-b*(s+d).choose s)*(n+s+d-1).choose d) :
    ∃ (e : Fin m → Fin n →₀ ℕ) (v : Fin m → Fin h → K),
      ∃ he : ∀ i,(e i).degree=s,
      (∀ i,(attachedPolynomialFamily o e v i).IsHomogeneous (R+s)) ∧
      (∀ c≤d,Function.Injective (fun p : Fin m → Forms K n c =>
        ∑ i,attachedPolynomialFamily o e v i * rename Sum.inr (p i).val)) ∧
      ∃ P : MvPolynomial (Fin (finrank K (Fin q → Forms K n d))) K,
        (∃ Q : Fin q → Forms K n d,
          eval (Quartic.PolynomialBilinearCoordinates.coordinates K _ Q) P≠0) ∧
        ∀ Q : Fin q → Forms K n d,
          eval (Quartic.PolynomialBilinearCoordinates.coordinates K _ Q) P≠0 →
          (AttachedMultiplication.polynomialIntermediateRow o e v he Q).ker=
            (AttachedMultiplication.intermediateKoszul e v he Q).range := by
  obtain ⟨e,v,he,hdiv,hv,hpos,hinj,P,hP,hPQ⟩ :=
    exists_exact_sparse_intermediate (K := K) hn hh hm hcap hcount
  refine ⟨e,v,he,attachedPolynomialFamily_homogeneous o hdegree e v he,?_,P,hP,?_⟩
  · intro c hc
    exact attachedPolynomialFamily_injective o ho e v (hinj c hc)
  · intro Q hQ
    exact AttachedMultiplication.polynomialIntermediateRow_ker o ho e v he Q
      (hinj d le_rfl) (hPQ Q hQ)

end Froberg
