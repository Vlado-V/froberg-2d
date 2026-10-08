import Froberg.AffineGraphConstraints
import Froberg.ProjectionCharts
import Quartic.HomogeneousEmptyFiberOpen

/-! Full Grassmannian charts for the actual relation kernel, and the
literal affine equations for its higher covector coordinates. -/
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial Quartic Quartic.SubspaceCharts Quartic.BilinearCovectorCharts
open Quartic.BilinearCoefficientKernel
variable {K : Type} [Field K] [Infinite K]

private theorem polynomial_pi {I J V : Type*} [Fintype J]
    [AddCommGroup V] [Module K V] (f : (I → K) → J → V)
    (hf : ∀ j,IsPolynomialFamily (fun p => f p j)) : IsPolynomialFamily f := by
  classical
  have h := IsPolynomialFamily.sum (fun j =>
    (hf j).linear_comp (LinearMap.single K (fun _ : J => V) j))
  simpa only [LinearMap.single_apply,Finset.univ_sum_single] using h

theorem graphVector_polynomial {a k : ℕ} (j : Fin k ↪ Fin a) :
    IsPolynomialFamily (graphVector (K := K) j) := by
  apply polynomial_pi
  intro i
  apply polynomial_pi
  intro l
  simpa only [eval_graphPolynomial] using
    HomogeneousEmptyFiberOpen.polynomial_eval_family (graphPolynomial (K := K) j i l)

abbrev graphParameterCount {a k : ℕ} (j : Fin k ↪ Fin a) := Fintype.card (GraphParameters j)

def graphFromFin {a k : ℕ} (j : Fin k ↪ Fin a) (u : Fin (graphParameterCount j) → K) :
    Fin k → Fin a → K := graphVector j (u ∘ Fintype.equivFin (GraphParameters j))

theorem graphFromFin_polynomial {a k : ℕ} (j : Fin k ↪ Fin a) :
    IsPolynomialFamily (graphFromFin (K := K) j) :=
  polynomial_family_reindex (graphVector_polynomial j) (Fintype.equivFin (GraphParameters j))

theorem graphParameterCount_bound {a k : ℕ} (j : Fin k ↪ Fin a) :
    graphParameterCount j≤a*k := by
  rw [graphParameterCount,card_coefficient_positions]
  nlinarith [Nat.sub_le a k]

theorem exists_graphFromFin {a k : ℕ} (S : Submodule K (Fin a → K)) (hk : finrank K S=k) :
    ∃ j : Fin k ↪ Fin a,∃ u : Fin (graphParameterCount j) → K,
      Submodule.span K (Set.range (graphFromFin j u))=S := by
  obtain ⟨j,A,hA⟩ := exists_chart S hk
  let u : Fin (graphParameterCount j) → K := fun i =>
    A ((Fintype.equivFin (GraphParameters j)).symm i).1
      ((Fintype.equivFin (GraphParameters j)).symm i).2
  refine ⟨j,u,?_⟩
  rw [graphFromFin,graphVector_span]
  have he : graphCoefficients j (u ∘ Fintype.equivFin (GraphParameters j))=A := by
    funext l i
    simp only [graphCoefficients,Function.comp_apply,u,Equiv.symm_apply_apply]
  rw [he,hA]

variable {a b T T₀ H k : ℕ}

def chartBottom (j : Fin k ↪ Fin a) :
    (Fin (T₀+graphParameterCount j) → K) →ₗ[K] (Fin T₀ → K) :=
  LinearMap.pi fun i => LinearMap.proj (Fin.castAdd (graphParameterCount j) i)

def chartGraphCoordinates (j : Fin k ↪ Fin a) :
    (Fin (T₀+graphParameterCount j) → K) →ₗ[K] (Fin (graphParameterCount j) → K) :=
  LinearMap.pi fun i => LinearMap.proj (Fin.natAdd T₀ i)

@[simp] theorem chartBottom_append (j : Fin k ↪ Fin a) (t : Fin T₀ → K)
    (u : Fin (graphParameterCount j) → K) : chartBottom j (Fin.append t u)=t := by
  ext i
  exact Fin.append_left t u i

@[simp] theorem chartGraphCoordinates_append (j : Fin k ↪ Fin a) (t : Fin T₀ → K)
    (u : Fin (graphParameterCount j) → K) : chartGraphCoordinates j (Fin.append t u)=u := by
  ext i
  exact Fin.append_right t u i

def affineKernelChart
    (mu₀ : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T₀ → K))
    (muH : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin H → K))
    (j : Fin k ↪ Fin a) (p : Fin (T₀+graphParameterCount j) → K) :
    ((Fin H → K) × K) →ₗ[K] (Fin (k*b) → K) :=
  affineGraphConstraint mu₀ muH (graphFromFin j (chartGraphCoordinates j p)) (chartBottom j p)

theorem affineKernelChart_polynomial
    (mu₀ : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T₀ → K))
    (muH : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin H → K))
    (j : Fin k ↪ Fin a) : IsPolynomialFamily (affineKernelChart mu₀ muH j) := by
  apply affineGraphConstraint_polynomial
  · exact polynomial_family_reindex (graphFromFin_polynomial j) (Fin.natAdd T₀)
  · exact isPolynomialFamily_linear (chartBottom (K := K) (T₀ := T₀) j)

def chartCovector (res : ((Fin T₀ → K) × (Fin H → K)) →ₗ[K] (Fin T → K))
    (j : Fin k ↪ Fin a) (p : Fin (T₀+graphParameterCount j) → K) (x : (Fin H → K) × K) : Fin T → K :=
  res (x.2 • chartBottom j p,x.1)

theorem chartCovector_polynomial
    (res : ((Fin T₀ → K) × (Fin H → K)) →ₗ[K] (Fin T → K)) (j : Fin k ↪ Fin a) :
    IsPolynomialFamily (fun p : (Fin (T₀+graphParameterCount j) ⊕
      Fin (finrank K ((Fin H → K) × K))) → K => chartCovector res j
        (fun i => p (.inl i)) ((Module.finBasis K _).equivFun.symm (fun i => p (.inr i)))) := by
  let E := (Fin H → K) × K
  let I := Fin (T₀+graphParameterCount j) ⊕ Fin (finrank K E)
  let bot : (I → K) →ₗ[K] (Fin T₀ → K) :=
    (chartBottom j).comp (LinearMap.pi fun i => LinearMap.proj (Sum.inl i))
  let x : (I → K) →ₗ[K] E := (Module.finBasis K E).equivFun.symm.toLinearMap.comp
    (LinearMap.pi fun i => LinearMap.proj (Sum.inr i))
  have hb := isPolynomialFamily_linear bot
  have hx := isPolynomialFamily_linear x
  exact (((hx.linear_comp (LinearMap.snd K _ _)).smul hb).prod_mk
    (hx.linear_comp (LinearMap.fst K _ _))).linear_comp res

theorem affineKernelChart_rank
    (mu₀ : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T₀ → K))
    (muH : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin H → K))
    (j : Fin k ↪ Fin a) (t : Fin T₀ → K) (u : Fin (graphParameterCount j) → K) :
    finrank K (BilinearImage.image muH (Submodule.span K (Set.range (graphFromFin j u))))≤
      finrank K (affineKernelChart mu₀ muH j (Fin.append t u)).range := by
  unfold affineKernelChart
  rw [chartBottom_append (K := K), chartGraphCoordinates_append (K := K)]
  exact affineGraphConstraint_rank mu₀ muH (graphFromFin j u) t

end Froberg
