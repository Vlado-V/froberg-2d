module

public import Quartic.PolynomialSubspaceCovectorCharts
public import Quartic.SlicedCovectorAvoidance
public import Froberg.BilinearScalarFamily
public import Mathlib.LinearAlgebra.Dual.Lemmas

@[expose] public section

/-! Actual covector strata for scalar multiplication: full Grassmannian charts,
exact shared-coefficient equations, and their negative-incidence consequences. -/
noncomputable section
namespace Froberg.BilinearCovectorStrata
open Module MvPolynomial Quartic
open BilinearCovectorCharts (covector graphPolynomial GraphParameters)
open BilinearCoefficientKernel (relationMap)
variable {K : Type*} [Field K] {a b T r e q t : ℕ}

/-- The polynomial graph family covers every r-dimensional source subspace. -/
theorem graph_covers (L : Submodule K (Fin a → K)) (hL : finrank K L = r) :
    PolynomialSubspaceCovectorCharts.Covered
      (fun j : Fin r ↪ Fin a => graphPolynomial (K := K) j) L := by
  obtain ⟨j,A,hA⟩ := SubspaceCharts.exists_chart L hL
  refine ⟨j,fun z => A z.1 z.2,?_⟩
  have hvec : PolynomialSubspaceCovectorCharts.vector
      (graphPolynomial (K := K) j) (fun z => A z.1 z.2) =
      BilinearCovectorCharts.graphVector j (fun z => A z.1 z.2) := by
    funext i k
    exact BilinearCovectorCharts.eval_graphPolynomial _ _ _ _
  rw [PolynomialSubspaceCovectorCharts.subspace,hvec,BilinearCovectorCharts.graphVector_span]
  exact hA

/-- The graph chart has exactly r(a-r) affine parameters. -/
theorem graph_parameter_count (j : Fin r ↪ Fin a) :
    Fintype.card (GraphParameters j) = r*(a-r) := by
  simp only [GraphParameters,Fintype.card_prod,SubspaceCharts.card_outside,Fintype.card_fin,Nat.mul_comm]

/-- An actual image-rank lower bound excludes the whole r-kernel stratum
when its exact conditioned projective parameter count is negative. -/
theorem generic_excludes_stratum [Infinite K]
    (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (hgrowth : ∀ L : Submodule K (Fin a → K), finrank K L = r →
      e ≤ finrank K (BilinearImage.image mu L))
    (hcount : (r*(a-r) : ℕ)+(T : ℤ)-e-1 < (q*(a-r) : ℕ)) :
    ∃ P : MvPolynomial (Fin q × Fin b) K,
      (∃ Q, eval Q P ≠ 0) ∧ ∀ Q, eval Q P ≠ 0 →
      ∀ ell : Fin T → K, ell ≠ 0 → finrank K (LinearMap.ker (relationMap mu ell)) = r →
      ∃ i : Fin q, ∃ x : Fin a → K, covector ell (mu (fun k => Q (i,k)) x) ≠ 0 := by
  obtain ⟨P,hP,hgood⟩ := PolynomialSubspaceCovectorCharts.principal_open_excludes_covered_stratum_of_int_bound
    (d := r) (e := e) (q := q) mu (fun j : Fin r ↪ Fin a => graphPolynomial (K := K) j)
    (r*(a-r) : ℕ) (fun j => by rw [graph_parameter_count]) hcount
  exact ⟨P,hP,fun Q hQ ell hell hr =>
    hgood Q hQ ell hell hr (graph_covers _ hr) (hgrowth _ hr)⟩

/-- The sliced version retains the same common scalar family and gives one
additional independent equation per target slice. -/
theorem generic_excludes_sliced_stratum [Infinite K]
    (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (hgrowth : ∀ L : Submodule K (Fin a → K), finrank K L = r →
      e ≤ finrank K (BilinearImage.image mu L))
    (hcount : (r*(a-r) : ℕ)+(T : ℤ)-e-1 < (q*(a-r)+t : ℕ)) :
    ∃ P : MvPolynomial (Fin (finrank K (SharedCovectorPolynomial.Input K b T q t))) K,
      (∃ z : SharedCovectorPolynomial.Input K b T q t,
        eval (PolynomialBilinearCoordinates.coordinates K _ z) P ≠ 0) ∧
      ∀ z : SharedCovectorPolynomial.Input K b T q t,
        eval (PolynomialBilinearCoordinates.coordinates K _ z) P ≠ 0 →
        ∀ ell : Fin T → K, ell ≠ 0 → finrank K (LinearMap.ker (relationMap mu ell)) = r →
        ¬ ((∀ i x, covector ell (mu (z.1 i) x) = 0) ∧
          (∀ j, covector ell (z.2 j) = 0)) := by
  obtain ⟨P,hP,hgood⟩ := SlicedCovectorAvoidance.principal_open_excludes_sliced_stratum_of_int_bound
    (d := r) (e := e) (q := q) (s := t) mu (fun j : Fin r ↪ Fin a => graphPolynomial (K := K) j)
    (r*(a-r) : ℕ) (fun j => by rw [graph_parameter_count]) hcount
  exact ⟨P,hP,fun Q hQ ell hell hr =>
    hgood Q hQ ell hell hr (graph_covers _ hr) (hgrowth _ hr)⟩

/-- No nonzero coordinate covector annihilates all columns exactly when
scalar-family multiplication is surjective. -/
theorem surjective_of_covectors
    (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K)) (Q : Fin q → Fin b → K)
    (h : ∀ ell : Fin T → K, ell ≠ 0 →
      ∃ i : Fin q, ∃ x : Fin a → K, covector ell (mu (Q i) x) ≠ 0) :
    Function.Surjective (BilinearScalarFamily.multiplication mu Q) := by
  classical
  apply LinearMap.dualMap_injective_iff.mp
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro ell hell
  let c : Fin T → K := fun k => ell (Pi.single k 1)
  have hc : covector c = ell := by
    apply LinearMap.ext
    intro x
    conv_rhs => rw [← (Pi.basisFun K (Fin T)).sum_equivFun x]
    simp [covector,c,Pi.basisFun_apply,Pi.basisFun_equivFun,smul_eq_mul,mul_comm]
  by_contra hne
  have hcne : c ≠ 0 := by
    intro hz
    apply hne
    rw [← hc,hz]
    ext x
    simp [BilinearCovectorCharts.covector_apply]
  obtain ⟨i,x,hix⟩ := h c hcne
  apply hix
  rw [hc]
  have hh := LinearMap.congr_fun hell (Pi.single i x)
  change ell (BilinearScalarFamily.multiplication mu Q (Pi.single i x)) = 0 at hh
  rw [BilinearScalarFamily.multiplication_apply] at hh
  simpa only [Pi.single_apply,apply_ite,map_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true] using hh

/-- Intersecting all kernel-dimension strata produces an actual nonempty open
of surjective scalar-family maps. -/
theorem generic_surjective_of_budgets [Infinite K]
    (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (E : Fin (a+1) → ℕ)
    (hgrowth : ∀ r : Fin (a+1), ∀ L : Submodule K (Fin a → K), finrank K L = r.val →
      E r ≤ finrank K (BilinearImage.image mu L))
    (hcount : ∀ r : Fin (a+1), (r.val*(a-r.val) : ℕ)+(T : ℤ)-E r-1 < (q*(a-r.val) : ℕ)) :
    ∃ P : MvPolynomial (Fin q × Fin b) K,
      (∃ Q, eval Q P ≠ 0) ∧ ∀ Q, eval Q P ≠ 0 →
      Function.Surjective (BilinearScalarFamily.multiplication mu (fun i k => Q (i,k))) := by
  classical
  choose P hP hgood using fun r : Fin (a+1) =>
    generic_excludes_stratum (e := E r) mu (hgrowth r) (hcount r)
  have hne : ∀ r, P r ≠ 0 := by
    intro r hz
    obtain ⟨Q,hQ⟩ := hP r
    simp [hz] at hQ
  obtain ⟨Q₀,hQ₀⟩ := nonempty_principal_intersection P hne
  refine ⟨∏ r, P r,⟨Q₀,?_⟩,?_⟩
  · simpa only [map_prod] using Finset.prod_ne_zero_iff.mpr (fun r _ => hQ₀ r)
  intro Q hQ
  apply surjective_of_covectors
  intro ell hell
  have hle : finrank K (LinearMap.ker (relationMap mu ell)) ≤ a := by
    simpa using (LinearMap.ker (relationMap mu ell)).finrank_le
  let r : Fin (a+1) := ⟨finrank K (LinearMap.ker (relationMap mu ell)),by omega⟩
  have hQr : eval Q (P r) ≠ 0 := (Finset.prod_ne_zero_iff.mp (by simpa only [map_prod] using hQ)) r (Finset.mem_univ r)
  exact hgood r Q hQr ell hell rfl

end Froberg.BilinearCovectorStrata
