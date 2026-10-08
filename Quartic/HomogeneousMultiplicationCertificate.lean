import Quartic.HomogeneousNullstellensatz

/-! # Finite-degree multiplication certificates for geometric projective emptiness -/
noncomputable section
namespace Quartic.HomogeneousMultiplicationCertificate
open Module MvPolynomial HomogeneousNullstellensatz
variable {K : Type*} [Field K] {s r : ℕ}

/-- Multiply into degree N; a generator of larger degree contributes zero. -/
def term {d : ℕ} (f : Forms K s d) (N : ℕ) : Forms K s (N-d) →ₗ[K] Forms K s N :=
  if hd : d ≤ N then
    { toFun := fun u => ⟨u.val*f.val, by
        change (u.val*f.val).IsHomogeneous N
        have h := u.property.mul f.property
        simpa only [Nat.sub_add_cancel hd] using h⟩
      map_add' := fun u v => Subtype.ext (add_mul _ _ _)
      map_smul' := fun a u => Subtype.ext (smul_mul_assoc _ _ _) }
  else 0

@[simp] theorem term_val {d : ℕ} (f : Forms K s d) (N : ℕ) (u : Forms K s (N-d)) :
    (term f N u).val = if d ≤ N then u.val*f.val else 0 := by
  unfold term
  split_ifs <;> rfl

/-- One fixed finite-dimensional map whose full rank certifies projective emptiness. -/
def multiplication (d : Fin r → ℕ) (f : ∀ j, Forms K s (d j)) (N : ℕ) :
    (∀ j, Forms K s (N-d j)) →ₗ[K] Forms K s N :=
  ∑ j, (term (f j) N).comp (LinearMap.proj j)

@[simp] theorem multiplication_val (d : Fin r → ℕ) (f : ∀ j, Forms K s (d j))
    (N : ℕ) (u : ∀ j, Forms K s (N-d j)) :
    (multiplication d f N u).val = ∑ j, if d j ≤ N then (u j).val*(f j).val else 0 := by
  simp [multiplication]

/-- Homogeneous extraction gives the finite map directly from arbitrary ideal coefficients. -/
theorem component_sum_products (d : Fin r → ℕ) (f : ∀ j, Forms K s (d j))
    (N : ℕ) (u : Fin r → Poly K s) :
    homogeneousComponent N (∑ j, u j*(f j).val) =
      (multiplication d f N (fun j => ⟨homogeneousComponent (N-d j) (u j),
        homogeneousComponent_isHomogeneous _ _⟩)).val := by
  classical
  rw [map_sum,multiplication_val]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hd : d j ≤ N
  · simpa only [hd,↓reduceIte] using component_mul_homogeneous (u j) (f j) hd
  · simpa only [hd,↓reduceIte] using component_mul_homogeneous_of_lt (u j) (f j) (by omega)

/-- Ideal membership of all degree-N forms implies actual finite-degree surjectivity. -/
theorem surjective_of_all_forms_mem (d : Fin r → ℕ) (f : ∀ j, Forms K s (d j)) (N : ℕ)
    (hmem : ∀ p : Forms K s N, p.val ∈ Ideal.span (Set.range (fun j => (f j).val))) :
    Function.Surjective (multiplication d f N) := by
  intro p
  obtain ⟨u,hu⟩ := Ideal.mem_span_range_iff_exists_fun.mp (hmem p)
  refine ⟨fun j => ⟨homogeneousComponent (N-d j) (u j), homogeneousComponent_isHomogeneous _ _⟩, ?_⟩
  apply Subtype.ext
  rw [← component_sum_products, hu, homogeneousComponent_eq_self p.property]

/-- The finite-degree spanning certificate follows from the Nullstellensatz. -/
theorem exists_surjective_degree {L : Type*} [Field L] [Algebra K L] [IsAlgClosed L]
    (d : Fin r → ℕ) (f : ∀ j, Forms K s (d j))
    (hempty : ∀ x : Fin s → L, (∀ j, aeval x (f j).val = 0) → x = 0) :
    ∃ N : ℕ, 0 < N ∧ Function.Surjective (multiplication d f N) := by
  obtain ⟨N,hN,hmem⟩ := exists_degree_all_forms_mem (fun j => (f j).val) hempty
  exact ⟨N,hN,surjective_of_all_forms_mem d f N hmem⟩

/-- A spanning certificate excludes nonzero solutions over every extension field. -/
theorem zero_of_surjective {L : Type*} [Field L] [Algebra K L]
    (d : Fin r → ℕ) (f : ∀ j, Forms K s (d j)) (N : ℕ) (hN : 0 < N)
    (hsurj : Function.Surjective (multiplication d f N))
    (x : Fin s → L) (hx : ∀ j, aeval x (f j).val = 0) : x = 0 := by
  classical
  have heval (p : Forms K s N) : aeval x p.val = 0 := by
    obtain ⟨u,rfl⟩ := hsurj p
    rw [multiplication_val,map_sum]
    apply Finset.sum_eq_zero
    intro j _
    split_ifs <;> simp [map_mul,hx]
  funext i
  change x i = 0
  have hp : ((X i : Poly K s)^N).IsHomogeneous N := by
    simpa using (isHomogeneous_X K i).pow N
  have hz := heval ⟨(X i)^N,hp⟩
  simpa only [map_pow, aeval_X, pow_eq_zero_iff (Nat.ne_of_gt hN)] using hz

end Quartic.HomogeneousMultiplicationCertificate
