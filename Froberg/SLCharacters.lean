import Froberg.InvariantRationalLine

/-! # Special-linear characters without regularity hypotheses

Over an infinite field every character of a special-linear group in a
commutative group is trivial.  This removes any need to establish separate
polynomial dependence of the scalar obtained by primitive normalization.
-/

namespace Froberg
open Matrix
variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I]

/-- Diagonal conjugation rescales a transvection by a square. -/
theorem sl_diag2n_transvection (i j : I) (hij : i ≠ j) (a b : K) (ha : a ≠ 0) :
    SpecialLinearGroup.diag2n hij a ha * SpecialLinearGroup.transvection hij b =
      SpecialLinearGroup.transvection hij (a ^ 2 * b) *
        SpecialLinearGroup.diag2n hij a ha := by
  ext k l
  by_cases hki : k = i <;> by_cases hkj : k = j <;>
    by_cases hli : l = i <;> by_cases hlj : l = j <;>
    subst_vars <;> try contradiction
  all_goals
    simp_all [SpecialLinearGroup.diag2n_coe, SpecialLinearGroup.coe_mul,
      SpecialLinearGroup.transvection_coe, Matrix.diagonal_mul, Matrix.mul_diagonal,
      Matrix.one_apply, Matrix.single_apply, eq_comm, pow_two]
  all_goals field_simp
  all_goals ring

variable [Infinite K]

/-- Every character into a commutative group kills all transvections. -/
theorem sl_group_character_transvection {C : Type*} [CommGroup C]
    (χ : SpecialLinearGroup I K →* C) (i j : I) (hij : i ≠ j) (c : K) :
    χ (SpecialLinearGroup.transvection hij c) = 1 := by
  classical
  obtain ⟨a, ha⟩ := (Finset.exists_notMem ({0, 1, -1} : Finset K))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha
  have hasq : a ^ 2 ≠ 1 := sq_ne_one_iff.mpr ha.2
  let b := c / (a ^ 2 - 1)
  let D := SpecialLinearGroup.diag2n hij a ha.1
  have hrescale : χ (SpecialLinearGroup.transvection hij (a ^ 2 * b)) =
      χ (SpecialLinearGroup.transvection hij b) := by
    apply mul_right_cancel (b := χ D)
    calc
      χ (SpecialLinearGroup.transvection hij (a ^ 2 * b)) * χ D =
          χ D * χ (SpecialLinearGroup.transvection hij b) := by
        have hh := congrArg χ (sl_diag2n_transvection i j hij a b ha.1)
        simpa only [map_mul] using hh.symm
      _ = _ := mul_comm _ _
  have hdiff : a ^ 2 * b + (-b) = c := by
    dsimp [b]
    field_simp [sub_ne_zero_of_ne hasq]
    ring
  calc
    χ (SpecialLinearGroup.transvection hij c) =
        χ (SpecialLinearGroup.transvection hij (a ^ 2 * b)) *
          χ (SpecialLinearGroup.transvection hij (-b)) := by
      rw [← hdiff, SpecialLinearGroup.transvection_add, map_mul]
    _ = χ (SpecialLinearGroup.transvection hij b) *
        χ (SpecialLinearGroup.transvection hij (-b)) := by rw [hrescale]
    _ = 1 := by rw [← map_mul, SpecialLinearGroup.transvection_mul_neg, map_one]

/-- Every character of `SL` over an infinite field in a commutative group
is trivial; this is the form of perfectness needed here. -/
theorem sl_group_character_trivial {C : Type*} [CommGroup C]
    (χ : SpecialLinearGroup I K →* C) (g : SpecialLinearGroup I K) : χ g = 1 := by
  rcases subsingleton_or_nontrivial I with hsub | hnontriv
  · have := hsub
    rw [Subsingleton.elim g 1, map_one]
  · have := hnontriv
    apply SpecialLinearGroup.diagonal_transvection_induction' (fun g => χ g = 1) g
    · intro i j hij a ha
      rw [sl_diag2n_decompose i j hij a ha]
      simp only [map_mul, sl_group_character_transvection, one_mul]
    · exact sl_group_character_transvection χ
    · intro g h hg hh
      rw [map_mul, hg, hh, one_mul]

/-- The same statement for a commutative monoid: a group homomorphism
automatically takes its values in the unit group. -/
theorem sl_character_trivial {C : Type*} [CommMonoid C]
    (χ : SpecialLinearGroup I K →* C) (g : SpecialLinearGroup I K) : χ g = 1 := by
  simpa only [MonoidHom.coe_toHomUnits, Units.val_one] using
    congrArg Units.val (sl_group_character_trivial χ.toHomUnits g)

/-- Every invariant line in an arbitrary linear representation of `SL`
is pointwise fixed. -/
theorem sl_invariant_line_fixed {V : Type*} [AddCommGroup V] [Module K V]
    (ρ : Representation K (SpecialLinearGroup I K) V)
    (v : V) (hv : v ≠ 0) (hline : ∀ g, ∃ a : K, ρ g v = a • v) :
    ∀ g, ρ g v = v := by
  obtain ⟨χ, hχ⟩ := representation_scalar_character ρ v hv hline
  intro g
  rw [hχ, sl_character_trivial χ g, one_smul]

/-- Primitive polynomial normalization upgrades invariant rational lines
to fixed polynomial vectors, without a regularity premise. -/
theorem sl_primitive_rational_line_fixed
    {σ F J : Type*} [Field F]
    [Algebra (MvPolynomial σ K) F] [IsFractionRing (MvPolynomial σ K) F]
    [Fintype J] [DecidableEq J]
    (ρ : Representation K (SpecialLinearGroup I K) (J → MvPolynomial σ K))
    (v : J → MvPolynomial σ K) (hv : v ≠ 0) (hprim : IsPrimitiveVector v)
    (e : SpecialLinearGroup I K → MvPolynomial σ K ≃+* MvPolynomial σ K)
    (A B : SpecialLinearGroup I K → Matrix J J (MvPolynomial σ K))
    (hBA : ∀ g, B g * A g = 1)
    (haction : ∀ g, ρ g v = A g *ᵥ (fun i => e g (v i)))
    (hline : ∀ g, ∃ c : F, ∀ i, algebraMap (MvPolynomial σ K) F ((ρ g v) i) =
      c * algebraMap (MvPolynomial σ K) F (v i)) :
    ∀ g, ρ g v = v := by
  apply sl_invariant_line_fixed ρ v hv
  intro g
  have hprim' : IsPrimitiveVector (ρ g v) := by
    rw [haction]
    exact (hprim.map (e g)).mulVec (A g) (B g) (hBA g)
  obtain ⟨c, hc⟩ := hline g
  obtain ⟨a, _, _, ha⟩ := primitive_polynomial_vectors_constant_scalar
    v (ρ g v) hprim hprim' c hc
  refine ⟨a, ?_⟩
  funext i
  simpa only [Pi.smul_apply, MvPolynomial.smul_eq_C_mul] using ha i

end Froberg
