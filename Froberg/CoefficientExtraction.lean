module

public import Froberg.FormalHyperplane

@[expose] public section

/-! Coefficient extraction on actual symmetric relations.  Separation of the
new symmetric products is precisely what makes the quotient by old relations
inject into the new coefficient space. -/
noncomputable section
namespace Froberg
open Module
variable {K : Type} [Field K]
variable {V Z : Type*} [AddCommGroup V] [Module K V] [AddCommGroup Z] [Module K Z]
variable {r : ℕ}

theorem formalMixed_sup (W F : Submodule K V) :
    formalMixed (W ⊔ F) = formalMixed W ⊔ formalMixed F := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨a, b, ha, rfl⟩
    obtain ⟨w, hw, f, hf, rfl⟩ := Submodule.mem_sup.mp ha
    change (symProdLeft (K := K) b) (w + f) ∈ _
    rw [map_add]
    exact Submodule.add_mem _
      ((show formalMixed W ≤ formalMixed W ⊔ formalMixed F from le_sup_left)
        (symProd_mem_formalMixed W hw b))
      ((show formalMixed F ≤ formalMixed W ⊔ formalMixed F from le_sup_right)
        (symProd_mem_formalMixed F hf b))
  · exact sup_le (formalMixed_mono le_sup_left) (formalMixed_mono le_sup_right)

/-- A coordinate derivative followed by reduction modulo the whole generator space. -/
def relationCoefficientMap (G : Submodule K V) (dual : Fin r → V →ₗ[K] K) :
    SymmetricSquare K V →ₗ[K] (Fin r → V ⧸ G) :=
  LinearMap.pi fun i => G.mkQ.comp (symmetricContraction (dual i))

@[simp] theorem relationCoefficientMap_apply (G : Submodule K V)
    (dual : Fin r → V →ₗ[K] K) (x : SymmetricSquare K V) (i : Fin r) :
    relationCoefficientMap G dual x i = G.mkQ (symmetricContraction (dual i) x) := rfl

theorem relationCoefficientMap_kills_old (W G : Submodule K V) (hWG : W ≤ G)
    (dual : Fin r → V →ₗ[K] K) (hdual : ∀ i w, w ∈ W → dual i w = 0) :
    formalMixed W ≤ (relationCoefficientMap G dual).ker := by
  apply Submodule.span_le.mpr
  rintro _ ⟨w, v, hw, rfl⟩
  apply funext
  intro i
  simp only [relationCoefficientMap_apply, symmetricContraction_symProd,
    hdual i w hw, zero_smul, zero_add, map_smul]
  rw [show G.mkQ w = 0 from (Submodule.Quotient.mk_eq_zero G).mpr (hWG hw)]
  simp

theorem relationCoefficientMap_coefficients (G : Submodule K V)
    (f : Fin r → V) (hfG : ∀ i, f i ∈ G) (dual : Fin r → V →ₗ[K] K)
    (hdual : ∀ i j, dual i (f j) = if i = j then 1 else 0) (a : Fin r → V) :
    relationCoefficientMap G dual (formalCoefficientMap f a) = fun i => G.mkQ (a i) := by
  classical
  funext i
  simp only [relationCoefficientMap_apply, formalCoefficientMap_apply,
    map_sum, symmetricContraction_symProd, map_add, map_smul, hdual]
  have hz (j : Fin r) : G.mkQ (f j) = 0 :=
    (Submodule.Quotient.mk_eq_zero G).mpr (hfG j)
  simp [hz]

/-- If the new coefficients vanish modulo all generators, the formal relation
is an old mixed product plus a symmetric product of new generators. -/
theorem relationCoefficientMap_kernel_bound (W : Submodule K V) (f : Fin r → V)
    (dual : Fin r → V →ₗ[K] K)
    (hdualW : ∀ i w, w ∈ W → dual i w = 0)
    (hdualF : ∀ i j, dual i (f j) = if i = j then 1 else 0) :
    formalMixed (W ⊔ Submodule.span K (Set.range f)) ⊓
        (relationCoefficientMap (W ⊔ Submodule.span K (Set.range f)) dual).ker ≤
      formalMixed W ⊔ formalSquare (Submodule.span K (Set.range f)) := by
  classical
  let F := Submodule.span K (Set.range f)
  let G := W ⊔ F
  have hf (i : Fin r) : f i ∈ F := Submodule.subset_span ⟨i, rfl⟩
  have hkill := relationCoefficientMap_kills_old W G le_sup_left dual hdualW
  intro x hx
  obtain ⟨w, hw, y, hy, hxy⟩ := Submodule.mem_sup.mp ((formalMixed_sup W F).le hx.1)
  obtain ⟨a, rfl⟩ := (range_formalCoefficientMap f).ge hy
  have hca : relationCoefficientMap G dual (formalCoefficientMap f a) = 0 := by
    have hw0 : relationCoefficientMap G dual w = 0 := hkill hw
    have hx0 : relationCoefficientMap G dual x = 0 := hx.2
    rw [← hxy, map_add, hw0, zero_add] at hx0
    exact hx0
  rw [relationCoefficientMap_coefficients G f (fun i => (show F ≤ G from le_sup_right) (hf i))
    dual hdualF a] at hca
  have ha (i : Fin r) : a i ∈ G :=
    (Submodule.Quotient.mk_eq_zero G).mp (congrFun hca i)
  choose aW haW aF haF haeq using fun i => Submodule.mem_sup.mp (ha i)
  have hdecomp : formalCoefficientMap (K := K) f a =
      (∑ i, symProd (f i) (aW i)) + ∑ i, symProd (f i) (aF i) := by
    rw [formalCoefficientMap_apply, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← haeq i, symProd_comm (f i) (aW i + aF i)]
    change (symProdLeft (K := K) (f i)) (aW i + aF i) = _
    rw [map_add]
    change symProd (aW i) (f i) + symProd (aF i) (f i) = _
    rw [symProd_comm (aW i) (f i), symProd_comm (aF i) (f i)]
  have hWsum : (∑ i, symProd (f i) (aW i)) ∈ formalMixed W :=
    Submodule.sum_mem _ fun i _ => symProd_mem_formalMixed_right W _ (haW i)
  have hFsum : (∑ i, symProd (f i) (aF i)) ∈ formalSquare F := by
    apply Submodule.sum_mem
    intro i _
    exact ⟨symProd (⟨f i, hf i⟩ : F) (⟨aF i, haF i⟩ : F),
      symmetricMap_symProd F.subtype _ _⟩
  apply Submodule.mem_sup.mpr
  refine ⟨w + ∑ i, symProd (f i) (aW i), (formalMixed W).add_mem hw hWsum,
    ∑ i, symProd (f i) (aF i), hFsum, ?_⟩
  rw [add_assoc, ← hdecomp]
  exact hxy

/-- Separation in the polynomial quotient removes the new symmetric summand. -/
theorem separated_relation_kernel (μ : SymmetricSquare K V →ₗ[K] Z)
    (W F : Submodule K V)
    (hsep : formalSquare F ⊓ ((formalMixed W).map μ).comap μ = ⊥) :
    μ.ker ⊓ (formalMixed W ⊔ formalSquare F) ≤ formalMixed W := by
  intro x hx
  obtain ⟨w, hw, f, hf, hsum⟩ := Submodule.mem_sup.mp hx.2
  have hμf : μ f = -μ w := by
    have hx0 : μ x = 0 := hx.1
    rw [← hsum, map_add] at hx0
    exact eq_neg_of_add_eq_zero_right hx0
  have hf0 : f = 0 := by
    have hm : μ f ∈ (formalMixed W).map μ := by
      rw [hμf, ← map_neg]
      exact ⟨-w, (formalMixed W).neg_mem hw, rfl⟩
    have hmem : f ∈ formalSquare F ⊓ ((formalMixed W).map μ).comap μ := ⟨hf, hm⟩
    rw [hsep] at hmem
    exact hmem
  rw [← hsum, hf0, add_zero]
  exact hw

/-- On polynomial relations, the coefficient map has exactly the old relations as kernel. -/
theorem relationCoefficientMap_exact_kernel (μ : SymmetricSquare K V →ₗ[K] Z)
    (W : Submodule K V) (f : Fin r → V) (dual : Fin r → V →ₗ[K] K)
    (hdualW : ∀ i w, w ∈ W → dual i w = 0)
    (hdualF : ∀ i j, dual i (f j) = if i = j then 1 else 0)
    (hsep : formalSquare (Submodule.span K (Set.range f)) ⊓
      ((formalMixed W).map μ).comap μ = ⊥) :
    (relationCoefficientMap (W ⊔ Submodule.span K (Set.range f)) dual).ker ⊓
      (μ.ker ⊓ formalMixed (W ⊔ Submodule.span K (Set.range f))) =
        μ.ker ⊓ formalMixed W := by
  apply le_antisymm
  · intro x hx
    exact ⟨hx.2.1, separated_relation_kernel μ W _ hsep
      ⟨hx.2.1, relationCoefficientMap_kernel_bound W f dual hdualW hdualF ⟨hx.2.2, hx.1⟩⟩⟩
  · intro x hx
    exact ⟨relationCoefficientMap_kills_old W _ le_sup_left dual hdualW hx.2,
      hx.1, formalMixed_mono le_sup_left hx.2⟩

/-- Coordinates on the new generators modulo the old ones always exist. -/
theorem exists_relative_coordinate_functionals (W : Submodule K V) (f : Fin r → V)
    (hf : LinearIndependent K (fun i => W.mkQ (f i))) :
    ∃ dual : Fin r → V →ₗ[K] K,
      (∀ i w, w ∈ W → dual i w = 0) ∧
      (∀ i j, dual i (f j) = if i = j then 1 else 0) := by
  obtain ⟨dual, hdual⟩ := exists_coordinate_functionals (fun i => W.mkQ (f i)) hf
  refine ⟨fun i => (dual i).comp W.mkQ, ?_, hdual⟩
  intro i w hw
  change dual i (W.mkQ w) = 0
  have hw0 : W.mkQ w = 0 := (Submodule.Quotient.mk_eq_zero W).mpr hw
  rw [hw0, map_zero]

end Froberg
