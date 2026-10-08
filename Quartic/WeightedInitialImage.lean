import Quartic.FilteredImage

/-!
# Multiplication images do not grow on passing to initial subspaces

For a bilinear multiplication between finite ordered direct sums, assume that
each homogeneous multiplier sends a source component into one target component,
and that this component shift strictly preserves the source order. Then the
multiplication image of the initial subspace is contained in the initial
subspace of the original multiplication image. The resulting dimension bound
uses only finite filtrations and actual products.
-/

noncomputable section
namespace Quartic.WeightedInitialImage
open Module FilteredImage
variable {K : Type*} [Field K]

section InitialSubspace
variable {n : ℕ} (E : Fin n → Type*)
  [∀ i, AddCommGroup (E i)] [∀ i, Module K (E i)]

/-- The graded initial subspace, assembled from its actual coordinate initial pieces. -/
def initialSubspace (L : Submodule K ((i : Fin n) → E i)) :
    Submodule K ((i : Fin n) → E i) :=
  Submodule.pi Set.univ (initialPiece E L)

@[simp] theorem mem_initialSubspace (L : Submodule K ((i : Fin n) → E i)) (v : (i : Fin n) → E i) :
    v ∈ initialSubspace E L ↔ ∀ i, v i ∈ initialPiece E L i := by
  simp [initialSubspace]

/-- The initial subspace is the actual finite product of its coordinate pieces. -/
def initialSubspaceEquiv (L : Submodule K ((i : Fin n) → E i)) :
    initialSubspace E L ≃ₗ[K] ((i : Fin n) → initialPiece E L i) where
  toFun x i := ⟨x.val i, (mem_initialSubspace E L x.val).mp x.property i⟩
  invFun x := ⟨fun i => (x i).val, (mem_initialSubspace E L _).mpr (fun i => (x i).property)⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := funext fun _ => Subtype.ext rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Taking initial components preserves every subspace dimension. -/
theorem initialSubspace_finrank [∀ i, FiniteDimensional K (E i)]
    (L : Submodule K ((i : Fin n) → E i)) :
    finrank K (initialSubspace E L) = finrank K L := by
  rw [(initialSubspaceEquiv E L).finrank_eq, Module.finrank_pi_fintype]
  exact sum_initialPiece_finrank E L

/-- A vector in a single initial component belongs to the full initial subspace. -/
theorem single_mem_initialSubspace (L : Submodule K ((i : Fin n) → E i))
    (i : Fin n) (v : E i) (hv : v ∈ initialPiece E L i) :
    Pi.single i v ∈ initialSubspace E L := by
  classical
  apply (mem_initialSubspace E L _).mpr
  intro j
  by_cases h : j = i
  · subst j
    simpa using hv
  · simpa only [Pi.single_eq_of_ne h] using (initialPiece E L j).zero_mem

end InitialSubspace

section LinearSupport
variable {n q : ℕ} {E : Fin n → Type*} {T : Fin q → Type*}
  [∀ i, AddCommGroup (E i)] [∀ i, Module K (E i)]
  [∀ i, AddCommGroup (T i)] [∀ i, Module K (T i)]

/-- The leading coordinate of an order-compatible block map is the image of
exactly the corresponding source coordinate. -/
theorem map_leading_coefficient (f : ((i : Fin n) → E i) →ₗ[K] ((i : Fin q) → T i))
    (shift : Fin n → Fin q) (hshift : Function.Injective shift)
    (hsupport : ∀ j (v : E j) k, k ≠ shift j → f (Pi.single j v) k = 0)
    (j : Fin n) (v : (i : Fin n) → E i) :
    f v (shift j) = f (Pi.single j (v j)) (shift j) := by
  classical
  conv_lhs => rw [← Finset.univ_sum_single v, map_sum, Finset.sum_apply]
  apply Finset.sum_eq_single j
  · intro k _ hkj
    exact hsupport k (v k) (shift j) (fun he => hkj (hshift he.symm))
  · simp

/-- A block map with increasing support shifts preserves the corresponding prefix flags. -/
theorem map_coordinateFlag (f : ((i : Fin n) → E i) →ₗ[K] ((i : Fin q) → T i))
    (shift : Fin n → Fin q) (hshift : StrictMono shift)
    (hsupport : ∀ j (v : E j) k, k ≠ shift j → f (Pi.single j v) k = 0)
    (j : Fin n) (v : (i : Fin n) → E i)
    (hv : v ∈ coordinateFlag (K := K) E (j.val + 1)) :
    f v ∈ coordinateFlag (K := K) T ((shift j).val + 1) := by
  classical
  intro k hk
  rw [← Finset.univ_sum_single v, map_sum, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro l _
  by_cases hlj : l ≤ j
  · apply hsupport
    have hs : shift l ≤ shift j := hshift.monotone hlj
    intro he
    subst k
    omega
  · have hzero : v l = 0 := hv l (by omega)
    simp [hzero]

/-- A vector supported at one coordinate is its corresponding single-coordinate vector. -/
theorem eq_single_of_support (w : (i : Fin q) → T i) (k : Fin q)
    (hw : ∀ l, l ≠ k → w l = 0) : w = Pi.single k (w k) := by
  classical
  funext l
  by_cases h : l = k
  · subst l; simp
  · simp [Pi.single_eq_of_ne h, hw l h]

end LinearSupport

section Multiplication
variable {I : Type*} [Fintype I] [DecidableEq I] {n q : ℕ}
  {A : I → Type*} {E : Fin n → Type*} {T : Fin q → Type*}
  [∀ i, AddCommGroup (A i)] [∀ i, Module K (A i)]
  [∀ i, AddCommGroup (E i)] [∀ i, Module K (E i)]
  [∀ i, AddCommGroup (T i)] [∀ i, Module K (T i)]

/-- The actual image under all multipliers in the given multiplier space. -/
def multiplicationImage
    (μ : ((a : I) → A a) →ₗ[K] ((i : Fin n) → E i) →ₗ[K] ((k : Fin q) → T k))
    (L : Submodule K ((i : Fin n) → E i)) : Submodule K ((k : Fin q) → T k) :=
  ⨆ a : (i : I) → A i, L.map (μ a)

omit [Fintype I] [DecidableEq I] in
/-- Every actual product lies in the full multiplication image. -/
theorem product_mem_image
    (μ : ((a : I) → A a) →ₗ[K] ((i : Fin n) → E i) →ₗ[K] ((k : Fin q) → T k))
    (L : Submodule K ((i : Fin n) → E i)) (a : (i : I) → A i)
    (v : (i : Fin n) → E i) (hv : v ∈ L) : μ a v ∈ multiplicationImage μ L :=
  (le_iSup (fun a => L.map (μ a)) a) ⟨v, hv, rfl⟩

omit [Fintype I] in
/-- A homogeneous product of an initial component lifts to the leading
coordinate of an actual product of the original subspace. -/
theorem homogeneous_initial_product_mem
    (μ : ((a : I) → A a) →ₗ[K] ((i : Fin n) → E i) →ₗ[K] ((k : Fin q) → T k))
    (shift : I → Fin n → Fin q) (hshift : ∀ a, StrictMono (shift a))
    (hgrade : ∀ a j (u : A a) (v : E j) k, k ≠ shift a j →
      μ (Pi.single a u) (Pi.single j v) k = 0)
    (L : Submodule K ((i : Fin n) → E i)) (a : I) (j : Fin n)
    (u : A a) (v : E j) (hv : v ∈ initialPiece E L j) :
    μ (Pi.single a u) (Pi.single j v) ∈ initialSubspace T (multiplicationImage μ L) := by
  classical
  obtain ⟨x, hx, hxj⟩ := hv
  change x j = v at hxj
  let f := μ (Pi.single a u)
  have hflag : f x ∈ coordinateFlag (K := K) T ((shift a j).val + 1) :=
    map_coordinateFlag f (shift a) (hshift a) (hgrade a · u) j x hx.2
  have hcomponent : f (Pi.single j v) (shift a j) = f x (shift a j) := by
    rw [map_leading_coefficient f (shift a) (hshift a).injective (hgrade a · u) j x, hxj]
  have hsingle : f (Pi.single j v) = Pi.single (shift a j) (f (Pi.single j v) (shift a j)) :=
    eq_single_of_support _ _ (hgrade a j u v)
  rw [hsingle]
  apply single_mem_initialSubspace
  rw [hcomponent]
  exact ⟨f x, ⟨product_mem_image μ L _ x hx.1, hflag⟩, rfl⟩

/-- The initial multiplication image embeds in the initial space of the actual image. -/
theorem multiplicationImage_initial_le
    (μ : ((a : I) → A a) →ₗ[K] ((i : Fin n) → E i) →ₗ[K] ((k : Fin q) → T k))
    (shift : I → Fin n → Fin q) (hshift : ∀ a, StrictMono (shift a))
    (hgrade : ∀ a j (u : A a) (v : E j) k, k ≠ shift a j →
      μ (Pi.single a u) (Pi.single j v) k = 0)
    (L : Submodule K ((i : Fin n) → E i)) :
    multiplicationImage μ (initialSubspace E L) ≤ initialSubspace T (multiplicationImage μ L) := by
  classical
  apply iSup_le
  intro a
  rintro _ ⟨v, hv, rfl⟩
  have ha : μ a v = ∑ b : I, ∑ j : Fin n,
      μ (Pi.single b (a b)) (Pi.single j (v j)) := by
    conv_lhs => rw [← Finset.univ_sum_single a, map_sum, LinearMap.sum_apply]
    apply Finset.sum_congr rfl
    intro b _
    conv_lhs => rw [← Finset.univ_sum_single v, map_sum]
  rw [ha]
  apply Submodule.sum_mem
  intro b _
  apply Submodule.sum_mem
  intro j _
  exact homogeneous_initial_product_mem μ shift hshift hgrade L b j (a b) (v j)
    ((mem_initialSubspace E L v).mp hv j)

/-- Quadratic, or any other graded, multiplication cannot gain image dimension
when the source subspace is replaced by its initial subspace. -/
theorem multiplicationImage_initial_finrank_le [∀ i, FiniteDimensional K (T i)]
    (μ : ((a : I) → A a) →ₗ[K] ((i : Fin n) → E i) →ₗ[K] ((k : Fin q) → T k))
    (shift : I → Fin n → Fin q) (hshift : ∀ a, StrictMono (shift a))
    (hgrade : ∀ a j (u : A a) (v : E j) k, k ≠ shift a j →
      μ (Pi.single a u) (Pi.single j v) k = 0)
    (L : Submodule K ((i : Fin n) → E i)) :
    finrank K (multiplicationImage μ (initialSubspace E L)) ≤ finrank K (multiplicationImage μ L) :=
  (Submodule.finrank_mono (multiplicationImage_initial_le μ shift hshift hgrade L)).trans_eq
    (initialSubspace_finrank T (multiplicationImage μ L))

/-- The replacement preserves source dimension and weakly decreases the actual multiplication image. -/
theorem initial_dimension_and_image_bound
    [∀ i, FiniteDimensional K (E i)] [∀ i, FiniteDimensional K (T i)]
    (μ : ((a : I) → A a) →ₗ[K] ((i : Fin n) → E i) →ₗ[K] ((k : Fin q) → T k))
    (shift : I → Fin n → Fin q) (hshift : ∀ a, StrictMono (shift a))
    (hgrade : ∀ a j (u : A a) (v : E j) k, k ≠ shift a j →
      μ (Pi.single a u) (Pi.single j v) k = 0)
    (L : Submodule K ((i : Fin n) → E i)) :
    finrank K (initialSubspace E L) = finrank K L ∧
      finrank K (multiplicationImage μ (initialSubspace E L)) ≤ finrank K (multiplicationImage μ L) :=
  ⟨initialSubspace_finrank E L, multiplicationImage_initial_finrank_le μ shift hshift hgrade L⟩

end Multiplication

/-- Strictly ordered additive weights imply the required order preservation.
Weights may have gaps, and shifts from different multiplier blocks may coincide. -/
theorem shift_strictMono_of_weights {I : Type*} {n q : ℕ}
    (sourceWeight : Fin n → ℕ) (targetWeight : Fin q → ℕ) (multiplierWeight : I → ℕ)
    (hs : StrictMono sourceWeight) (ht : StrictMono targetWeight)
    (shift : I → Fin n → Fin q)
    (hadd : ∀ a j, targetWeight (shift a j) = multiplierWeight a + sourceWeight j) :
    ∀ a, StrictMono (shift a) := by
  intro a i j hij
  apply ht.lt_iff_lt.mp
  rw [hadd, hadd]
  exact Nat.add_lt_add_left (hs hij) _

end Quartic.WeightedInitialImage
