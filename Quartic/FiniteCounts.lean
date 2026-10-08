import Quartic.Counts

/-!
# Kernel-checked finite dimension counts

This file checks integer signs and structural inequalities only. The endpoint
table is generated data, whose assertions below are independently checked by
Lean's kernel. It contains no matrix rank certificates and proves no geometric
transfer or generic maximal-rank statement. `decide` is used; `native_decide`
is deliberately not used.
-/

namespace Quartic.FiniteCounts

open Quartic.Counts

/-- Efficient integer formula for the quadratic dimension. -/
def quadratics (n : ℕ) : ℤ := (n : ℤ) * ((n : ℤ) + 1) / 2

/-- Efficient integer formula for the cubic dimension. -/
def cubics (n : ℕ) : ℤ := (n : ℤ) * ((n : ℤ) + 1) * ((n : ℤ) + 2) / 6

/-- Efficient integer formula for the quartic dimension. -/
def quartics (n : ℕ) : ℤ :=
  (n : ℤ) * ((n : ℤ) + 1) * ((n : ℤ) + 2) * ((n : ℤ) + 3) / 24

/-- Efficient integer formula for an unordered pair count. -/
def pairs (r : ℕ) : ℤ := (r : ℤ) * ((r : ℤ) - 1) / 2

theorem quadratics_eq_b2 (n : ℕ) : quadratics n = b2 n := by
  unfold quadratics
  rw [← b2_scaled n]
  omega

theorem cubics_eq_b3 (n : ℕ) : cubics n = b3 n := by
  unfold cubics
  rw [← b3_scaled n]
  omega

theorem quartics_eq_b4 (n : ℕ) : quartics n = b4 n := by
  unfold quartics
  rw [← b4_scaled n]
  omega

theorem pairs_eq_choose (r : ℕ) : pairs r = (Nat.choose r 2 : ℤ) := by
  unfold pairs
  rw [← choose_two_scaled r]
  omega

/-- A computational form of the already-defined Euler difference. -/
def euler (n r : ℕ) : ℤ := quartics n - (r : ℤ) * quadratics n + pairs r

theorem euler_eq_chi (n r : ℕ) : euler n r = chi n r := by
  simp only [euler, chi, quartics_eq_b4, quadratics_eq_b2, pairs_eq_choose]

/-- Adjacent lower/upper endpoint data, indexed by `n = 0, …, 322`. -/
def endpointData : Array (ℕ × ℕ) := #[
  (0, 0), (1, 1), (2, 2), (3, 3), (4, 5), (5, 6), (7, 7), (8, 9),
  (10, 11), (12, 13), (14, 15), (17, 18), (19, 20), (22, 23), (25, 26), (28, 29),
  (32, 33), (35, 36), (39, 40), (43, 44), (47, 48), (51, 52), (56, 57), (60, 61),
  (65, 66), (70, 71), (75, 76), (81, 82), (86, 87), (92, 93), (98, 99), (104, 105),
  (110, 111), (117, 118), (123, 124), (130, 131), (137, 138), (144, 145), (152, 153), (159, 160),
  (167, 168), (175, 176), (183, 184), (191, 192), (200, 201), (209, 210), (217, 218), (226, 227),
  (236, 237), (245, 246), (255, 256), (264, 265), (274, 275), (284, 285), (295, 296), (305, 306),
  (316, 317), (327, 328), (338, 339), (349, 350), (361, 362), (372, 373), (384, 385), (396, 397),
  (408, 409), (420, 421), (433, 434), (446, 447), (458, 459), (472, 473), (485, 486), (498, 499),
  (512, 513), (526, 527), (540, 541), (554, 555), (568, 569), (583, 584), (597, 598), (612, 613),
  (627, 628), (643, 644), (658, 659), (674, 675), (690, 691), (706, 707), (722, 723), (738, 739),
  (755, 756), (771, 772), (788, 789), (806, 806), (823, 824), (840, 841), (858, 859), (876, 877),
  (894, 895), (912, 913), (930, 931), (949, 950), (968, 969), (987, 988), (1006, 1007), (1025, 1026),
  (1045, 1046), (1064, 1065), (1084, 1085), (1104, 1105), (1124, 1125), (1145, 1146), (1165, 1166), (1186, 1187),
  (1207, 1208), (1228, 1229), (1250, 1251), (1271, 1272), (1293, 1294), (1315, 1316), (1337, 1338), (1359, 1360),
  (1381, 1382), (1404, 1405), (1427, 1428), (1450, 1451), (1473, 1474), (1496, 1497), (1520, 1521), (1544, 1545),
  (1567, 1568), (1592, 1593), (1616, 1617), (1640, 1641), (1665, 1666), (1690, 1691), (1715, 1716), (1740, 1741),
  (1765, 1766), (1791, 1792), (1817, 1818), (1842, 1843), (1869, 1870), (1895, 1896), (1921, 1922), (1948, 1949),
  (1975, 1976), (2002, 2003), (2029, 2030), (2056, 2057), (2084, 2085), (2112, 2113), (2140, 2141), (2168, 2169),
  (2196, 2197), (2225, 2226), (2253, 2254), (2282, 2283), (2311, 2312), (2340, 2341), (2370, 2371), (2399, 2400),
  (2429, 2430), (2459, 2460), (2489, 2490), (2519, 2520), (2550, 2551), (2581, 2582), (2612, 2613), (2643, 2644),
  (2674, 2675), (2705, 2706), (2737, 2738), (2769, 2770), (2801, 2802), (2833, 2834), (2865, 2866), (2898, 2899),
  (2930, 2931), (2963, 2964), (2996, 2997), (3030, 3031), (3063, 3064), (3097, 3098), (3130, 3131), (3164, 3165),
  (3199, 3200), (3233, 3234), (3267, 3268), (3302, 3303), (3337, 3338), (3372, 3373), (3407, 3408), (3443, 3444),
  (3479, 3480), (3514, 3515), (3550, 3551), (3587, 3588), (3623, 3624), (3659, 3660), (3696, 3697), (3733, 3734),
  (3770, 3771), (3808, 3809), (3845, 3846), (3883, 3884), (3921, 3922), (3959, 3960), (3997, 3998), (4035, 4036),
  (4074, 4075), (4113, 4114), (4151, 4152), (4191, 4192), (4230, 4231), (4269, 4270), (4309, 4310), (4349, 4350),
  (4389, 4390), (4429, 4430), (4470, 4471), (4510, 4511), (4551, 4552), (4592, 4593), (4633, 4634), (4674, 4675),
  (4716, 4717), (4758, 4759), (4800, 4801), (4842, 4843), (4884, 4885), (4926, 4927), (4969, 4970), (5012, 5013),
  (5055, 5056), (5098, 5099), (5141, 5142), (5185, 5186), (5228, 5229), (5272, 5273), (5316, 5317), (5361, 5362),
  (5405, 5406), (5450, 5451), (5495, 5496), (5540, 5541), (5585, 5586), (5630, 5631), (5676, 5677), (5721, 5722),
  (5767, 5768), (5813, 5814), (5860, 5861), (5906, 5907), (5953, 5954), (6000, 6001), (6047, 6048), (6094, 6095),
  (6141, 6142), (6189, 6190), (6237, 6238), (6285, 6286), (6333, 6334), (6381, 6382), (6429, 6430), (6478, 6479),
  (6527, 6528), (6576, 6577), (6625, 6626), (6675, 6676), (6724, 6725), (6774, 6775), (6824, 6825), (6874, 6875),
  (6924, 6925), (6975, 6976), (7026, 7027), (7076, 7077), (7127, 7128), (7179, 7180), (7230, 7231), (7282, 7283),
  (7334, 7335), (7386, 7387), (7438, 7439), (7490, 7491), (7543, 7544), (7595, 7596), (7648, 7649), (7701, 7702),
  (7754, 7755), (7808, 7809), (7862, 7863), (7915, 7916), (7969, 7970), (8023, 8024), (8078, 8079), (8132, 8133),
  (8187, 8188), (8242, 8243), (8297, 8298), (8352, 8353), (8408, 8409), (8464, 8465), (8519, 8520), (8575, 8576),
  (8632, 8633), (8688, 8689), (8744, 8745), (8801, 8802), (8858, 8859), (8915, 8916), (8973, 8974), (9030, 9031),
  (9088, 9089), (9146, 9147), (9204, 9205), (9262, 9263), (9320, 9321), (9379, 9380), (9438, 9439), (9496, 9497),
  (9556, 9557), (9615, 9616), (9674, 9675)
]

def endpointPair (n : ℕ) : ℕ × ℕ := endpointData[n]?.getD (0, 0)
def lowerEndpoint (n : ℕ) : ℕ := (endpointPair n).1
def upperEndpoint (n : ℕ) : ℕ := (endpointPair n).2

/-- Sign and adjacency conditions identifying the two integer endpoints on the
strictly decreasing part of the Euler polynomial. -/
def EndpointValid (n lower upper : ℕ) : Prop :=
  lower ≤ upper ∧ upper ≤ lower + 1 ∧
  (upper : ℤ) ≤ quadratics n ∧
  0 ≤ euler n lower ∧ euler n upper ≤ 0 ∧
  (lower = upper ↔ euler n lower = 0) ∧
  (lower < upper → euler n upper < 0 ∧ 0 < euler n lower)

instance (n lower upper : ℕ) : Decidable (EndpointValid n lower upper) := by
  unfold EndpointValid
  infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- All 323 records, including every base dimension and every finite transfer
child/parent dimension, satisfy the defining endpoint sign tests. -/
theorem endpoint_table_verified : ∀ n : Fin 323,
    EndpointValid n (lowerEndpoint n) (upperEndpoint n) := by
  decide

/-- Endpoint certification expressed with the original `Nat.choose` Euler count. -/
theorem endpoint_signs (n : ℕ) (hn : n ≤ 322) :
    0 ≤ chi n (lowerEndpoint n) ∧ chi n (upperEndpoint n) ≤ 0 ∧
    upperEndpoint n ≤ lowerEndpoint n + 1 := by
  have h := endpoint_table_verified ⟨n, by omega⟩
  change EndpointValid n (lowerEndpoint n) (upperEndpoint n) at h
  rcases h with ⟨_, hadj, _, hlo, hup, _⟩
  simpa only [euler_eq_chi] using And.intro hlo (And.intro hup hadj)

/-- The finite base range receives numerical endpoint certificates. This is not
an assertion about ranks of the base-case multiplication matrices. -/
theorem base_endpoint_signs (n : ℕ) (hn : n ≤ 30) :
    0 ≤ chi n (lowerEndpoint n) ∧ chi n (upperEndpoint n) ≤ 0 := by
  exact ⟨(endpoint_signs n (by omega)).1, (endpoint_signs n (by omega)).2.1⟩

def parentCount (m : ℕ) (upper : Bool) : ℕ :=
  if upper then upperEndpoint (m + 3) else lowerEndpoint (m + 3)

def mixedCount (m : ℕ) (upper : Bool) : ℕ :=
  parentCount m upper - upperEndpoint m - 4

/-- The finite structural assertions in the manuscript, plus the sign assertions
on `j`, `H`, and the endpoint defect. Every operation uses integer arithmetic
except explicitly nonnegative indexing and the truncated free-variable count. -/
def StructuralValid (m q c : ℕ) : Prop :=
  let α := quadratics m - (q : ℤ)
  let β := cubics m - (m : ℤ) * (q : ℤ)
  let h := 3 * (m : ℤ) * (c : ℤ) - 2 * α - pairs c
  let outer := 3 * β - (c : ℤ) * α
  let δ := -euler m q
  let w₀ := m - 2 * c
  4 ≤ c ∧ c ≤ m ∧
  (m : ℤ) * (q : ℤ) ≤ cubics m ∧
  3 ≤ α - quadratics c ∧
  (c : ℤ) * (w₀ : ℤ) + quadratics w₀ ≤ (q : ℤ) ∧
  0 < outer ∧ 0 ≤ h ∧ 0 ≤ δ ∧ δ ≤ α

instance (m q c : ℕ) : Decidable (StructuralValid m q c) := by
  unfold StructuralValid
  infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Both parent endpoints satisfy all structural count inequalities for every
child dimension `28 ≤ m ≤ 319`: 584 integer configurations. -/
theorem structural_table_verified : ∀ i : Fin 292, ∀ upper : Bool,
    let m := (i : ℕ) + 28
    parentCount m upper = upperEndpoint m + mixedCount m upper + 4 ∧
    StructuralValid m (upperEndpoint m) (mixedCount m upper) := by
  decide

/-- Readable bounded form of the finite structural result. -/
theorem structural_counts (m : ℕ) (hmlo : 28 ≤ m) (hmhi : m ≤ 319)
    (upper : Bool) :
    parentCount m upper = upperEndpoint m + mixedCount m upper + 4 ∧
    StructuralValid m (upperEndpoint m) (mixedCount m upper) := by
  have h := structural_table_verified ⟨m - 28, by omega⟩ upper
  have hm : m - 28 + 28 = m := by omega
  simpa only [hm] using h

/-- The signs in the finite certificate use the original dimension definitions. -/
theorem structural_dimension_signs (m : ℕ) (hmlo : 28 ≤ m) (hmhi : m ≤ 319)
    (upper : Bool) :
    0 < j m (upperEndpoint m) (mixedCount m upper) ∧
    0 ≤ H m (upperEndpoint m) (mixedCount m upper) ∧
    0 ≤ delta m (upperEndpoint m) ∧
    delta m (upperEndpoint m) ≤ alpha m (upperEndpoint m) := by
  have h := (structural_counts m hmlo hmhi upper).2
  simp only [StructuralValid, quadratics_eq_b2, cubics_eq_b3, pairs_eq_choose,
    euler_eq_chi] at h
  exact ⟨h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2⟩

/-- Structural count inequalities stated using the original binomial dimensions. -/
theorem structural_binomial_counts (m : ℕ) (hmlo : 28 ≤ m) (hmhi : m ≤ 319)
    (upper : Bool) :
    let q := upperEndpoint m
    let c := mixedCount m upper
    let w₀ := m - 2 * c
    4 ≤ c ∧ c ≤ m ∧
    (m : ℤ) * (q : ℤ) ≤ b3 m ∧
    3 ≤ alpha m q - b2 c ∧
    (c : ℤ) * (w₀ : ℤ) + b2 w₀ ≤ (q : ℤ) := by
  have h := (structural_counts m hmlo hmhi upper).2
  simp only [StructuralValid, quadratics_eq_b2, cubics_eq_b3,
    pairs_eq_choose, euler_eq_chi] at h
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩

end Quartic.FiniteCounts
