import FsFltz.Toric
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Supporting faces of the lattice polytope

The vertex-support encoding in `IsPolytopeFace` is related here to the actual
supporting slices and to Mathlib's `IsExposed` predicate. This supplies the
face-representation foundation of `geoemtric-part-fsf.tex`, `sec:data`, lines
61–64, and `sec:lean`, lines 778–782. The fan axioms and the geometric target
`thm:target` remain separate pending results.
-/

noncomputable section

namespace FsFltz

variable {n : ℕ}

/-- A supporting bound on the generators holds on their entire convex hull. -/
theorem latticePolytope_le (V : Finset (Lattice n)) (ℓ : RealSpace n →ₗ[ℝ] ℝ)
    (a : ℝ) (h : ∀ v ∈ V, ℓ (latticeReal v) ≤ a) :
    ∀ x ∈ latticePolytope V, ℓ x ≤ a := by
  apply convexHull_min ?_ (convex_halfSpace_le ℓ.isLinear a)
  rintro _ ⟨v, hv, rfl⟩
  exact h v hv

/-- The convex hull of the supporting vertex set is literally the supporting
hyperplane slice of the full polytope, including empty and full faces. -/
theorem latticePolytope_eq_supporting_slice (V s : Finset (Lattice n))
    (ℓ : RealSpace n →ₗ[ℝ] ℝ) (a : ℝ) (hs : s ⊆ V)
    (hle : ∀ v ∈ V, ℓ (latticeReal v) ≤ a)
    (heq : ∀ v ∈ V, v ∈ s ↔ ℓ (latticeReal v) = a) :
    latticePolytope s = {x ∈ latticePolytope V | ℓ x = a} := by
  apply Set.Subset.antisymm
  · apply convexHull_min ?_ ((convex_convexHull ℝ _).inter (convex_hyperplane ℓ.isLinear a))
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨subset_convexHull ℝ _ ⟨v, hs hv, rfl⟩, (heq v (hs hv)).mp hv⟩
  · let C : Set (RealSpace n) :=
      {x | ℓ x ≤ a ∧ (ℓ x = a → x ∈ latticePolytope s)}
    have hgen : latticeReal '' (V : Set (Lattice n)) ⊆ C := by
      rintro _ ⟨v, hv, rfl⟩
      exact ⟨hle v hv, fun he => subset_convexHull ℝ _ ⟨v, (heq v hv).mpr he, rfl⟩⟩
    have hconv : Convex ℝ C := by
      intro x hx y hy p q hp hq hpq
      change ℓ x ≤ a ∧ (ℓ x = a → x ∈ latticePolytope s) at hx
      change ℓ y ≤ a ∧ (ℓ y = a → y ∈ latticePolytope s) at hy
      change ℓ (p • x + q • y) ≤ a ∧
        (ℓ (p • x + q • y) = a → p • x + q • y ∈ latticePolytope s)
      simp only [map_add, map_smul, smul_eq_mul]
      have hsum : p * a + q * a = a := by rw [← add_mul, hpq, one_mul]
      refine ⟨by nlinarith [mul_nonneg hp (sub_nonneg.mpr hx.1),
        mul_nonneg hq (sub_nonneg.mpr hy.1)], ?_⟩
      intro h
      rcases eq_or_lt_of_le hp with hp0 | hp0
      · have hq1 : q = 1 := by linarith
        subst p
        subst q
        simpa using hy.2 (by simpa using h)
      rcases eq_or_lt_of_le hq with hq0 | hq0
      · have hp1 : p = 1 := by linarith
        subst q
        subst p
        simpa using hx.2 (by simpa using h)
      have hx_eq : ℓ x = a := by
        have hgap : p * (a - ℓ x) = 0 := by
          nlinarith [mul_nonneg hp (sub_nonneg.mpr hx.1),
            mul_nonneg hq (sub_nonneg.mpr hy.1)]
        have := (mul_eq_zero.mp hgap).resolve_left (ne_of_gt hp0)
        linarith
      have hy_eq : ℓ y = a := by
        have hgap : q * (a - ℓ y) = 0 := by
          nlinarith [mul_nonneg hp (sub_nonneg.mpr hx.1),
            mul_nonneg hq (sub_nonneg.mpr hy.1)]
        have := (mul_eq_zero.mp hgap).resolve_left (ne_of_gt hq0)
        linarith
      exact (convex_convexHull ℝ _) (hx.2 hx_eq) (hy.2 hy_eq) hp hq hpq
    intro x hx
    exact (convexHull_min hgen hconv hx.1).2 hx.2

/-- Every encoded face has a genuine supporting hyperplane presentation. -/
theorem IsPolytopeFace.eq_supporting_slice {V s : Finset (Lattice n)}
    (h : IsPolytopeFace V s) :
    ∃ ℓ : RealSpace n →ₗ[ℝ] ℝ, ∃ a : ℝ,
      (∀ x ∈ latticePolytope V, ℓ x ≤ a) ∧
      latticePolytope s = {x ∈ latticePolytope V | ℓ x = a} := by
  obtain ⟨hs, ℓ, a, hle, heq⟩ := h
  exact ⟨ℓ, a, latticePolytope_le V ℓ a hle,
    latticePolytope_eq_supporting_slice V s ℓ a hs hle heq⟩

/-- An encoded face is an exposed subset in Mathlib's continuous-functional
sense. Continuity follows from the finite-dimensional coordinate space. -/
theorem IsPolytopeFace.isExposed {V s : Finset (Lattice n)}
    (h : IsPolytopeFace V s) :
    IsExposed ℝ (latticePolytope V) (latticePolytope s) := by
  obtain ⟨ℓ, a, hle, hs⟩ := h.eq_supporting_slice
  intro hne
  obtain ⟨z, hz⟩ := hne
  rw [hs] at hz
  refine ⟨LinearMap.toContinuousLinearMap ℓ, ?_⟩
  rw [hs]
  ext x
  constructor
  · rintro ⟨hx, heq⟩
    exact ⟨hx, fun y hy => by change ℓ y ≤ ℓ x; rw [heq]; exact hle y hy⟩
  · rintro ⟨hx, hmax⟩
    refine ⟨hx, le_antisymm (hle x hx) ?_⟩
    have hzx := hmax z hz.1
    change ℓ z ≤ ℓ x at hzx
    simpa [hz.2] using hzx

/-- The empty face is represented by the zero functional at a strictly
positive level. -/
theorem isPolytopeFace_empty (V : Finset (Lattice n)) : IsPolytopeFace V ∅ := by
  refine ⟨Finset.empty_subset V, 0, 1, ?_, ?_⟩ <;> simp

/-- The whole polytope is a face, represented by the zero functional. -/
theorem isPolytopeFace_self (V : Finset (Lattice n)) : IsPolytopeFace V V := by
  refine ⟨Finset.Subset.refl V, 0, 0, ?_, ?_⟩ <;> simp

/-- Extract the actual input vertices belonging to a geometric subset. -/
def faceVertexSupport (V : Finset (Lattice n)) (F : Set (RealSpace n)) :
    Finset (Lattice n) := by
  classical
  exact V.filter fun v => latticeReal v ∈ F

@[simp]
theorem mem_faceVertexSupport {V : Finset (Lattice n)} {F : Set (RealSpace n)}
    {v : Lattice n} : v ∈ faceVertexSupport V F ↔ v ∈ V ∧ latticeReal v ∈ F := by
  classical
  simp [faceVertexSupport]

theorem faceVertexSupport_subset (V : Finset (Lattice n)) (F : Set (RealSpace n)) :
    faceVertexSupport V F ⊆ V := by
  intro v hv
  exact (mem_faceVertexSupport.mp hv).1

@[simp]
theorem faceVertexSupport_empty (V : Finset (Lattice n)) :
    faceVertexSupport V ∅ = ∅ := by
  ext v
  simp

/-- A geometric exposed face yields its supporting vertex set without any
extra hypothesis on `ToricInput` or on the face. -/
theorem isPolytopeFace_faceVertexSupport {V : Finset (Lattice n)}
    {F : Set (RealSpace n)} (hF : IsExposed ℝ (latticePolytope V) F) :
    IsPolytopeFace V (faceVertexSupport V F) := by
  rcases F.eq_empty_or_nonempty with rfl | hne
  · simpa using isPolytopeFace_empty V
  obtain ⟨ℓ, he⟩ := hF hne
  obtain ⟨z, hz⟩ := hne
  have hz' : z ∈ latticePolytope V ∧ ∀ y ∈ latticePolytope V, ℓ y ≤ ℓ z := by
    rwa [he] at hz
  refine ⟨faceVertexSupport_subset V F, ℓ.toLinearMap, ℓ z, ?_, ?_⟩
  · intro v hv
    exact hz'.2 (latticeReal v) (subset_convexHull ℝ _ ⟨v, hv, rfl⟩)
  · intro v hv
    rw [mem_faceVertexSupport]
    constructor
    · rintro ⟨_, hvF⟩
      rw [he] at hvF
      exact le_antisymm (hz'.2 _ hvF.1) (hvF.2 _ hz'.1)
    · intro hvEq
      refine ⟨hv, ?_⟩
      rw [he]
      refine ⟨subset_convexHull ℝ _ ⟨v, hv, rfl⟩, ?_⟩
      intro y hy
      change ℓ y ≤ ℓ (latticeReal v)
      rw [show ℓ (latticeReal v) = ℓ z from hvEq]
      exact hz'.2 y hy

/-- Every geometric exposed face is exactly the convex hull of the input
vertices that it contains. -/
theorem latticePolytope_faceVertexSupport {V : Finset (Lattice n)}
    {F : Set (RealSpace n)} (hF : IsExposed ℝ (latticePolytope V) F) :
    latticePolytope (faceVertexSupport V F) = F := by
  rcases F.eq_empty_or_nonempty with rfl | hne
  · simp [latticePolytope]
  obtain ⟨ℓ, he⟩ := hF hne
  obtain ⟨z, hz⟩ := hne
  have hz' : z ∈ latticePolytope V ∧ ∀ y ∈ latticePolytope V, ℓ y ≤ ℓ z := by
    rwa [he] at hz
  have hs := isPolytopeFace_faceVertexSupport hF
  have hle : ∀ v ∈ V, ℓ (latticeReal v) ≤ ℓ z :=
    fun v hv => hz'.2 _ (subset_convexHull ℝ _ ⟨v, hv, rfl⟩)
  have hmem : ∀ v ∈ V, v ∈ faceVertexSupport V F ↔ ℓ (latticeReal v) = ℓ z := by
    intro v hv
    rw [mem_faceVertexSupport]
    constructor
    · rintro ⟨_, hvF⟩
      rw [he] at hvF
      exact le_antisymm (hle v hv) (hvF.2 _ hz'.1)
    · intro hvEq
      refine ⟨hv, ?_⟩
      rw [he]
      exact ⟨subset_convexHull ℝ _ ⟨v, hv, rfl⟩, fun y hy => by
        rw [hvEq]; exact hz'.2 y hy⟩
  rw [latticePolytope_eq_supporting_slice V _ ℓ.toLinearMap (ℓ z) hs.1 hle hmem, he]
  ext x
  constructor
  · rintro ⟨hx, hxeq⟩
    change ℓ x = ℓ z at hxeq
    exact ⟨hx, fun y hy => by change ℓ y ≤ ℓ x; rw [hxeq]; exact hz'.2 y hy⟩
  · rintro ⟨hx, hmax⟩
    exact ⟨hx, le_antisymm (hz'.2 x hx) (hmax z hz'.1)⟩

/-- The finite supporting-vertex representation and the canonical geometric
exposed-face representation describe exactly the same family of subsets. -/
theorem isExposed_iff_exists_isPolytopeFace (V : Finset (Lattice n))
    (F : Set (RealSpace n)) :
    IsExposed ℝ (latticePolytope V) F ↔
      ∃ s, IsPolytopeFace V s ∧ latticePolytope s = F := by
  constructor
  · intro hF
    exact ⟨faceVertexSupport V F, isPolytopeFace_faceVertexSupport hF,
      latticePolytope_faceVertexSupport hF⟩
  · rintro ⟨s, hs, rfl⟩
    exact hs.isExposed

/-- A supporting face contains precisely its supporting input vertices. -/
theorem IsPolytopeFace.mem_latticePolytope_iff {V s : Finset (Lattice n)}
    (h : IsPolytopeFace V s) {v : Lattice n} (hv : v ∈ V) :
    latticeReal v ∈ latticePolytope s ↔ v ∈ s := by
  obtain ⟨hs, ℓ, a, hle, hmem⟩ := h
  rw [latticePolytope_eq_supporting_slice V s ℓ a hs hle hmem]
  constructor
  · intro hx
    exact (hmem v hv).mpr hx.2
  · intro hvs
    exact ⟨subset_convexHull ℝ _ ⟨v, hv, rfl⟩, (hmem v hv).mp hvs⟩

/-- Vertex-support extraction is inverse to taking the convex hull of an
encoded face. -/
theorem IsPolytopeFace.faceVertexSupport_eq {V s : Finset (Lattice n)}
    (h : IsPolytopeFace V s) : faceVertexSupport V (latticePolytope s) = s := by
  ext v
  rw [mem_faceVertexSupport]
  constructor
  · rintro ⟨hv, hx⟩
    exact (h.mem_latticePolytope_iff hv).mp hx
  · intro hv
    exact ⟨h.1 hv, (h.mem_latticePolytope_iff (h.1 hv)).mpr hv⟩

/-- Taking the convex hull preserves inclusion of vertex sets. -/
theorem latticePolytope_mono {s t : Finset (Lattice n)} (hst : s ⊆ t) :
    latticePolytope s ⊆ latticePolytope t := by
  apply convexHull_mono
  rintro _ ⟨v, hv, rfl⟩
  exact ⟨v, hst hv, rfl⟩

/-- Inclusion of encoded faces is exactly inclusion of their geometric
subsets. Only the containing set needs to be a supporting face. -/
theorem IsPolytopeFace.latticePolytope_subset_iff {V s t : Finset (Lattice n)}
    (ht : IsPolytopeFace V t) (hs : s ⊆ V) :
    latticePolytope s ⊆ latticePolytope t ↔ s ⊆ t := by
  constructor
  · intro hst v hv
    exact (ht.mem_latticePolytope_iff (hs hv)).mp
      (hst (subset_convexHull ℝ _ ⟨v, hv, rfl⟩))
  · exact latticePolytope_mono

/-- Encoded faces have unique geometric convex-hull presentations. -/
theorem IsPolytopeFace.latticePolytope_eq_iff {V s t : Finset (Lattice n)}
    (hs : IsPolytopeFace V s) (ht : IsPolytopeFace V t) :
    latticePolytope s = latticePolytope t ↔ s = t := by
  constructor
  · intro he
    apply Finset.Subset.antisymm
    · exact (ht.latticePolytope_subset_iff hs.1).mp he.subset
    · exact (hs.latticePolytope_subset_iff ht.1).mp he.symm.subset
  · rintro rfl
    rfl

/-- Nonemptiness is preserved and reflected by the geometric convex hull. -/
theorem latticePolytope_nonempty_iff (s : Finset (Lattice n)) :
    (latticePolytope s).Nonempty ↔ s.Nonempty := by
  simp only [latticePolytope, convexHull_nonempty_iff, Set.image_nonempty,
    Finset.coe_nonempty]

/-- For an encoded face, maximality among proper vertex supports is exactly
maximality among proper geometric exposed faces. This does not identify
arbitrary convex extreme faces with exposed faces. -/
theorem IsPolytopeFace.isPolytopeFacet_iff {V s : Finset (Lattice n)}
    (hs : IsPolytopeFace V s) :
    IsPolytopeFacet V s ↔
      (latticePolytope s).Nonempty ∧ latticePolytope s ≠ latticePolytope V ∧
      ∀ F, IsExposed ℝ (latticePolytope V) F → F ≠ latticePolytope V →
        latticePolytope s ⊆ F → F = latticePolytope s := by
  have hproper : latticePolytope s ≠ latticePolytope V ↔ s ≠ V :=
    not_congr (hs.latticePolytope_eq_iff (isPolytopeFace_self V))
  constructor
  · rintro ⟨_, hne, hpr, hmax⟩
    refine ⟨(latticePolytope_nonempty_iff s).mpr hne, hproper.mpr hpr, ?_⟩
    intro F hF hFp hsub
    let t := faceVertexSupport V F
    have ht : IsPolytopeFace V t := isPolytopeFace_faceVertexSupport hF
    have htF : latticePolytope t = F := latticePolytope_faceVertexSupport hF
    have htpr : t ≠ V := by
      intro he
      apply hFp
      rw [← htF, he]
    have hst : s ⊆ t := (ht.latticePolytope_subset_iff hs.1).mp (htF ▸ hsub)
    have he := hmax t ht htpr hst
    rw [← htF, he]
  · rintro ⟨hne, hpr, hmax⟩
    refine ⟨hs, (latticePolytope_nonempty_iff s).mp hne, hproper.mp hpr, ?_⟩
    intro t ht htp hst
    have htp' : latticePolytope t ≠ latticePolytope V :=
      (not_congr (ht.latticePolytope_eq_iff (isPolytopeFace_self V))).mpr htp
    exact (ht.latticePolytope_eq_iff hs).mp
      (hmax (latticePolytope t) ht.isExposed htp' (latticePolytope_mono hst))

/-- With the input's exact-vertex hypothesis, the extreme points of every
encoded face are precisely its encoded lattice vertices. -/
theorem ToricInput.extremePoints_face (I : ToricInput n)
    {s : Finset (Lattice n)} (hs : IsPolytopeFace I.vertices s) :
    (latticePolytope s).extremePoints ℝ = latticeReal '' (s : Set (Lattice n)) := by
  rw [hs.isExposed.isExtreme.extremePoints_eq, ← I.vertices_exact]
  apply Set.Subset.antisymm
  · rintro _ ⟨hx, v, hv, rfl⟩
    exact ⟨v, (hs.mem_latticePolytope_iff hv).mp hx, rfl⟩
  · rintro _ ⟨v, hv, rfl⟩
    exact ⟨(hs.mem_latticePolytope_iff (hs.1 hv)).mpr hv, ⟨v, hs.1 hv, rfl⟩⟩

/-- Scalar extension of the based lattice loses no lattice vectors. -/
theorem latticeReal_injective : Function.Injective (latticeReal : Lattice n → RealSpace n) := by
  intro v w he
  funext j
  exact Int.cast_injective (congrFun he j : (v j : ℝ) = (w j : ℝ))

/-- An actual input vertex belongs to the hull of a vertex subset exactly
when it belongs to that subset. The exact-vertex hypothesis is essential
here because the subset is not assumed to be a supporting face. -/
theorem ToricInput.mem_latticePolytope_iff (I : ToricInput n)
    {s : Finset (Lattice n)} (hs : s ⊆ I.vertices) {v : Lattice n}
    (hv : v ∈ I.vertices) : latticeReal v ∈ latticePolytope s ↔ v ∈ s := by
  constructor
  · intro hx
    have hvext : latticeReal v ∈ (latticePolytope I.vertices).extremePoints ℝ := by
      rw [← I.vertices_exact]
      exact ⟨v, hv, rfl⟩
    have hxext : latticeReal v ∈ (latticePolytope s).extremePoints ℝ :=
      inter_extremePoints_subset_extremePoints_of_subset (latticePolytope_mono hs) ⟨hx, hvext⟩
    obtain ⟨w, hw, hweq⟩ := extremePoints_convexHull_subset hxext
    exact latticeReal_injective hweq ▸ hw
  · intro hvs
    exact subset_convexHull ℝ _ ⟨v, hvs, rfl⟩

/-- Exact input vertices are recovered from the hull of any input subset. -/
theorem ToricInput.faceVertexSupport_latticePolytope (I : ToricInput n)
    {s : Finset (Lattice n)} (hs : s ⊆ I.vertices) :
    faceVertexSupport I.vertices (latticePolytope s) = s := by
  ext v
  rw [mem_faceVertexSupport]
  constructor
  · rintro ⟨hv, hx⟩
    exact (I.mem_latticePolytope_iff hs hv).mp hx
  · intro hv
    exact ⟨hs hv, (I.mem_latticePolytope_iff hs (hs hv)).mpr hv⟩

/-- For subsets of the actual input vertices, the encoded face condition is
equivalent directly to the native exposed-face condition on their hulls. -/
theorem ToricInput.isPolytopeFace_iff_isExposed (I : ToricInput n)
    {s : Finset (Lattice n)} (hs : s ⊆ I.vertices) :
    IsPolytopeFace I.vertices s ↔
      IsExposed ℝ (latticePolytope I.vertices) (latticePolytope s) := by
  constructor
  · exact IsPolytopeFace.isExposed
  · intro hF
    have hface := isPolytopeFace_faceVertexSupport hF
    rwa [I.faceVertexSupport_latticePolytope hs] at hface

/-- The input facet condition agrees with maximal proper nonempty exposed
faces of the actual polytope, for every subset of its actual vertices. -/
theorem ToricInput.isPolytopeFacet_iff (I : ToricInput n)
    {s : Finset (Lattice n)} (hs : s ⊆ I.vertices) :
    IsPolytopeFacet I.vertices s ↔
      IsExposed ℝ (latticePolytope I.vertices) (latticePolytope s) ∧
      (latticePolytope s).Nonempty ∧
      latticePolytope s ≠ latticePolytope I.vertices ∧
      ∀ F, IsExposed ℝ (latticePolytope I.vertices) F →
        F ≠ latticePolytope I.vertices → latticePolytope s ⊆ F →
        F = latticePolytope s := by
  constructor
  · intro hfacet
    exact ⟨hfacet.1.isExposed, hfacet.1.isPolytopeFacet_iff.mp hfacet⟩
  · rintro ⟨hF, hgeom⟩
    exact ((I.isPolytopeFace_iff_isExposed hs).mpr hF).isPolytopeFacet_iff.mpr hgeom

/-- The lattice-basis condition applies to the actual vertices of every
maximal proper nonempty exposed face. This is the geometric consumer of the
support-extraction and facet-correspondence lemmas. -/
theorem ToricInput.facet_basis_of_isExposed (I : ToricInput n)
    {F : Set (RealSpace n)} (hF : IsExposed ℝ (latticePolytope I.vertices) F)
    (hne : F.Nonempty) (hproper : F ≠ latticePolytope I.vertices)
    (hmax : ∀ G, IsExposed ℝ (latticePolytope I.vertices) G →
      G ≠ latticePolytope I.vertices → F ⊆ G → G = F) :
    ∃ b : Module.Basis {v : Lattice n // v ∈ faceVertexSupport I.vertices F}
      ℤ (Lattice n), ∀ v, b v = v.val := by
  apply I.facet_basis
  have hs := isPolytopeFace_faceVertexSupport hF
  apply hs.isPolytopeFacet_iff.mpr
  simpa only [latticePolytope_faceVertexSupport hF] using And.intro hne (And.intro hproper hmax)

end FsFltz
