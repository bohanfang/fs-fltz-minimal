import FsFltz.ToricIntrinsicFaces
import FsFltz.ToricFanCompleteness

/-!
# Intrinsic faces of the input polytope

Source: `geoemtric-part-fsf.tex`, `sec:data`, lines 61–66, and `sec:lean`,
lines 778–782. In the pinned Mathlib an intrinsic convex face is expressed
by `Convex ℝ F` and `IsExtreme ℝ Q F`. Recovering its vertices and supporting
their barycenter places it in a proper exposed face; the input facet-basis
condition then exposes every subset of those vertices.

No additional face/exposure assumption is added to `ToricInput`. These are
input-definition foundations, separate from the target `thm:target`.
-/

noncomputable section

namespace FsFltz

open scoped BigOperators

variable {n : ℕ}

/-- A convex intrinsic face of a finite hull is exactly the hull of the
generators it contains. The reverse inclusion uses intrinsic extremality
on positive two-term combinations, rather than an exposed-face premise. -/
theorem latticePolytope_faceVertexSupport_of_convex_isExtreme
    {V : Finset (Lattice n)} {F : Set (RealSpace n)}
    (hconv : Convex ℝ F) (hext : IsExtreme ℝ (latticePolytope V) F) :
    latticePolytope (faceVertexSupport V F) = F := by
  apply Set.Subset.antisymm
  · apply convexHull_min ?_ hconv
    rintro _ ⟨v, hv, rfl⟩
    exact (mem_faceVertexSupport.mp hv).2
  · let C : Set (RealSpace n) :=
      {x | x ∈ latticePolytope V ∧ (x ∈ F → x ∈ latticePolytope (faceVertexSupport V F))}
    have hgen : latticeReal '' (V : Set (Lattice n)) ⊆ C := by
      rintro _ ⟨v, hv, rfl⟩
      refine ⟨subset_convexHull ℝ _ ⟨v, hv, rfl⟩, ?_⟩
      intro hvF
      exact subset_convexHull ℝ _ ⟨v, mem_faceVertexSupport.mpr ⟨hv, hvF⟩, rfl⟩
    have hC : Convex ℝ C := by
      intro x hx y hy p q hp hq hpq
      refine ⟨(convex_convexHull ℝ _) hx.1 hy.1 hp hq hpq, ?_⟩
      intro hzF
      rcases eq_or_lt_of_le hp with rfl | hp
      · have hq : q = 1 := by linarith
        subst q
        simpa using hy.2 (by simpa using hzF)
      rcases eq_or_lt_of_le hq with rfl | hq
      · have hp : p = 1 := by linarith
        subst p
        simpa using hx.2 (by simpa using hzF)
      have hzseg : p • x + q • y ∈ openSegment ℝ x y := ⟨p, q, hp, hq, hpq, rfl⟩
      exact (convex_convexHull ℝ _)
        (hx.2 (hext.left_mem_of_mem_openSegment hx.1 hy.1 hzF hzseg))
        (hy.2 (hext.right_mem_of_mem_openSegment hx.1 hy.1 hzF hzseg)) hp.le hq.le hpq
    intro x hx
    exact (convexHull_min hgen hC (hext.subset hx)).2 hx

/-- An intrinsic extreme subset containing an ambient interior point is
the whole set: extend the segment from any point slightly beyond the
interior point and apply the native open-segment face law. -/
theorem isExtreme_eq_of_mem_interior {Q F : Set (RealSpace n)}
    (hext : IsExtreme ℝ Q F) {x : RealSpace n}
    (hxF : x ∈ F) (hxQ : x ∈ interior Q) : F = Q := by
  apply Set.Subset.antisymm hext.subset
  intro y hy
  let f : ℝ → RealSpace n := fun t => x + t • (x - y)
  have hcont : ContinuousAt f 0 := by fun_prop
  have hnhds : f ⁻¹' Q ∈ nhds (0 : ℝ) :=
    hcont.preimage_mem_nhds (by simpa [f] using mem_interior_iff_mem_nhds.mp hxQ)
  obtain ⟨l, u, hlu, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hnhds
  let t : ℝ := u / 2
  have ht : 0 < t := half_pos hlu.2
  have hft : f t ∈ Q := hsub ⟨by dsimp [t]; linarith [hlu.1, hlu.2],
    by dsimp [t]; linarith [hlu.2]⟩
  have hden : 0 < 1 + t := by linarith
  have hseg : x ∈ openSegment ℝ y (f t) := by
    refine ⟨t / (1 + t), 1 / (1 + t), div_pos ht hden,
      div_pos zero_lt_one hden, ?_, ?_⟩
    · field_simp
      ring
    · ext j
      simp only [f, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      field_simp
      ring
  exact hext.left_mem_of_mem_openSegment hy hft hxF hseg

/-- If the uniform barycenter of a nonempty vertex subset lies in a
supporting face, all those vertices lie in the face. Positivity of every
barycentric weight rules out a strict supporting gap at any vertex. -/
theorem IsPolytopeFace.subset_of_barycenter_mem {V s t : Finset (Lattice n)}
    (ht : IsPolytopeFace V t) (hs : s.Nonempty) (hsV : s ⊆ V)
    (hx : (∑ v ∈ s, (s.card : ℝ)⁻¹ • latticeReal v) ∈ latticePolytope t) :
    s ⊆ t := by
  obtain ⟨htV, ℓ, a, hle, heq⟩ := ht
  have hcard : 0 < (s.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hs)
  have hweight : 0 < (s.card : ℝ)⁻¹ := inv_pos.mpr hcard
  have hweights : (∑ _v ∈ s, (s.card : ℝ)⁻¹) = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_inv_cancel₀ (ne_of_gt hcard)]
  rw [latticePolytope_eq_supporting_slice V t ℓ a htV hle heq] at hx
  have hxEq := hx.2
  simp only [map_sum, map_smul, smul_eq_mul] at hxEq
  have hgap : (∑ v ∈ s, (s.card : ℝ)⁻¹ * (a - ℓ (latticeReal v))) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [← Finset.sum_mul, hweights, one_mul, hxEq, sub_self]
  have hnonneg : ∀ v ∈ s, 0 ≤ (s.card : ℝ)⁻¹ * (a - ℓ (latticeReal v)) := by
    intro v hv
    exact mul_nonneg hweight.le (sub_nonneg.mpr (hle v (hsV hv)))
  intro v hv
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hgap v hv
  have hz' := (mul_eq_zero.mp hz).resolve_left (ne_of_gt hweight)
  exact (heq v (hsV hv)).mpr (sub_eq_zero.mp hz').symm

/-- Every intrinsic convex face of the actual input polytope is exposed.
For a proper nonempty face, its barycenter lies on the frontier; a supporting
face at that point contains all its vertices, and a containing integral
facet basis exposes the recovered subset. Empty and full faces are explicit. -/
theorem ToricInput.isExposed_of_convex_isExtreme (I : ToricInput n)
    {F : Set (RealSpace n)} (hconv : Convex ℝ F)
    (hext : IsExtreme ℝ (latticePolytope I.vertices) F) :
    IsExposed ℝ (latticePolytope I.vertices) F := by
  rcases F.eq_empty_or_nonempty with rfl | hne
  · exact isExposed_empty
  by_cases hfull : F = latticePolytope I.vertices
  · rw [hfull]
  let s := faceVertexSupport I.vertices F
  have hsHull : latticePolytope s = F :=
    latticePolytope_faceVertexSupport_of_convex_isExtreme hconv hext
  have hsne : s.Nonempty :=
    (latticePolytope_nonempty_iff s).mp (hsHull.symm ▸ hne)
  have hcard : 0 < (s.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hsne)
  let x : RealSpace n := ∑ v ∈ s, (s.card : ℝ)⁻¹ • latticeReal v
  have hxF : x ∈ F := by
    apply hconv.sum_mem (fun _ _ => (inv_pos.mpr hcard).le) ?_ ?_
    · rw [Finset.sum_const, nsmul_eq_mul, mul_inv_cancel₀ (ne_of_gt hcard)]
    · intro v hv
      exact (mem_faceVertexSupport.mp hv).2
  have hxFrontier : x ∈ frontier (latticePolytope I.vertices) := by
    refine ⟨subset_closure (hext.subset hxF), ?_⟩
    intro hxInt
    exact hfull (isExtreme_eq_of_mem_interior hext hxF hxInt)
  obtain ⟨G, hG, _, hGproper, hxG⟩ :=
    I.exists_proper_isExposed_of_mem_frontier hxFrontier
  let t := faceVertexSupport I.vertices G
  have htFace : IsPolytopeFace I.vertices t := isPolytopeFace_faceVertexSupport hG
  have htHull : latticePolytope t = G := latticePolytope_faceVertexSupport hG
  have htproper : t ≠ I.vertices := by
    intro ht
    apply hGproper
    rw [← htHull, ht]
  have hst : s ⊆ t := htFace.subset_of_barycenter_mem hsne
    (faceVertexSupport_subset I.vertices F) (htHull.symm ▸ hxG)
  have hsFace := I.isPolytopeFace_subset htFace htproper hst
  exact hsHull ▸ hsFace.isExposed

/-- On the actual input polytope, the native convex/extreme face notion
agrees with the supporting-functional face notion, without extra inputs. -/
theorem ToricInput.isExposed_iff_convex_isExtreme (I : ToricInput n)
    (F : Set (RealSpace n)) :
    IsExposed ℝ (latticePolytope I.vertices) F ↔
      Convex ℝ F ∧ IsExtreme ℝ (latticePolytope I.vertices) F := by
  constructor
  · intro hF
    exact ⟨hF.convex (convex_convexHull ℝ _), hF.isExtreme⟩
  · rintro ⟨hconv, hext⟩
    exact I.isExposed_of_convex_isExtreme hconv hext

/-- The finite support face predicate agrees with intrinsic convex faces
for every subset of the actual vertices of the source polytope. -/
theorem ToricInput.isPolytopeFace_iff_convex_isExtreme (I : ToricInput n)
    {s : Finset (Lattice n)} (hs : s ⊆ I.vertices) :
    IsPolytopeFace I.vertices s ↔ Convex ℝ (latticePolytope s) ∧
      IsExtreme ℝ (latticePolytope I.vertices) (latticePolytope s) := by
  rw [I.isPolytopeFace_iff_isExposed hs, I.isExposed_iff_convex_isExtreme]

/-- The input's integral facet basis is a basis of precisely the vertices
of every intrinsic maximal proper nonempty convex face. -/
theorem ToricInput.facet_basis_of_convex_isExtreme (I : ToricInput n)
    {F : Set (RealSpace n)} (hconv : Convex ℝ F)
    (hext : IsExtreme ℝ (latticePolytope I.vertices) F)
    (hne : F.Nonempty) (hproper : F ≠ latticePolytope I.vertices)
    (hmax : ∀ G, Convex ℝ G → IsExtreme ℝ (latticePolytope I.vertices) G →
      G ≠ latticePolytope I.vertices → F ⊆ G → G = F) :
    ∃ b : Module.Basis {v : Lattice n // v ∈ faceVertexSupport I.vertices F}
      ℤ (Lattice n), ∀ v, b v = v.val := by
  apply I.facet_basis_of_isExposed (I.isExposed_of_convex_isExtreme hconv hext) hne hproper
  intro G hG hGproper hFG
  exact hmax G (hG.convex (convex_convexHull ℝ _)) hG.isExtreme hGproper hFG

/-- The original fan is exactly zero and the radial cones on all nonempty
proper intrinsic convex faces of the actual input polytope. -/
theorem mem_faceFan_iff_exists_convex_isExtreme (I : ToricInput n)
    (σ : Set (RealSpace n)) :
    σ ∈ faceFan I ↔ σ = {0} ∨
      ∃ F : Set (RealSpace n), Convex ℝ F ∧
        IsExtreme ℝ (latticePolytope I.vertices) F ∧ F.Nonempty ∧
        F ≠ latticePolytope I.vertices ∧ σ = radialCone F := by
  simpa only [I.isExposed_iff_convex_isExtreme, and_assoc] using
    mem_faceFan_iff_exists_isExposed I σ

/-- The literal FLTZ link admits the source formula with all intrinsic
nonempty proper convex faces, in the same quotient torus and boundary. -/
theorem mem_fltzLink_iff_exists_convex_isExtreme (I : ToricInput n)
    (x : Cotangent n) :
    x ∈ fltzLink I ↔ x ∈ cosphere ∧
      ∃ F : Set (RealSpace n), Convex ℝ F ∧
        IsExtreme ℝ (latticePolytope I.vertices) F ∧ F.Nonempty ∧
        F ≠ latticePolytope I.vertices ∧
        x.1 ∈ coneTorus (radialCone F) ∧ x.2 ∈ radialCone F := by
  simpa only [I.isExposed_iff_convex_isExtreme, and_assoc] using
    mem_fltzLink_iff_exists_isExposed I x

end FsFltz
