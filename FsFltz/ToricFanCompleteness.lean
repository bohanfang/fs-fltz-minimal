import FsFltz.ToricFan
import Mathlib.Analysis.Convex.Gauge
import Mathlib.Analysis.LocallyConvex.Separation

/-!
# Completeness of the finite face fan

Source: `geoemtric-part-fsf.tex`, `sec:data`, lines 57–66: the finite
polytope contains zero in its interior, and its nonempty proper face cones
cover the real lattice space. The exact fan supplies the positive-cone
FLTZ link in `eq:link`, lines 99–109, as requested in the first foundation
layer of `sec:lean`, lines 778–782.

The finite convex hull is compact. Its gauge normalizes each nonzero vector
to a frontier point. Separation from the interior places that point on a
nonempty proper exposed face. The existing face-support and radial-cone
identifications then give a member of the original `faceFan`, rather than
an independently supplied fan-cover assumption. As a consumer, every unit
cotangent direction at the zero torus point belongs to the literal link.

This proves the cover property. Lattice smoothness, closure under all
intrinsic cone faces, and the geometric existence target `thm:target`
remain separate obligations.
-/

noncomputable section

namespace FsFltz

open scoped Topology

variable {n : ℕ}

/-- The convex hull of any finite lattice set is compact. -/
theorem isCompact_latticePolytope (V : Finset (Lattice n)) :
    IsCompact (latticePolytope V) := by
  exact (V.finite_toSet.image latticeReal).isCompact_convexHull ℝ

/-- Each nonzero direction has a positive radial multiple on the actual
polytope frontier. Compactness makes its gauge strictly positive. -/
theorem ToricInput.exists_pos_smul_mem_frontier (I : ToricInput n)
    {p : RealSpace n} (hp : p ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ r • p ∈ frontier (latticePolytope I.vertices) := by
  have hnhds : latticePolytope I.vertices ∈ 𝓝 (0 : RealSpace n) :=
    mem_interior_iff_mem_nhds.mp I.zero_interior
  have hg : 0 < gauge (latticePolytope I.vertices) p :=
    (gauge_pos (absorbent_nhds_zero hnhds)
      ((isCompact_latticePolytope I.vertices).isVonNBounded ℝ)).mpr hp
  refine ⟨(gauge (latticePolytope I.vertices) p)⁻¹, inv_pos.mpr hg, ?_⟩
  apply (gauge_eq_one_iff_mem_frontier (convex_convexHull ℝ _) hnhds).mp
  rw [gauge_smul_of_nonneg (inv_nonneg.mpr hg.le)]
  exact inv_mul_cancel₀ (ne_of_gt hg)

/-- Every frontier point lies on a nonempty proper geometric exposed face.
Separation from the nonempty interior gives the supporting functional. -/
theorem ToricInput.exists_proper_isExposed_of_mem_frontier (I : ToricInput n)
    {x : RealSpace n} (hx : x ∈ frontier (latticePolytope I.vertices)) :
    ∃ F : Set (RealSpace n), IsExposed ℝ (latticePolytope I.vertices) F ∧
      F.Nonempty ∧ F ≠ latticePolytope I.vertices ∧ x ∈ F := by
  have hcompact := isCompact_latticePolytope I.vertices
  have hconv : Convex ℝ (latticePolytope I.vertices) := convex_convexHull ℝ _
  have hclosure : closure (interior (latticePolytope I.vertices)) =
      latticePolytope I.vertices := by
    rw [hconv.closure_interior_eq_closure_of_nonempty_interior ⟨0, I.zero_interior⟩,
      hcompact.isClosed.closure_eq]
  obtain ⟨ℓ, hlt⟩ := geometric_hahn_banach_open_point hconv.interior isOpen_interior hx.2
  have hbound : ∀ y ∈ latticePolytope I.vertices, ℓ y ≤ ℓ x := by
    intro y hy
    apply le_on_closure (fun z hz => (hlt z hz).le) ℓ.continuous.continuousOn
      continuousOn_const
    rwa [hclosure]
  have hxQ : x ∈ latticePolytope I.vertices := by
    exact hcompact.isClosed.closure_eq ▸ hx.1
  let F : Set (RealSpace n) := {y ∈ latticePolytope I.vertices | ℓ y = ℓ x}
  have hxF : x ∈ F := ⟨hxQ, rfl⟩
  refine ⟨F, ?_, ⟨x, hxF⟩, ?_, hxF⟩
  · intro _
    refine ⟨ℓ, ?_⟩
    ext y
    constructor
    · rintro ⟨hy, he⟩
      exact ⟨hy, fun z hz => he ▸ hbound z hz⟩
    · rintro ⟨hy, hmax⟩
      exact ⟨hy, le_antisymm (hbound y hy) (hmax x hxQ)⟩
  · intro he
    have hzero : (0 : RealSpace n) ∈ F := he.symm ▸ interior_subset I.zero_interior
    exact (ne_of_lt (hlt 0 I.zero_interior)) hzero.2

/-- Every vector belongs to a cone in the exact source-defined face family.
The nonzero case consumes radial frontier normalization and a supporting face. -/
theorem ToricInput.exists_mem_faceFan (I : ToricInput n) (p : RealSpace n) :
    ∃ σ ∈ faceFan I, p ∈ σ := by
  by_cases hp : p = 0
  · exact ⟨{0}, Or.inl rfl, hp⟩
  obtain ⟨r, hr, hx⟩ := I.exists_pos_smul_mem_frontier hp
  obtain ⟨F, hF, hne, hproper, hpoint⟩ := I.exists_proper_isExposed_of_mem_frontier hx
  refine ⟨radialCone F, (mem_faceFan_iff_exists_isExposed I _).mpr
    (Or.inr ⟨F, hF, hne, hproper, rfl⟩), r⁻¹, (inv_pos.mpr hr).le,
    r • p, hpoint, ?_⟩
  simp only [smul_smul, inv_mul_cancel₀ (ne_of_gt hr), one_smul]

/-- Completeness is literal coverage of the entire real lattice space. -/
theorem ToricInput.sUnion_faceFan (I : ToricInput n) :
    ⋃₀ faceFan I = Set.univ := by
  apply Set.eq_univ_of_forall
  intro p
  exact Set.mem_sUnion.mpr (I.exists_mem_faceFan p)

/-- The annihilator torus of every cone contains the zero torus point. -/
theorem zero_mem_coneTorus (σ : Set (RealSpace n)) : (0 : Torus n) ∈ coneTorus σ := by
  intro v _
  simp [integralAngle]

/-- Fan completeness places every unit cotangent direction over the zero
torus point in the original FLTZ link with an actual nonzero cone witness. -/
theorem ToricInput.zero_angle_mem_fltzLink (I : ToricInput n)
    {p : RealSpace n} (hp : (0, p) ∈ cosphere) : (0, p) ∈ fltzLink I := by
  obtain ⟨σ, hσ, hpσ⟩ := I.exists_mem_faceFan p
  refine ⟨hp, σ, hσ, ?_, zero_mem_coneTorus σ, hpσ⟩
  intro he
  apply cotangent_ne_zero_of_mem_cosphere hp
  simpa only [he, Set.mem_singleton_iff] using hpσ

end FsFltz
