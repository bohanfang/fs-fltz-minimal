import FsFltz.Geometry.TailoringCriticalNormalData
import FsFltz.Analysis.TailoringCriticalOmegaLimit

/-!
# The same critical radii for normal trapping and omega limits

Source: `geometric-part-fsf-proof.tex`, `lem:stable`, lines 1709–1724,
and `thm:core`, lines 1738–1748. An actual reconstructed critical chart
and its literal retained support identify the critical-normal datum with
the exhaustive classifier. The same classifier is then used for the actual
omega-limit conclusion, so no equality of independently chosen radii is
assumed at the reverse-core junction.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FsFltz

open Geometry Set Filter Function
open scoped Topology BigOperators ContDiff Manifold

namespace CriticalFaceNormalData

variable {n : ℕ} {I : ToricInput n} {φEnd φ : RealSpace n → ℝ} {β : ℝ}
  {s : Finset (Lattice n)} {u : RealSpace n} {q : s → ℝ} {lam : ℝ}
  {B : (s → ℝ) →L[ℝ] RealSpace n} {R : (s → ℝ) →L[ℝ] (s → ℝ)}

theorem retainedVertices_eq (D : CriticalFaceNormalData I φEnd φ β s u q lam B R)
    (hsub : s ⊆ I.vertices) : tailoringRetainedVertices I β u = s := by
  classical
  have hcut := D.plateau_cutoff u D.plateau_mem
  ext v
  rw [mem_tailoringRetainedVertices_iff]
  constructor
  · intro hv
    rw [hcut v (Finset.mem_insert_of_mem hv.1)] at hv
    by_contra hvs
    have hv0 : v ≠ 0 := fun h => I.zero_not_mem_vertices (h ▸ hv.1)
    simpa [hv0, hvs] using hv.2
  · intro hv
    refine ⟨hsub hv, ?_⟩
    rw [hcut v (Finset.mem_insert_of_mem (hsub hv)), ite_eq_left (Or.inr hv)]
    norm_num

/-- An actual critical chart and exact retained supports identify the
reconstructed radius with a classifier radius on the same face. -/
theorem radial_eq_of_critical_torus_classification
    (D : CriticalFaceNormalData I φEnd φ β s u q lam B R)
    (hs : IsPolytopeFace I.vertices s) (hsne : s.Nonempty) (hsproper : s ≠ I.vertices)
    (hφ : ContDiff ℝ ∞ φ) {c : ℝ} (hc : 0 < c)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hpi : ∀ y, tailoringFamily I β 1 y = 1 →
      0 < (lgManifold n).planePairing (lambdaPotentialForm φ) (tailoringFamily I β 1) y
        (nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower y))
    (N : SmoothManifold (2 * n - 2)) (j : N.SmoothEmbedding (lgManifold n))
    (himage : range j.map = {y | tailoringFamily I β 1 y = 1})
    (radii : {t : Finset (Lattice n) //
      IsPolytopeFace I.vertices t ∧ t.Nonempty ∧ t ≠ I.vertices} → RealSpace n)
    (hsupport : ∀ t, tailoringRetainedVertices I β (radii t) = t.val)
    (hclass : ∀ a : N.Point,
      (∀ V : N.Tangent a, N.scalarDerivative (fun b => φ (j.map b).1) a V = 0) →
      ∃ t, j.map a ∈ {radii t} ×ˢ coneTorus (positiveCone t.val)) :
    u = radii ⟨s, hs, hsne, hsproper⟩ := by
  have hθ : (0 : Torus n) ∈ coneTorus (positiveCone s) := zero_mem_coneTorus _
  have hmem : (u, (0 : Torus n)) ∈ range j.map := by
    rw [himage]
    exact D.fiber_eq 0 hθ
  obtain ⟨a, ha⟩ := hmem
  obtain ⟨ξ, hξ⟩ := lgCover_surjective n (u, (0 : Torus n))
  obtain ⟨C⟩ := D.nativeChart hs hφ hc hlower hpi 0 hθ N j himage a ξ
    (ha.trans hξ.symm) hξ
  obtain ⟨t, ht⟩ := hclass a (C.critical hφ)
  have hrad : u = radii t := (congrArg Prod.fst ha).symm.trans ht.1
  have hface : t = ⟨s, hs, hsne, hsproper⟩ := by
    apply Subtype.ext
    exact (hsupport t).symm.trans (hrad ▸ D.retainedVertices_eq hs.1)
  simpa only [hface] using hrad

end CriticalFaceNormalData

/-- One chosen classifier supplies both exact identification of every
constructed critical-normal datum and the omega-limit torus conclusion. -/
theorem IsStronglyCompatibleEndPotential.exists_fullFiber_identified_omegaLimit_face_torus
    {n : ℕ} {I : ToricInput n} {φEnd : RealSpace n → ℝ}
    (hStrong : IsStronglyCompatibleEndPotential I φEnd) (hEnd1 : ContDiff ℝ 1 φEnd)
    {d : ℝ} (hd : 0 < d)
    (hEndConv : ConvexOn ℝ univ (fun u : EuclideanSpace ℝ (Fin n) =>
      φEnd ((EuclideanSpace.equiv (Fin n) ℝ) u) - d * ‖u‖ ^ 2))
    {a₀ : ℝ} (ha₀ : 0 < a₀) (hEndLower : ∀ u, a₀ * ‖u‖ ^ 2 ≤ φEnd u)
    {φ : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    {R₀ : ℝ} (hEnd : ∀ u,
      R₀ ≤ ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖ → φ u = φEnd u) :
    let Faces := {s : Finset (Lattice n) //
      IsPolytopeFace I.vertices s ∧ s.Nonempty ∧ s ≠ I.vertices}
    ∃ radii : Faces → ℝ → RealSpace n, ∃ B₀ : ℝ, 0 < B₀ ∧ ∀ β ≥ B₀,
      (∀ s, ∀ θ ∈ coneTorus (positiveCone s.val),
        tailoringFamily I β 1 (radii s β, θ) = 1 ∧
        tailoringRetainedVertices I β (radii s β) = s.val) ∧
      Pairwise (fun s t => Disjoint
        ({radii s β} ×ˢ coneTorus (positiveCone s.val))
        ({radii t β} ×ˢ coneTorus (positiveCone t.val))) ∧
      ∀ (N : SmoothManifold (2 * n - 2)) (j : N.SmoothEmbedding (lgManifold n)),
        range j.map = {y | tailoringFamily I β 1 y = 1} →
        (∀ p : N.Point,
          (((∀ V : N.Tangent p, N.scalarDerivative (fun b => φ (j.map b).1) p V = 0) ∨
            N.liouvilleVector (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)) p = 0) ↔
            ∃ s, j.map p ∈ {radii s β} ×ˢ coneTorus (positiveCone s.val))) ∧
        (∀ (s : Faces) (u : RealSpace n) (q : s.val → ℝ) (lam : ℝ)
          (B : (s.val → ℝ) →L[ℝ] RealSpace n)
          (R : (s.val → ℝ) →L[ℝ] (s.val → ℝ)),
          CriticalFaceNormalData I φEnd φ β s.val u q lam B R → u = radii s β) ∧
        ∀ F : CompleteLiouvilleFlow N
          (N.liouvilleVector (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ))),
          ∀ p : N.Point, IsCompact (closure (F.flow.forwardOrbit p)) →
          ∃ s, omegaLimit atTop F.flow {p} ⊆
              j.map ⁻¹' ({radii s β} ×ˢ coneTorus (positiveCone s.val)) ∧
            ∀ O : Set N.Point, IsOpen O →
              j.map ⁻¹' ({radii s β} ×ˢ coneTorus (positiveCone s.val)) ⊆ O →
              ∀ᶠ t in atTop, F.flow t p ∈ O := by
  classical
  dsimp only
  obtain ⟨radii, Bc, hBc, hclass⟩ := hStrong.exists_fullFiber_critical_face_tori
    hEnd1 hd hEndConv ha₀ hEndLower hφ hc hU hlower hupper hEnd
  obtain ⟨Bl, _, hlyap⟩ := tailoringEndpoint_exists_uniform_fullFiber_strict_lyapunov
    I hφ hc hU hlower hupper hStrong ha₀ hEndLower hEnd
  obtain ⟨_, _, _, _, Bπ, _, hπ⟩ :=
    tailoringFamily_exists_uniform_native_planePairing_positivity I hφ hc hU hlower hupper
  refine ⟨radii, max Bc (max Bl Bπ), hBc.trans_le (le_max_left _ _), ?_⟩
  intro β hβ
  have hβc := (le_max_left _ _).trans hβ
  have hβl := (le_max_left _ _).trans ((le_max_right _ _).trans hβ)
  have hβπ := (le_max_right _ _).trans ((le_max_right _ _).trans hβ)
  have hcβ := hclass β hβc
  refine ⟨hcβ.1, hcβ.2.1, ?_⟩
  intro N j himage
  refine ⟨fun p => (hcβ.2.2 N j himage p).2.1, ?_, ?_⟩
  · intro s u q lam B R D
    have hpi : ∀ y, tailoringFamily I β 1 y = 1 →
        0 < (lgManifold n).planePairing (lambdaPotentialForm φ) (tailoringFamily I β 1) y
          (nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower y) := by
      intro y hy
      exact (hπ β hβπ 1 (by simp) y
        (nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower y)).2.2 (by simp [hy])
    exact D.radial_eq_of_critical_torus_classification s.property.1 s.property.2.1
      s.property.2.2 hφ hc hlower hpi N j himage (fun t => radii t β)
      (fun t => (hcβ.1 t 0 (zero_mem_coneTorus _)).2)
      (fun a ha => (hcβ.2.2 N j himage a).1.mp ha)
  intro F p hcompact
  let Faces := {s : Finset (Lattice n) //
    IsPolytopeFace I.vertices s ∧ s.Nonempty ∧ s ≠ I.vertices}
  let embed : Faces → {s // s ∈ I.vertices.powerset} := fun s =>
    ⟨s.val, Finset.mem_powerset.mpr s.property.1.1⟩
  have hinj : Injective embed := by
    intro s t h
    exact Subtype.ext (congrArg (fun t : {s // s ∈ I.vertices.powerset} => t.val) h)
  let : Finite Faces := Finite.of_injective embed hinj
  let : Fintype Faces := Fintype.ofFinite Faces
  let C : Faces → Set N.Point := fun s =>
    j.map ⁻¹' ({radii s β} ×ˢ coneTorus (positiveCone s.val))
  have hlβ := hlyap β hβl N j himage
  have hV : ContMDiff 𝓘(ℝ, Model (2 * n - 2)) 𝓘(ℝ, ℝ) ∞
      (fun q : N.Point => φ (j.map q).1) :=
    (contMDiff_potentialValue hφ).comp j.map.contMDiff
  have hstrict : ∀ q, N.liouvilleVector
      (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)) q ≠ 0 →
      0 < N.scalarDerivative (fun q => φ (j.map q).1) q
        (N.liouvilleVector (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)) q) := by
    intro q hq
    exact (hlβ q).2 (fun hcrit => hq ((hlβ q).1.mp hcrit))
  have hzero := (F.omegaLimit_nonempty_subset_zero _ hV hstrict hcompact).2
  have hC : ∀ s, IsClosed (C s) := fun s =>
    (isClosed_singleton.prod (isClosed_coneTorus _)).preimage j.map.contMDiff.continuous
  have hdisj : Pairwise (fun s t => Disjoint (C s) (C t)) := by
    intro s t hst
    exact (hcβ.2.1 hst).preimage j.map
  have hcover : omegaLimit atTop F.flow {p} ⊆ ⋃ s, C s := by
    intro q hq
    obtain ⟨s, hs⟩ := (hcβ.2.2 N j himage q).2.2.mp (hzero hq)
    exact mem_iUnion.mpr ⟨s, hs⟩
  exact omegaLimit_subset_one_and_eventually F.flow hcompact C hC hdisj hcover

end FsFltz
