import FsFltz.Analysis.TailoringCriticalToriClassification
import FsFltz.Analysis.OmegaLimitConnected
import FsFltz.Geometry.OmegaLimitLyapunov

/-!
# Every compact tailored forward orbit approaches one critical face torus

Source: `geometric-part-fsf-proof.tex`, `thm:core`, lines 1735–1747.
This consumes the exhaustive native critical-locus classification, the
same-potential strict Lyapunov theorem, and connectedness of actual forward
limit sets. Local geometric trapping is the next obligation.
-/

noncomputable section
namespace FsFltz
open Geometry Set Filter Function
open scoped Topology ContDiff Manifold
variable {n : ℕ}

/-- The actual complete intrinsic flow eventually lies in every neighborhood
of one literal critical torus. No finite critical-locus certificate is supplied. -/
theorem IsStronglyCompatibleEndPotential.exists_fullFiber_omegaLimit_face_torus
    {I : ToricInput n} {φEnd : RealSpace n → ℝ}
    (hStrong : IsStronglyCompatibleEndPotential I φEnd) (hEnd1 : ContDiff ℝ 1 φEnd)
    {d : ℝ} (hd : 0 < d)
    (hEndConv : ConvexOn ℝ univ (fun u : EuclideanSpace ℝ (Fin n) =>
      φEnd ((EuclideanSpace.equiv (Fin n) ℝ) u) - d * ‖u‖ ^ 2))
    {a : ℝ} (ha : 0 < a) (hEndLower : ∀ u, a * ‖u‖ ^ 2 ≤ φEnd u)
    {φ : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    {R : ℝ} (hEnd : ∀ u,
      R ≤ ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖ → φ u = φEnd u) :
    ∃ u : {s : Finset (Lattice n) //
        IsPolytopeFace I.vertices s ∧ s.Nonempty ∧ s ≠ I.vertices} → ℝ → RealSpace n,
      ∃ B : ℝ, 0 < B ∧ ∀ β ≥ B,
        ∀ (N : SmoothManifold (2 * n - 2)) (j : N.SmoothEmbedding (lgManifold n)),
          Set.range j.map = {y | tailoringFamily I β 1 y = 1} →
          ∀ F : CompleteLiouvilleFlow N
            (N.liouvilleVector (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ))),
          ∀ p : N.Point, IsCompact (closure (F.flow.forwardOrbit p)) →
          ∃ s, omegaLimit atTop F.flow {p} ⊆
              j.map ⁻¹' ({u s β} ×ˢ coneTorus (positiveCone s.val)) ∧
            ∀ O : Set N.Point, IsOpen O →
              j.map ⁻¹' ({u s β} ×ˢ coneTorus (positiveCone s.val)) ⊆ O →
              ∀ᶠ t in atTop, F.flow t p ∈ O := by
  classical
  obtain ⟨u, Bc, hBc, hclass⟩ := hStrong.exists_fullFiber_critical_face_tori
    hEnd1 hd hEndConv ha hEndLower hφ hc hU hlower hupper hEnd
  obtain ⟨Bl, _, hlyap⟩ := tailoringEndpoint_exists_uniform_fullFiber_strict_lyapunov
    I hφ hc hU hlower hupper hStrong ha hEndLower hEnd
  refine ⟨u, max Bc Bl, hBc.trans_le (le_max_left _ _), ?_⟩
  intro β hβ N j himage F p hcompact
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
    j.map ⁻¹' ({u s β} ×ˢ coneTorus (positiveCone s.val))
  have hcβ := hclass β ((le_max_left _ _).trans hβ)
  have hlβ := hlyap β ((le_max_right _ _).trans hβ) N j himage
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
