import FsFltz.Geometry.TailoringFiberMarking
import FsFltz.Analysis.TailoringNonempty

/-!
# Nonempty actual full-tailored-fiber truncations

Source: `geometric-part-fsf-proof.tex`, `eq:fiberends`, lines 1230–1237,
and the finite-chain assembly, lines 2159–2166. The full-fiber point is
produced on the actual real-positive slice; the actual complete intrinsic
flow then enters every sufficiently large literal potential truncation.
Regularity alone is not used to infer nonemptiness.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz.Geometry

variable {n : ℕ}

/-- A point of the whole literal fiber is absorbed into the actual native
compact ribbon domain by its proved intrinsic complete flow. -/
theorem tailoringFiberOutwardDomain_nonempty
    {φ φEnd : RealSpace n → ℝ} {c : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hEnd1 : ContDiff ℝ 1 φEnd)
    (hEnd : ∀ u ≠ 0, ContDiffAt ℝ ∞ φEnd u)
    (hhom : ∀ r : ℝ, 0 < r → ∀ u, φEnd (r • u) = r ^ 2 * φEnd u)
    (hc : 0 < c)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    {L : ℝ} (hL : 0 < L)
    (hend : ∀ u, L ≤ ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖ → φ u = φEnd u)
    (I : ToricInput n) (β s : ℝ)
    {N : SmoothManifold (2 * n - 2)} (j : N.SmoothEmbedding (lgManifold n))
    (himage : range j.map = {y | tailoringFamily I β s y = 1})
    (P : CompletePrimitive N (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)))
    (A : ℝ) (hpos : ∀ x : N.Point, A ≤ φ (j.map x).1 →
      0 < N.scalarDerivative (fun y => φ (j.map y).1) x
        (N.liouvilleVector (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)) x))
    (hne : {y : LGSpace n | tailoringFamily I β s y = 1}.Nonempty) :
    (tailoringFiberOutwardDomain hφ hEnd1 hEnd hhom hc hlower hL hend
      I β s j himage P A hpos).domain.carrier.Nonempty := by
  obtain ⟨y, hy⟩ := hne
  have hyj : y ∈ range j.map := by rwa [himage]
  obtain ⟨x, _hx⟩ := hyj
  obtain ⟨T, _hT, hentry⟩ := tailoringFiber_absorbs_outward_sublevel
    hφ hEnd1 hEnd hhom hc hlower hL hend I β s j himage P A hpos x
  rw [tailoringFiberOutwardDomain_carrier]
  exact ⟨P.completeFlow.flow (-T) x, hentry⟩

/-- Every sufficiently large literal potential truncation of every member
of the actual tailoring family is nonempty, uniformly in the parameter.
Its native compact domain and inclusion marking are the already constructed
full-fiber truncation ones. -/
theorem _root_.FsFltz.tailoringFamily_exists_uniform_nonempty_fiber_truncations
    (I : ToricInput n) {φ φEnd : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    (hEnd1 : ContDiff ℝ 1 φEnd)
    (hEnd : ∀ u ≠ 0, ContDiffAt ℝ ∞ φEnd u)
    (hhom : ∀ r : ℝ, 0 < r → ∀ u, φEnd (r • u) = r ^ 2 * φEnd u)
    {L : ℝ} (hL : 0 < L)
    (hend : ∀ u, L ≤ ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖ → φ u = φEnd u) :
    ∃ F : ℝ, 0 < F ∧ ∃ β₀ : ℝ, 0 < β₀ ∧
      ∀ β ≥ β₀, ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 →
      ∀ A : ℝ, F ^ 2 * β ^ 2 / 2 ≤ A →
        {y : LGSpace n | tailoringFamily I β s y = 1 ∧ φ y.1 ≤ A}.Nonempty := by
  obtain ⟨F, hF, Bfull, hBfull, hfull⟩ := tailoringFamily_exists_uniform_fullFiber_markings
    I hφ hc hU hlower hupper hEnd1 hEnd hhom hL hend
  obtain ⟨Bne, _hBne, hne⟩ := tailoringFamily_exists_uniform_nonempty_fiber I
  refine ⟨F, hF, max Bfull Bne, hBfull.trans_le (le_max_left _ _), ?_⟩
  intro β hβ s hs A hA
  obtain ⟨N, j, P, himage, hlevels⟩ := hfull β ((le_max_left _ _).trans hβ) s hs
  obtain ⟨hpos, hrest⟩ := hlevels A hA
  obtain ⟨u, hu⟩ := hne β ((le_max_right _ _).trans hβ) s hs
  have hdomain := tailoringFiberOutwardDomain_nonempty hφ hEnd1 hEnd hhom hc hlower hL hend
    I β s j himage P A hpos ⟨(u, 0), hu⟩
  rw [← hrest.1]
  exact hdomain.image j.map

end FsFltz.Geometry
