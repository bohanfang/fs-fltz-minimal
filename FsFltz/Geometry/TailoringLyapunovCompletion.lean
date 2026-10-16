import FsFltz.Geometry.TailoringFiberMarking
import FsFltz.Geometry.CompletionCore
import FsFltz.Analysis.TailoringLyapunov
import FsFltz.Geometry.OmegaLimitLyapunov
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-!
# Proper potential and full core on the actual tailored completion

Source: `geometric-part-fsf-proof.tex`, `prop:lyapunov`, lines 1472–1496,
and `sec:skeleton`, lines 1569–1575. Properness and the orbit characterization
use the same chosen full-fiber presentation and the same primitive as its
actual inclusion completion marking. No skeleton identification is assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Topology
open scoped Manifold ContDiff

namespace FsFltz.Geometry
open SmoothManifold

variable {n : ℕ} {φ φEnd : RealSpace n → ℝ} {c : ℝ}
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

include hφ hEnd1 hEnd hhom hc hlower hL hend himage

/-- The retained potential is a proper map on the literal whole tailored
fiber, rather than a separately chosen exhaustion function. -/
theorem isProperMap_tailoringFiber_potential :
    IsProperMap (fun x : N.Point => φ (j.map x).1) := by
  have hcontinuous : Continuous (fun x : N.Point => φ (j.map x).1) :=
    (contMDiff_potential_W_level_value hφ j).continuous
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨hcontinuous, ?_⟩
  intro K hK
  obtain ⟨A, hA⟩ := hK.bddAbove
  apply (isCompact_tailoringFiber_potential_sublevel hφ hEnd1 hEnd hhom hc hlower hL
    hend I β s j himage A).of_isClosed_subset (hK.isClosed.preimage hcontinuous)
  intro x hx
  exact hA hx

variable (P : CompletePrimitive N (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)))
    (A : ℝ) (hpos : ∀ x : N.Point, A ≤ φ (j.map x).1 →
      0 < N.scalarDerivative (fun y => φ (j.map y).1) x
        (N.liouvilleVector (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)) x))

local notation "D" => tailoringFiberOutwardDomain hφ hEnd1 hEnd hhom hc hlower hL hend I β s j himage P A hpos

/-- Every completion of this actual full-fiber truncation has the same
native core: precisely the relatively compact forward orbits of the given
complete intrinsic fiber flow under its inclusion marking. -/
theorem tailoringFiberOutwardDomain_core_eq_relativelyCompact_forwardOrbit
    (C : Completion D) :
    C.core = {x : N.Point | IsCompact (closure (P.completeFlow.flow.forwardOrbit x))} := by
  have h := (tailoringFiberOutwardInclusionMarkingOfCompletion hφ hEnd1 hEnd hhom hc
    hlower hL hend I β s j himage P A hpos C).image_core_eq_relativelyCompact_forwardOrbit
  have he : (fun x : (D).domain.Point => x.val) ''
      {x : (D).domain.Point | x.val ∈ C.core} = C.core := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hx.1⟩, hx, rfl⟩
  exact he.symm.trans h

include hpos in
/-- The intrinsic skeleton, defined by all forward orbits on the whole
fiber, is compact; the actual compact-domain completion proves this. -/
theorem isCompact_tailoringFiber_relativelyCompact_forwardOrbits :
    IsCompact {x : N.Point | IsCompact (closure (P.completeFlow.flow.forwardOrbit x))} := by
  let C := tailoringFiberOutwardCompletion hφ hEnd1 hEnd hhom hc hlower hL hend I β s j himage P A hpos
  rw [← tailoringFiberOutwardDomain_core_eq_relativelyCompact_forwardOrbit hφ hEnd1
    hEnd hhom hc hlower hL hend I β s j himage P A hpos C]
  exact C.isCompact_core

include hpos in
/-- The embedded full intrinsic skeleton is compact in the original
logarithmic torus ambient, with no change of full-fiber presentation. -/
theorem isCompact_tailoringFiber_embedded_relativelyCompact_forwardOrbits :
    IsCompact (j.map ''
      {x : N.Point | IsCompact (closure (P.completeFlow.flow.forwardOrbit x))}) :=
  (isCompact_tailoringFiber_relativelyCompact_forwardOrbits hφ hEnd1 hEnd hhom hc
    hlower hL hend I β s j himage P A hpos).image j.map.contMDiff.continuous

end FsFltz.Geometry

namespace FsFltz
open Geometry Geometry.SmoothManifold Filter

variable {n : ℕ}

/-- Same-potential properness, strict Lyapunov dynamics and actual compact
full-core markings, on one chosen complete full endpoint fiber. The forward
limit assertion uses the strict derivative of this very intrinsic field. -/
theorem tailoringEndpoint_exists_uniform_fullFiber_proper_lyapunov_compact_core
    (I : ToricInput n) {φ φEnd : RealSpace n → ℝ} {c U a : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    (hEnd1 : ContDiff ℝ 1 φEnd) (hstrong : IsStronglyCompatibleEndPotential I φEnd)
    (ha : 0 < a) (hEndLower : ∀ u, a * ‖u‖ ^ 2 ≤ φEnd u)
    {L : ℝ} (hL : 0 < L)
    (hend : ∀ u, L ≤ ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖ → φ u = φEnd u) :
    ∃ F : ℝ, 0 < F ∧ ∃ B : ℝ, 0 < B ∧ ∀ β ≥ B,
      ∃ (N : SmoothManifold (2 * n - 2)) (j : N.SmoothEmbedding (lgManifold n))
        (P : CompletePrimitive N (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)))
        (himage : range j.map = {y | tailoringFamily I β 1 y = 1}),
      IsProperMap (fun x : N.Point => φ (j.map x).1) ∧
      (∀ x : N.Point, ¬ (∀ v : N.Tangent x,
        N.scalarDerivative (fun y => φ (j.map y).1) x v = 0) →
        0 < N.scalarDerivative (fun y => φ (j.map y).1) x
          (N.liouvilleVector (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)) x)) ∧
      (∀ x : N.Point, IsCompact (closure (P.completeFlow.flow.forwardOrbit x)) →
        (omegaLimit atTop P.completeFlow.flow {x}).Nonempty ∧
          omegaLimit atTop P.completeFlow.flow {x} ⊆
            {y | ∀ v : N.Tangent y, N.scalarDerivative (fun z => φ (j.map z).1) y v = 0}) ∧
      ∀ A : ℝ, F ^ 2 * β ^ 2 / 2 ≤ A →
        ∃ hpos : ∀ x : N.Point, A ≤ φ (j.map x).1 →
          0 < N.scalarDerivative (fun y => φ (j.map y).1) x
            (N.liouvilleVector (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)) x),
        let D := tailoringFiberOutwardDomain hφ hEnd1 hstrong.smooth
          hstrong.homogeneous hc hlower hL hend I β 1 j himage P A hpos
        j.map '' D.domain.carrier = {y | tailoringFamily I β 1 y = 1 ∧ φ y.1 ≤ A} ∧
          Nonempty (Completion D) ∧ ∀ C : Completion D,
            Nonempty (InclusionMarking C P.toCompleteLiouvilleManifold (fun x => x.val)) ∧
              IsCompact C.core ∧
                C.core = {x : N.Point | IsCompact (closure (P.completeFlow.flow.forwardOrbit x))} ∧
                  ∀ x ∈ C.core, (omegaLimit atTop P.completeFlow.flow {x}).Nonempty ∧
                    omegaLimit atTop P.completeFlow.flow {x} ⊆
                      {y | ∀ v : N.Tangent y,
                        N.scalarDerivative (fun z => φ (j.map z).1) y v = 0} := by
  obtain ⟨F, hF, Bmark, hBmark, hmark⟩ := tailoringFamily_exists_uniform_fullFiber_markings
    I hφ hc hU hlower hupper hEnd1 hstrong.smooth hstrong.homogeneous hL hend
  obtain ⟨Blyap, _, hlyap⟩ := tailoringEndpoint_exists_uniform_fullFiber_strict_lyapunov
    I hφ hc hU hlower hupper hstrong ha hEndLower hend
  refine ⟨F, hF, max Bmark Blyap, hBmark.trans_le (le_max_left _ _), ?_⟩
  intro β hβ
  obtain ⟨N, j, P, himage, hdomains⟩ := hmark β ((le_max_left _ _).trans hβ) 1 (by simp)
  have hstrict := hlyap β ((le_max_right _ _).trans hβ) N j himage
  have hlimits (x : N.Point) (hx : IsCompact (closure (P.completeFlow.flow.forwardOrbit x))) :
      (omegaLimit atTop P.completeFlow.flow {x}).Nonempty ∧
        omegaLimit atTop P.completeFlow.flow {x} ⊆
          {y | ∀ v : N.Tangent y, N.scalarDerivative (fun z => φ (j.map z).1) y v = 0} := by
    obtain ⟨hne, hzero⟩ := P.completeFlow.omegaLimit_nonempty_subset_zero
      (fun y => φ (j.map y).1) (contMDiff_potential_W_level_value hφ j)
      (fun y hy => (hstrict y).2 (fun hcrit => hy ((hstrict y).1.mp hcrit))) hx
    exact ⟨hne, fun y hy => (hstrict y).1.mpr (hzero hy)⟩
  refine ⟨N, j, P, himage,
    isProperMap_tailoringFiber_potential hφ hEnd1 hstrong.smooth hstrong.homogeneous
      hc hlower hL hend I β 1 j himage,
    fun x => (hstrict x).2, hlimits, ?_⟩
  intro A hA
  obtain ⟨hpos, him, hC, hq⟩ := hdomains A hA
  refine ⟨hpos, him, hC, ?_⟩
  intro C
  have hcore := tailoringFiberOutwardDomain_core_eq_relativelyCompact_forwardOrbit hφ hEnd1
    hstrong.smooth hstrong.homogeneous hc hlower hL hend I β 1 j himage P A hpos C
  refine ⟨hq C, C.isCompact_core, hcore, ?_⟩
  intro x hx
  apply hlimits x
  rwa [hcore] at hx

end FsFltz
