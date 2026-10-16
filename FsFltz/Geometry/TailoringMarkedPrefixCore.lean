import FsFltz.Geometry.OriginalKMarkedPrefix
import FsFltz.Geometry.TailoringFullCoreExistence
import FsFltz.Geometry.SmoothEmbeddingFactorization

/-!
# The full core of the retained marked ribbon

Source: `geometric-part-fsf-proof.tex`, `sec:skeleton`, lines 1569–1575,
`thm:core`, lines 1728–1750, and `subsec:junction`, lines 1876–1905.
The actual full-fiber marking transfers the core to the same retained pair.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz
open Geometry Geometry.SmoothManifold

/-- The full core of the retained compact ribbon, in its actual ambient
embedding, is the entire intrinsic relatively compact forward-orbit set. -/
theorem FullFiberRibbonMarking.image_core_eq {n : ℕ} {P : WitnessedPair n}
    {R : P.ribbonDomain.domain.extension.SmoothEmbedding (lgManifold n)}
    {f : LGSpace n → ℂ} {value : ℂ} {φ : RealSpace n → ℝ}
    (M : FullFiberRibbonMarking P R f value φ) :
    R.map '' P.ribbonCompletion.core = M.embedding.map ''
      {x | IsCompact (closure (M.primitive.completeFlow.flow.forwardOrbit x))} := by
  have h := M.marking.image_core_eq_relativelyCompact_forwardOrbit
  change M.inclusion '' {x : P.ribbonDomain.domain.Point | x.val ∈ P.ribbonCompletion.core} =
    {x | IsCompact (closure (M.primitive.completeFlow.flow.forwardOrbit x))} at h
  rw [← h, Set.image_image]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx.1⟩, hx, M.compact_square ⟨x, hx.1⟩⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.val, hx, (M.compact_square x).symm⟩

/-- Two presentations of one embedded full fiber have the same embedded
relatively compact forward-orbit set for the same ambient primitive. -/
theorem embedded_completePrimitive_compactOrbits_eq
    {d a : ℕ} (A : SmoothManifold a) (N M : SmoothManifold d)
    (i : N.SmoothEmbedding A) (j : M.SmoothEmbedding A)
    (hrange : range i.map = range j.map) (α : A.Form 1)
    (P : CompletePrimitive N (N.pullback A i.map α))
    (Q : CompletePrimitive M (M.pullback A j.map α)) :
    i.map '' {x | IsCompact (closure (P.completeFlow.flow.forwardOrbit x))} =
      j.map '' {x | IsCompact (closure (Q.completeFlow.flow.forwardOrbit x))} := by
  obtain ⟨q, hq⟩ := exists_smoothEmbedding_factor M N A j i hrange.subset
  obtain ⟨r, hr⟩ := exists_smoothEmbedding_factor N M A i j hrange.symm.subset
  let e : N.SmoothEquiv M :=
    { toEquiv :=
        { toFun := q.map, invFun := r.map
          left_inv := fun x => i.embedding.injective ((hr (q.map x)).trans (hq x))
          right_inv := fun x => j.embedding.injective ((hq (r.map x)).trans (hr x)) }
      contMDiff_toFun := q.map.contMDiff
      contMDiff_invFun := r.map.contMDiff }
  have heq : j.map ∘ e = i.map := funext hq
  have hprim : N.pullback M e (M.pullback A j.map α) = N.pullback A i.map α := by
    rw [← N.pullback_comp M A (e.contMDiff.mdifferentiable (by simp))
      (j.map.contMDiff.mdifferentiable (by simp)), heq]
  have hflow (x : N.Point) (t : ℝ) :
      e (P.completeFlow.flow t x) = Q.completeFlow.flow t (e x) :=
    P.toCompleteLiouvilleManifold.map_flow Q.toCompleteLiouvilleManifold e hprim x t
  have horbit (x : N.Point) : e '' P.completeFlow.flow.forwardOrbit x =
      Q.completeFlow.flow.forwardOrbit (e x) := by
    ext z
    constructor
    · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
      exact ⟨t, (hflow x t).symm⟩
    · rintro ⟨t, rfl⟩
      exact ⟨P.completeFlow.flow t x, ⟨t, rfl⟩, hflow x t⟩
  have hc (x : N.Point) :
      IsCompact (closure (P.completeFlow.flow.forwardOrbit x)) ↔
        IsCompact (closure (Q.completeFlow.flow.forwardOrbit (e x))) := by
    have hcl : e '' closure (P.completeFlow.flow.forwardOrbit x) =
        closure (Q.completeFlow.flow.forwardOrbit (e x)) := by
      simpa only [Diffeomorph.coe_toHomeomorph, horbit] using
        e.toHomeomorph.image_closure (P.completeFlow.flow.forwardOrbit x)
    rw [← hcl]
    exact e.toHomeomorph.isEmbedding.isCompact_iff
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨e x, (hc x).mp hx, hq x⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨e.symm x, (hc (e.symm x)).mpr (by simpa using hx), ?_⟩
    have hh := (hq (e.symm x)).symm
    change i.map (e.symm x) = j.map (e (e.symm x)) at hh
    simpa using hh

/-- Transfer a proved full-fiber orbit classification to any actual retained
ribbon marking of that same fiber and primitive. -/
theorem FullFiberRibbonMarking.image_core_eq_of_fullFiber {n : ℕ} {P : WitnessedPair n}
    {R : P.ribbonDomain.domain.extension.SmoothEmbedding (lgManifold n)}
    {f : LGSpace n → ℂ} {value : ℂ} {φ : RealSpace n → ℝ}
    (M : FullFiberRibbonMarking P R f value φ)
    (N : SmoothManifold (2 * n - 2)) (j : N.SmoothEmbedding (lgManifold n))
    (Q : CompletePrimitive N (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)))
    (himage : range j.map = {y | f y = value}) {S : Set (LGSpace n)}
    (hS : S ⊆ range j.map)
    (hcore : ∀ x : N.Point, IsCompact (closure (Q.completeFlow.flow.forwardOrbit x)) ↔
      j.map x ∈ S) :
    R.map '' P.ribbonCompletion.core = S := by
  rw [M.image_core_eq, embedded_completePrimitive_compactOrbits_eq (lgManifold n)
    M.manifold N M.embedding j (M.image.trans himage.symm) (lambdaPotentialForm φ)
    M.primitive Q]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (hcore x).mp hx
  · intro hy
    obtain ⟨x, rfl⟩ := hS hy
    exact ⟨x, (hcore x).mpr hy, rfl⟩

/-- Finite toric input constructs a marked original-K prefix whose actual
terminal ribbon has the literal full conormal core, using the same potential
as the core theorem. No core equality or comparison chain is an input. -/
theorem ToricInput.exists_uniform_original_marked_prefix_fullCore {n : ℕ}
    (I : ToricInput n) :
    ∃ φEnd φ : RealSpace n → ℝ,
      IsStronglyCompatibleEndPotential I φEnd ∧ ContDiff ℝ 1 φEnd ∧ ContDiff ℝ ∞ φ ∧
      ∃ c U : ℝ, 0 < c ∧ 0 < U ∧
      (∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
        inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v) ∧
      (∀ u v : EuclideanSpace ℝ (Fin n),
        inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2) ∧
      (∃ L > 0, ∀ u, L ≤ ‖(EuclideanSpace.equiv (Fin n) ℝ).symm u‖ → φ u = φEnd u) ∧
      ∃ Aamb Cminus Cplus β₀ : ℝ, AmbientEndBound I Aamb ∧
        0 < Cminus ∧ Cminus < Cplus ∧ 0 < β₀ ∧ ∀ β ≥ β₀,
        max 1 (sublevelMagnitudeSup I Aamb) < Real.exp β ∧
        RatioSetWellDefined I (Real.exp β) ∧
        (∃ Afib : ℝ, FiberEndBound I Aamb (Real.exp β) Afib ∧
          Afib < Cminus ^ 2 * β ^ 2 / 2) ∧
        ∀ originalK : ℝ, K0 I (Real.exp β) ≤ originalK →
          ∃ K : ℝ, 0 < K ∧ originalK ≤ K / Real.exp β ^ 2 ∧
          ∃ m : RoundingChoice,
            GeometricAdmissibleRounding I (Real.exp β) originalK
              (Cminus ^ 2 * β ^ 2 / 2) (Cplus ^ 2 * β ^ 2 / 2) m ∧
            ∃ P : PotentialTailoringOriginalMarkedPrefix I φ β Cplus
              (Cminus ^ 2 * β ^ 2 / 2) originalK K m,
              ((P.marked.tailoring.embedding parameterOne).comp
                (P.marked.tailoring.deformation.target.ambientDomain.domain.boundaryInclusion.comp
                  P.marked.tailoring.deformation.target.ribbonEmbedding)).map ''
                P.marked.tailoring.deformation.target.ribbonCompletion.core =
                  tailoringCoreSection I φEnd β := by
  obtain ⟨φEnd, φ, hstrong, hEnd1, hφ, _hzero, c, U, hc, hU, hlower, hupper,
    _hnear, L, hL, hend, _ΦEnd, _Φ, _hΦEndeq, _hΦEnd0, _hΦEnd,
    _hΦEndinv, _hΦeq, _hΦ, _hΦinv, _Fcore, _hFcore, Bcore, hBcore, hcore⟩ :=
    I.exists_complete_tailoring_fullCore
  obtain ⟨Aamb, F, hamb, hF, hprefix⟩ :=
    coefficientPath_tailoring_exists_uniform_original_marked_prefix
      I hφ hc hU hlower hupper hEnd1 hstrong.smooth hstrong.homogeneous hL hend
  let Cminus := F + 1
  let Cplus := F + 2
  have hCminus : 0 < Cminus := by dsimp [Cminus]; linarith
  have hFCminus : F < Cminus := by dsimp [Cminus]; linarith
  have hCminusCplus : Cminus < Cplus := by dsimp [Cminus, Cplus]; linarith
  obtain ⟨Bprefix, hBprefix, hprefix⟩ := hprefix Cplus (hFCminus.trans hCminusCplus)
  refine ⟨φEnd, φ, hstrong, hEnd1, hφ, c, U, hc, hU, hlower, hupper,
    ⟨L, hL, hend⟩, Aamb, Cminus, Cplus, max Bprefix Bcore,
    hamb, hCminus, hCminusCplus, hBprefix.trans_le (le_max_left _ _), ?_⟩
  intro β hβ
  have hβP := (le_max_left Bprefix Bcore).trans hβ
  have hβC := (le_max_right Bprefix Bcore).trans hβ
  have hβpos := hBprefix.trans_le hβP
  obtain ⟨hR, hset, hfib, Kstar, hKstar, hprefix⟩ := hprefix β hβP
  have hlevel : F ^ 2 * β ^ 2 / 2 < Cminus ^ 2 * β ^ 2 / 2 := by gcongr
  have houter : Cminus ^ 2 * β ^ 2 / 2 < Cplus ^ 2 * β ^ 2 / 2 := by gcongr
  obtain ⟨δ, hδ, _hgap, hprefix⟩ := hprefix (Cminus ^ 2 * β ^ 2 / 2) hlevel houter
  refine ⟨hR, hset, ⟨F ^ 2 * β ^ 2 / 2, hfib, hlevel⟩, ?_⟩
  intro originalK hK
  let K := max Kstar (originalK * Real.exp β ^ 2)
  have hKpos : 0 < K := hKstar.trans_le (le_max_left _ _)
  have hKL : originalK ≤ K / Real.exp β ^ 2 :=
    (le_div_iff₀ (sq_pos_of_pos (Real.exp_pos β))).mpr (le_max_right _ _)
  let m : RoundingChoice := ⟨δ, roundingProfile δ hδ⟩
  obtain ⟨hm, hprefix⟩ := hprefix m hδ le_rfl originalK hK
  obtain ⟨P⟩ := hprefix K (le_max_left _ _) hKL
  refine ⟨K, hKpos, hKL, m, hm, P, ?_⟩
  obtain ⟨_hcompact, _hbij, _himageRadial, N, j, Q, himage, hiff, _htruncations⟩ := hcore β hβC
  apply (P.marked.tailoring.ribbon_marking parameterOne).image_core_eq_of_fullFiber N j Q
    (by simpa [parameterOne] using himage)
  · intro y hy
    rw [himage]
    exact hy.2
  · exact hiff

end FsFltz
