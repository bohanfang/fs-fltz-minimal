import FsFltz.Geometry.CompactDomainLiouvillePullback
import FsFltz.Geometry.TailoringMarkedOuterBoundary
import FsFltz.Geometry.RankTwoPrimitiveFamily
import FsFltz.Geometry.OriginalParameterPairFamily

/-!
# Removing the base coefficient on the retained outer domain

Source: `geometric-part-fsf-proof.tex`, `sec:ribbons` and `subsec:junction`,
lines 1747–1757 and 1918–1924. The same native outer domain carries the
actual pulled-back primitives as the base coefficient decreases to zero.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped Manifold ContDiff Topology

namespace FsFltz
open Geometry Geometry.SmoothManifold
variable {n : ℕ}
local instance hittingOuterFamilyCharts : ChartedSpace (Model (2 * n)) (LGSpace n) :=
  (lgManifold n).charts
local instance hittingOuterFamilySmooth : IsManifold 𝓘(ℝ, Model (2 * n)) ∞ (LGSpace n) :=
  (lgManifold n).smooth


/-- A fixed base map and an affine decreasing coefficient give an actual
jointly smooth primitive family on all real parameters. -/
theorem isSmoothFormFamily_rankTwoPrimitive_decreasing {d : ℕ} (M : SmoothManifold d)
    {α : M.Form 1} (hα : M.IsSmoothForm α) {f : M.Point → ℂ}
    (hf : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℂ) ∞ f) (K : ℝ) :
    M.IsSmoothFormFamily (fun t => M.rankTwoPrimitive α f (K * (1 - t))) := by
  intro a
  let c := chartAt (Model d) a
  refine ⟨univ ×ˢ c.target, isOpen_univ.prod c.open_target,
    prod_mono (subset_univ _) Subset.rfl, ?_⟩
  have hs (η : M.Form 1) (hη : M.IsSmoothForm η) :
      ContDiffOn ℝ ∞ (fun p : ℝ × Model d => M.formInChart a η p.2)
        (univ ×ˢ c.target) := (hη a).comp contDiffOn_snd (fun _ hp => hp.2)
  have hk : ContDiffOn ℝ ∞ (fun p : ℝ × Model d => K * (1 - p.1))
      (univ ×ˢ c.target) :=
    contDiffOn_const.mul (contDiffOn_const.sub contDiffOn_fst)
  have h := (hs α hα).add (hk.smul (hs _ (M.isSmoothForm_planePullbackForm hf)))
  apply h.congr
  intro p _
  simp only [rankTwoPrimitive, formInChart_add, formInChart_smul]
  rfl

/-- The actual decreasing coefficient family on the retained native outer
domain, including constructed localized completions. Analytic nondegeneracy
and outwardness remain explicit inputs of this geometric assembly lemma. -/
theorem OuterAmbientInclusionMarkingFamily.exists_hitting_coefficient_family {n : ℕ}
    {Q : PairDeformation n}
    {J : ∀ t, (Q.pair t).ambientDomain.domain.extension.SmoothEmbedding (lgManifold n)}
    {α : Parameter → (lgManifold n).Form 1}
    (I : ToricInput n) {φ : RealSpace n → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (β A K : ℝ) (hK : 0 ≤ K)
    (O : OuterAmbientInclusionMarkingFamily Q J (fun y => φ y.1 - A) α)
    (hboundary : range (O.nativeEmbedding.comp O.domain.boundaryInclusion).map =
      {y | φ y.1 = A})
    (hnd : ∀ k ∈ Icc (0 : ℝ) K, ∀ y,
      (lgManifold n).Nondegenerate ((lgManifold n).exteriorDerivative
        ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ) (tailoringFamily I β 1) k)) y)
    (hout : ∀ k ∈ Icc (0 : ℝ) K, ∀ y, φ y.1 = A →
      0 < (lgManifold n).scalarDerivative (fun z => φ z.1) y
        ((lgManifold n).liouvilleVector
          ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ) (tailoringFamily I β 1) k) y)) :
    ∃ L : Parameter → LiouvilleStructure O.domain,
      (∀ t, (L t).primitive = O.domain.extension.pullback (lgManifold n)
        O.nativeEmbedding.map ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ)
          (tailoringFamily I β 1) (K * (1 - t.val)))) ∧
      O.domain.extension.IsSmoothIntervalFormFamily (fun t => (L t).primitive) ∧
      O.domain.extension.IsSmoothIntervalVectorFieldFamily (fun t => (L t).field) ∧
      (∀ t, O.domain.extension.IsSymplecticOn
        (O.domain.extension.exteriorDerivative (L t).primitive) univ) ∧
      Nonempty (LocalizedCompletionFamily O.domain L) := by
  let a (t : Parameter) := (lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ)
    (tailoringFamily I β 1) (K * (1 - t.val))
  have hk (t : Parameter) : K * (1 - t.val) ∈ Icc (0 : ℝ) K := by
    constructor
    · exact mul_nonneg hK (sub_nonneg.mpr t.property.2)
    · nlinarith [t.property.1]
  have ha : (lgManifold n).IsSmoothIntervalFormFamily a :=
    ⟨_, isSmoothFormFamily_rankTwoPrimitive_decreasing (lgManifold n)
      (isSmoothForm_lambdaPotentialForm hφ) (contMDiff_tailoringFamily_lgManifold I β 1) K,
      fun _ => rfl⟩
  have hq := (contMDiff_potentialValue hφ).sub (contMDiff_const (c := A))
  have hside (_t : Parameter) (x) (hx : x ∈ O.domain.carrier) :
      φ (O.nativeEmbedding.map x).1 - A ≤ 0 := by
    exact (congrArg (fun S => O.nativeEmbedding.map x ∈ S) O.native_image).mp
      (mem_image_of_mem O.nativeEmbedding.map hx)
  have hzero (x) (hx : x ∈ frontier O.domain.carrier) :
      φ (O.nativeEmbedding.map x).1 = A := by
    rw [← O.domain.boundary_range] at hx
    obtain ⟨y, rfl⟩ := hx
    have hy : (O.nativeEmbedding.comp O.domain.boundaryInclusion).map y ∈
        {y | φ y.1 = A} := by
      rw [← hboundary]
      exact mem_range_self y
    exact hy
  obtain ⟨L, hp, hs, hf, hsym, hc, _hmap⟩ :=
    O.domain.exists_liouvilleFamily_of_sublevel_pullback (lgManifold n)
      (fun _ => O.nativeEmbedding)
      (O.domain.extension.isSmoothIntervalMapFamily_constant (lgManifold n)
        O.nativeEmbedding.map O.nativeEmbedding.map.contMDiff)
      a ha (fun t => hnd _ (hk t)) (fun _ y => φ y.1 - A) (fun _ => hq)
      hside (fun _ x hx => sub_eq_zero.mpr (hzero x hx)) (by
        intro t x hx
        have h := hout _ (hk t) _ (hzero x hx)
        let y := O.nativeEmbedding.map x
        let D : (lgManifold n).Tangent y →L[ℝ] ℝ :=
          mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℝ) (fun z : LGSpace n => φ z.1 - A) y
        let Dφ : (lgManifold n).Tangent y →L[ℝ] ℝ :=
          mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℝ) (fun z : LGSpace n => φ z.1) y
        let Dc : (lgManifold n).Tangent y →L[ℝ] ℝ :=
          mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℝ) (fun _ : LGSpace n => A) y
        have he : D = Dφ - Dc :=
          mfderiv_sub ((contMDiff_potentialValue hφ).mdifferentiableAt (x := y) (by simp))
            (mdifferentiableAt_const (I := 𝓘(ℝ, Model (2 * n))) (c := A))
        have hz : Dc = 0 := mfderiv_const
        rw [hz, sub_zero] at he
        have hval := congrArg (fun L : (lgManifold n).Tangent y →L[ℝ] ℝ =>
          L ((lgManifold n).liouvilleVector (a t) y)) he
        exact lt_of_lt_of_eq h hval.symm)
  exact ⟨L, hp, hs, hf, hsym, hc⟩

end FsFltz
