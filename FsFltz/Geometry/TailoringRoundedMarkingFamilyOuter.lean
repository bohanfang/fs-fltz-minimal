import FsFltz.Geometry.TailoringRoundedMarkingFamilyAssembly
import FsFltz.Geometry.TailoringPotentialOuterDomainIdentity

/-!
# The actual common outer completion and ambient marking family

Source: `geometric-part-fsf-proof.tex`, actual common marking, lines
1270–1303. Fixed compact data and the proved slice construction produce
one common outer completion family, its actual ambient marking maps, and
their forward and inverse real smooth germs.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz
open Geometry Geometry.SmoothManifold
variable {n : ℕ}
local instance roundedMarkingOuterLGCharts : ChartedSpace (Model (2 * n)) (LGSpace n) :=
  (lgManifold n).charts

/-- Explicit transport of the actual Liouville structure to an equal
native compact domain. -/
def LiouvilleDomain.transportLiouvilleStructure {d : ℕ}
    (D : LiouvilleDomain d) (E : CompactDomain d) (h : D.domain = E) :
    LiouvilleStructure E := h ▸ D.liouville

/-- Transport of a Liouville structure retains its actual primitive up to
the type equality of the ambient extension. -/
theorem LiouvilleDomain.transport_primitive_heq {d : ℕ}
    (D : LiouvilleDomain d) (E : CompactDomain d) (h : D.domain = E) :
    HEq (LiouvilleDomain.transportLiouvilleStructure D E h).primitive D.liouville.primitive := by
  cases h
  exact HEq.rfl

/-- Explicit outer witnesses keep the common native-domain conversions
independent of the pointwise existence proof that supplied those witnesses. -/
theorem tailoringRoundedFamily_exists_commonOuter_marking_realGerms_of_outerData
    (I : ToricInput n) {φ : RealSpace n → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (β Cplus K R : ℝ) (hR : 0 < R) (m : RoundingChoice)
    {E : CompactDomain (2 * n)} {Λ : Parameter → LiouvilleStructure E}
    (ambient : LocalizedCompletionFamily E Λ) (hE : E.carrier.Nonempty)
    (J : Parameter → E.extension.SmoothEmbedding (lgManifold n))
    (hJ : E.extension.IsSmoothIntervalMapFamily (lgManifold n) (fun t => (J t).map))
    (himages : ∀ t : Parameter, (J t).map '' E.carrier =
      tailoringRoundedDomain I φ β t.val R (Cplus ^ 2 * β ^ 2 / 2) m)
    (hcompact : ∀ _t : Parameter,
                  IsCompact {y : LGSpace n | φ y.1 - Cplus ^ 2 * β ^ 2 / 2 ≤ 0})
                (hω : ∀ t : Parameter, (lgManifold n).IsSymplecticOn ((lgManifold n).exteriorDerivative
                  ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ)
                    (tailoringFamily I β t.val) K)) univ)
                (hout : ∀ (t : Parameter) (y : (lgManifold n).Point), φ y.1 - Cplus ^ 2 * β ^ 2 / 2 = 0 →
                  0 < (lgManifold n).scalarDerivative (fun z => φ z.1 - Cplus ^ 2 * β ^ 2 / 2) y
                    ((lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
                      (lambdaPotentialForm φ) (tailoringFamily I β t.val) K) y))
    (hmark : let A := ambient.collars
      ∀ t : Parameter,
              let Outer := tailoringPotentialOuterDomain I hφ β t.val K
                (Cplus ^ 2 * β ^ 2 / 2) (hcompact t) (hω t) (hout t)
              ∀ C : LiouvilleDomain.FlowCollar Outer,
              ∃ (i : (A t).localizedDomain.domain.Point → C.cylindricalCompletion.ambient.manifold.Point)
                (q : InclusionMarking (A t).cylindricalCompletion C.cylindricalCompletion.ambient i),
                (∀ x, C.originalInclusion.map (i x) = (J t).map ((A t).originalInclusion.map x.val)) ∧
                ∀ b r, q.equiv ((A t).cylindricalCompletion.endMap (b, r)) =
                  C.cylindricalCompletion.ambient.completeFlow.flow r
                    (i ⟨(A t).localizedDomain.domain.boundaryInclusion.map b,
                      (A t).localizedDomain.domain.boundaryInclusion_mem_carrier b⟩)) :
    let A := ambient.collars
              ∃ (hcompact : ∀ _t : Parameter,
                  IsCompact {y : LGSpace n | φ y.1 - Cplus ^ 2 * β ^ 2 / 2 ≤ 0})
                (hω : ∀ t : Parameter, (lgManifold n).IsSymplecticOn ((lgManifold n).exteriorDerivative
                  ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ)
                    (tailoringFamily I β t.val) K)) univ)
                (hout : ∀ (t : Parameter) (y : (lgManifold n).Point), φ y.1 - Cplus ^ 2 * β ^ 2 / 2 = 0 →
                  0 < (lgManifold n).scalarDerivative (fun z => φ z.1 - Cplus ^ 2 * β ^ 2 / 2) y
                    ((lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
                      (lambdaPotentialForm φ) (tailoringFamily I β t.val) K) y)),
              let Outer := fun (t : Parameter) => tailoringPotentialOuterDomain I hφ β t.val K
                (Cplus ^ 2 * β ^ 2 / 2) (hcompact t) (hω t) (hout t)
              let H := regularSublevelCompactDomain (lgManifold n)
                (fun y => φ y.1 - Cplus ^ 2 * β ^ 2 / 2)
                ((contMDiff_potentialValue hφ).sub contMDiff_const) (hcompact parameterZero)
                (regular_zero_of_scalarDerivative_pos (lgManifold n)
                  (fun y => φ y.1 - Cplus ^ 2 * β ^ 2 / 2)
                  ((lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
                    (lambdaPotentialForm φ) (tailoringFamily I β parameterZero.val) K)) (hout parameterZero))
              let domainEq := fun (t : Parameter) => tailoringPotentialOuterDomain_domain I hφ
                β t.val K (Cplus ^ 2 * β ^ 2 / 2) (hcompact t) (hω t) (hout t)
              let μ : Parameter → LiouvilleStructure H := fun t =>
                LiouvilleDomain.transportLiouvilleStructure (Outer t) H (domainEq t)
              ∃ (outer : LocalizedCompletionFamily H μ)
                (i : ∀ t, (A t).localizedDomain.domain.Point →
                  (outer.collars t).cylindricalCompletion.ambient.manifold.Point)
                (q : ∀ t, InclusionMarking (A t).cylindricalCompletion
                  (outer.collars t).cylindricalCompletion.ambient (i t)),
                (∀ t x, (outer.collars t).originalInclusion.map (i t x) =
                  (J t).map ((A t).originalInclusion.map x.val)) ∧
                (∀ t b r, (q t).equiv ((A t).cylindricalCompletion.endMap (b, r)) =
                  (outer.collars t).cylindricalCompletion.ambient.completeFlow.flow r
                    (i t ⟨(A t).localizedDomain.domain.boundaryInclusion.map b,
                      (A t).localizedDomain.domain.boundaryInclusion_mem_carrier b⟩)) ∧
                let M := (A parameterZero).cylindricalCompletion.ambient.manifold
                let N := (outer.collars parameterZero).cylindricalCompletion.ambient.manifold
                let f := fun t => ((ambient.completionPresentation t).equiv.trans (q t).equiv).trans
                  (outer.completionPresentation t).equiv.symm
                IntrinsicSmoothBundle.HasSmoothManifoldTargetFamilyOn M N univ (fun t => f t) ∧
                  IntrinsicSmoothBundle.HasSmoothManifoldTargetFamilyOn N M univ (fun t => (f t).symm) := by  classical
  dsimp only at hmark ⊢
  let A := ambient.collars
  let Outer := fun (t : Parameter) => tailoringPotentialOuterDomain I hφ β t.val K
    (Cplus ^ 2 * β ^ 2 / 2) (hcompact t) (hω t) (hout t)
  let H := regularSublevelCompactDomain (lgManifold n)
    (fun y => φ y.1 - Cplus ^ 2 * β ^ 2 / 2)
    ((contMDiff_potentialValue hφ).sub contMDiff_const) (hcompact parameterZero)
    (regular_zero_of_scalarDerivative_pos (lgManifold n)
      (fun y => φ y.1 - Cplus ^ 2 * β ^ 2 / 2)
      ((lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
        (lambdaPotentialForm φ) (tailoringFamily I β parameterZero.val) K)) (hout parameterZero))
  let domainEq := fun (t : Parameter) => tailoringPotentialOuterDomain_domain I hφ
    β t.val K (Cplus ^ 2 * β ^ 2 / 2) (hcompact t) (hω t) (hout t)
  let μ : Parameter → LiouvilleStructure H := fun t =>
                LiouvilleDomain.transportLiouvilleStructure (Outer t) H (domainEq t)
  have hμprimitive (t : Parameter) : (μ t).primitive =
      (lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ) (tailoringFamily I β t.val) K := by
    exact eq_of_heq (LiouvilleDomain.transport_primitive_heq (Outer t) H (domainEq t))
  have hμsmooth : H.extension.IsSmoothIntervalFormFamily (fun t => (μ t).primitive) := by
    exact ⟨fun s => (lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ)
      (tailoringFamily I β s) K, isSmoothFormFamily_tailoringPrimitive I β K hφ,
      fun t => (hμprimitive t).symm⟩
  obtain ⟨outer⟩ := H.exists_smooth_localizedCompletionFamily_of_liouvilleFamily μ hμsmooth
  have hH : H.carrier.Nonempty := by
    obtain ⟨x, hx⟩ := hE
    have hy := himages parameterZero ▸
      (show (J parameterZero).map x ∈ (J parameterZero).map '' E.carrier from ⟨x, hx, rfl⟩)
    have hbound := (tailoringRoundedDomain_subset I φ β parameterZero.val
      (Cplus ^ 2 * β ^ 2 / 2) hR m hy).1
    exact ⟨(J parameterZero).map x, sub_nonpos.mpr hbound⟩
  have hmarks : ∀ t : Parameter,
      ∃ (i : (A t).localizedDomain.domain.Point →
          (outer.collars t).cylindricalCompletion.ambient.manifold.Point)
        (q : InclusionMarking (A t).cylindricalCompletion
          (outer.collars t).cylindricalCompletion.ambient i),
        (∀ x, (outer.collars t).originalInclusion.map (i x) =
          (J t).map ((A t).originalInclusion.map x.val)) ∧
        ∀ b r, q.equiv ((A t).cylindricalCompletion.endMap (b, r)) =
          (outer.collars t).cylindricalCompletion.ambient.completeFlow.flow r
            (i ⟨(A t).localizedDomain.domain.boundaryInclusion.map b,
              (A t).localizedDomain.domain.boundaryInclusion_mem_carrier b⟩) := by
    intro t
    exact hmark t (outer.collars t)
  obtain ⟨i, hi⟩ := Classical.axiom_of_choice hmarks
  obtain ⟨q, hq⟩ := Classical.axiom_of_choice hi
  have hsquare := fun t => (hq t).1
  have hend := fun t => (hq t).2
  have hqcompact : ∀ t x, x ∈ (A t).localizedDomain.domain.carrier →
      (outer.collars t).originalInclusion.map ((q t).equiv x) =
        (J t).map ((A t).originalInclusion.map x) := by
    intro t x hx
    have he := (q t).inclusion ⟨x, hx⟩
    change (q t).equiv x = i t ⟨x, hx⟩ at he
    rw [he]
    exact hsquare t ⟨x, hx⟩
  have hregular := ambient.markingFamily_realGerms_of_original_square outer hH
    (fun t => (J t).map) hJ (fun t => (q t).equiv) (fun t => (q t).primitive) hqcompact
  exact ⟨hcompact, hω, hout, outer, i, q, hsquare, hend, hregular⟩

/-- The proved actual slice construction supplies the explicit outer data;
the common outer family and actual smooth markings are then constructed. -/
theorem tailoringRoundedFamily_exists_commonOuter_marking_realGerms
    (I : ToricInput n) {φ : RealSpace n → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (β Cplus K R : ℝ) (hR : 0 < R) (m : RoundingChoice)
    {E : CompactDomain (2 * n)} {Λ : Parameter → LiouvilleStructure E}
    (ambient : LocalizedCompletionFamily E Λ) (hE : E.carrier.Nonempty)
    (J : Parameter → E.extension.SmoothEmbedding (lgManifold n))
    (hJ : E.extension.IsSmoothIntervalMapFamily (lgManifold n) (fun t => (J t).map))
    (himages : ∀ t : Parameter, (J t).map '' E.carrier =
      tailoringRoundedDomain I φ β t.val R (Cplus ^ 2 * β ^ 2 / 2) m)
    (hdata : let A := ambient.collars
      ∀ t : Parameter,
              ∃ (hcompact : IsCompact {y : LGSpace n | φ y.1 - Cplus ^ 2 * β ^ 2 / 2 ≤ 0})
                (hω : (lgManifold n).IsSymplecticOn ((lgManifold n).exteriorDerivative
                  ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ)
                    (tailoringFamily I β t.val) K)) univ)
                (hout : ∀ y : (lgManifold n).Point, φ y.1 - Cplus ^ 2 * β ^ 2 / 2 = 0 →
                  0 < (lgManifold n).scalarDerivative (fun z => φ z.1 - Cplus ^ 2 * β ^ 2 / 2) y
                    ((lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
                      (lambdaPotentialForm φ) (tailoringFamily I β t.val) K) y)),
              let Outer := tailoringPotentialOuterDomain I hφ β t.val K
                (Cplus ^ 2 * β ^ 2 / 2) hcompact hω hout
              ∀ C : LiouvilleDomain.FlowCollar Outer,
              ∃ (i : (A t).localizedDomain.domain.Point → C.cylindricalCompletion.ambient.manifold.Point)
                (q : InclusionMarking (A t).cylindricalCompletion C.cylindricalCompletion.ambient i),
                (∀ x, C.originalInclusion.map (i x) = (J t).map ((A t).originalInclusion.map x.val)) ∧
                ∀ b r, q.equiv ((A t).cylindricalCompletion.endMap (b, r)) =
                  C.cylindricalCompletion.ambient.completeFlow.flow r
                    (i ⟨(A t).localizedDomain.domain.boundaryInclusion.map b,
                      (A t).localizedDomain.domain.boundaryInclusion_mem_carrier b⟩)) :
    let A := ambient.collars
              ∃ (hcompact : ∀ _t : Parameter,
                  IsCompact {y : LGSpace n | φ y.1 - Cplus ^ 2 * β ^ 2 / 2 ≤ 0})
                (hω : ∀ t : Parameter, (lgManifold n).IsSymplecticOn ((lgManifold n).exteriorDerivative
                  ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ)
                    (tailoringFamily I β t.val) K)) univ)
                (hout : ∀ (t : Parameter) (y : (lgManifold n).Point), φ y.1 - Cplus ^ 2 * β ^ 2 / 2 = 0 →
                  0 < (lgManifold n).scalarDerivative (fun z => φ z.1 - Cplus ^ 2 * β ^ 2 / 2) y
                    ((lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
                      (lambdaPotentialForm φ) (tailoringFamily I β t.val) K) y)),
              let Outer := fun (t : Parameter) => tailoringPotentialOuterDomain I hφ β t.val K
                (Cplus ^ 2 * β ^ 2 / 2) (hcompact t) (hω t) (hout t)
              let H := regularSublevelCompactDomain (lgManifold n)
                (fun y => φ y.1 - Cplus ^ 2 * β ^ 2 / 2)
                ((contMDiff_potentialValue hφ).sub contMDiff_const) (hcompact parameterZero)
                (regular_zero_of_scalarDerivative_pos (lgManifold n)
                  (fun y => φ y.1 - Cplus ^ 2 * β ^ 2 / 2)
                  ((lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
                    (lambdaPotentialForm φ) (tailoringFamily I β parameterZero.val) K)) (hout parameterZero))
              let domainEq := fun (t : Parameter) => tailoringPotentialOuterDomain_domain I hφ
                β t.val K (Cplus ^ 2 * β ^ 2 / 2) (hcompact t) (hω t) (hout t)
              let μ : Parameter → LiouvilleStructure H := fun t =>
                LiouvilleDomain.transportLiouvilleStructure (Outer t) H (domainEq t)
              ∃ (outer : LocalizedCompletionFamily H μ)
                (i : ∀ t, (A t).localizedDomain.domain.Point →
                  (outer.collars t).cylindricalCompletion.ambient.manifold.Point)
                (q : ∀ t, InclusionMarking (A t).cylindricalCompletion
                  (outer.collars t).cylindricalCompletion.ambient (i t)),
                (∀ t x, (outer.collars t).originalInclusion.map (i t x) =
                  (J t).map ((A t).originalInclusion.map x.val)) ∧
                (∀ t b r, (q t).equiv ((A t).cylindricalCompletion.endMap (b, r)) =
                  (outer.collars t).cylindricalCompletion.ambient.completeFlow.flow r
                    (i t ⟨(A t).localizedDomain.domain.boundaryInclusion.map b,
                      (A t).localizedDomain.domain.boundaryInclusion_mem_carrier b⟩)) ∧
                let M := (A parameterZero).cylindricalCompletion.ambient.manifold
                let N := (outer.collars parameterZero).cylindricalCompletion.ambient.manifold
                let f := fun t => ((ambient.completionPresentation t).equiv.trans (q t).equiv).trans
                  (outer.completionPresentation t).equiv.symm
                IntrinsicSmoothBundle.HasSmoothManifoldTargetFamilyOn M N univ (fun t => f t) ∧
                  IntrinsicSmoothBundle.HasSmoothManifoldTargetFamilyOn N M univ (fun t => (f t).symm) := by
  classical
  dsimp only at hdata ⊢
  obtain ⟨hcompact, hcompactSpec⟩ := Classical.axiom_of_choice hdata
  obtain ⟨hω, hωSpec⟩ := Classical.axiom_of_choice hcompactSpec
  obtain ⟨hout, hmark⟩ := Classical.axiom_of_choice hωSpec
  exact tailoringRoundedFamily_exists_commonOuter_marking_realGerms_of_outerData I hφ
    β Cplus K R hR m ambient hE J hJ himages hcompact hω hout hmark

end FsFltz
