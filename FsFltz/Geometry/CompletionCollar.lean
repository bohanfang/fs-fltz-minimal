import FsFltz.Geometry.CompletionGluing

/-!
# Intrinsic comparisons of completion collars

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 141–158;
`def:chain`, lines 181–189; and `sec:lean`, lines 805–814.

The all-real-time end range of a supplied completion is an open escaping
basin. Its unique end coordinates are a smooth inverse, constructed from
the inverse function theorem. A boundary diffeomorphism therefore produces
an actual radius-preserving smooth comparison of escaping basins, including
negative radii. This is a chosen intrinsic collar comparison, rather than
an assertion about an arbitrary supplied completion presentation.

For an existing compact presentation, extending the comparison for its own
boundary map after shrinking the collar, and making those modifications
coherently in a parameter family, remain separate foundations. An arbitrary
boundary diffeomorphism need not extend to the compact domains. No completion
existence or geometric target is proved here.
-/

noncomputable section
open scoped Manifold ContDiff
open Set Filter Topology

namespace FsFltz.Geometry
open SmoothManifold

namespace Completion

variable {d : ℕ} {D : LiouvilleDomain d} (C : Completion D)

/-- The open union of all end trajectories, at all real flow times. -/
def escapingBasin : TopologicalSpace.Opens C.ambient.manifold.Point :=
  C.endMap_isLocalDiffeomorph.image

/-- The native open submanifold of the escaping basin. -/
def escapingBasinManifold : SmoothManifold d where
  Point := C.escapingBasin
  topology := inferInstance
  charts := inferInstance
  hausdorff := inferInstance
  secondCountable := inferInstance
  smooth := inferInstance

/-- The intrinsic end parametrization with codomain its actual open range. -/
def endInBasin (q : D.domain.boundary.Point × ℝ) : C.escapingBasin :=
  ⟨C.endMap q, ⟨q, rfl⟩⟩

private theorem endInBasin_bijective : Function.Bijective C.endInBasin := by
  constructor
  · intro q p he
    exact C.endMap_injective (congrArg Subtype.val he)
  · rintro ⟨z, q, rfl⟩
    exact ⟨q, rfl⟩

private def endEquiv : (D.domain.boundary.Point × ℝ) ≃ C.escapingBasin :=
  Equiv.ofBijective C.endInBasin C.endInBasin_bijective

/-- The unique intrinsic boundary representative and real radius. -/
def endCoordinates (z : C.escapingBasin) : D.domain.boundary.Point × ℝ :=
  C.endEquiv.symm z

@[simp] theorem endCoordinates_endInBasin (q : D.domain.boundary.Point × ℝ) :
    C.endCoordinates (C.endInBasin q) = q :=
  C.endEquiv.symm_apply_apply q

@[simp] theorem endInBasin_endCoordinates (z : C.escapingBasin) :
    C.endInBasin (C.endCoordinates z) = z :=
  C.endEquiv.apply_symm_apply z

@[simp] theorem endMap_endCoordinates (z : C.escapingBasin) :
    C.endMap (C.endCoordinates z) = z.val :=
  congrArg Subtype.val (C.endInBasin_endCoordinates z)

/-- No regularity of the selected inverse is assumed. Injectivity identifies
it locally with the native inverse-function-theorem inverse. -/
theorem contMDiff_endCoordinates :
    ContMDiff 𝓘(ℝ, Model d)
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) ∞ C.endCoordinates := by
  intro z
  let l := C.endMap_isLocalDiffeomorph (C.endCoordinates z)
  have hi : ContMDiffAt 𝓘(ℝ, Model d)
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) ∞ l.localInverse z.val := by
    rw [← C.endMap_endCoordinates z]
    exact l.localInverse_contMDiffAt
  apply (hi.comp z (contMDiff_subtype_val z)).congr_of_eventuallyEq
  have ht : Tendsto (Subtype.val : C.escapingBasin → C.ambient.manifold.Point)
      (𝓝 z) (𝓝 (C.endMap (C.endCoordinates z))) := by
    rw [C.endMap_endCoordinates]
    exact continuous_subtype_val.continuousAt
  filter_upwards [l.localInverse_eventuallyEq_right.comp_tendsto ht] with y hy
  apply C.endMap_injective
  exact (C.endMap_endCoordinates y).trans hy.symm

/-- The actual complete flow stays in the escaping basin at every real
time. This formula only lifts that existing flow to its open range. -/
def flowInBasin (t : ℝ) (z : C.escapingBasin) : C.escapingBasin :=
  C.endInBasin ((C.endCoordinates z).1, t + (C.endCoordinates z).2)

@[simp] theorem flowInBasin_val (t : ℝ) (z : C.escapingBasin) :
    (C.flowInBasin t z).val = C.ambient.completeFlow.flow t z.val := by
  change C.endMap ((C.endCoordinates z).1, t + (C.endCoordinates z).2) = _
  rw [← C.flow_endMap, Prod.eta, C.endMap_endCoordinates]

@[simp] theorem flowInBasin_endInBasin
    (t : ℝ) (x : D.domain.boundary.Point) (r : ℝ) :
    C.flowInBasin t (C.endInBasin (x, r)) = C.endInBasin (x, t + r) := by
  simp [flowInBasin]

/-- The end parametrization is an actual diffeomorphism onto its open
escaping basin, including the case of an empty zero-dimensional boundary. -/
def endDiffeomorph :
    Diffeomorph ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d)
      (D.domain.boundary.Point × ℝ) C.escapingBasin ∞ where
  __ := C.endEquiv
  contMDiff_toFun :=
    (ContMDiff.subtypeVal_comp_iff C.escapingBasin C.endInBasin).mp C.smooth_endMap
  contMDiff_invFun := C.contMDiff_endCoordinates

@[simp] theorem endDiffeomorph_apply (q : D.domain.boundary.Point × ℝ) :
    C.endDiffeomorph q = C.endInBasin q := rfl

@[simp] theorem endDiffeomorph_symm_apply (z : C.escapingBasin) :
    C.endDiffeomorph.symm z = C.endCoordinates z := rfl

/-- The actual completed primitive restricted to the open escaping basin. -/
def basinPrimitive : C.escapingBasinManifold.Form 1 :=
  C.escapingBasinManifold.pullback C.ambient.manifold Subtype.val C.ambient.primitive

set_option backward.isDefEq.respectTransparency false in
/-- The primitive formula holds in the intrinsic end coordinates at every
real radius, rather than only on the attached nonnegative cylinder. -/
theorem basinPrimitive_endInBasin
    (x : D.domain.boundary.Point) (r : ℝ) (v : Model (d - 1)) (s : ℝ) :
    evalOne C.basinPrimitive (C.endInBasin (x, r))
      (mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d)
        C.endInBasin (x, r) (v, s)) =
      Real.exp r * evalOne (D.domain.boundaryForm D.liouville.primitive) x v := by
  have hs : ContMDiff ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, Model d) ∞ C.endInBasin := C.endDiffeomorph.contMDiff
  have hval : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) ∞
      (Subtype.val : C.escapingBasin → C.ambient.manifold.Point) := contMDiff_subtype_val
  have hd := mfderiv_comp (f := C.endInBasin) (g := Subtype.val) (x, r)
    (hval.mdifferentiableAt (by simp))
    (hs.mdifferentiableAt (by simp))
  change mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d)
      C.endMap (x, r) = _ at hd
  have he := congrArg (fun L => L (v, s)) hd
  change mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d)
      C.endMap (x, r) (v, s) =
    mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d)
      (Subtype.val : C.escapingBasin → C.ambient.manifold.Point) (C.endInBasin (x, r))
      (mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d)
        C.endInBasin (x, r) (v, s)) at he
  change evalOne C.ambient.primitive (C.endMap (x, r))
    (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d)
      (Subtype.val : C.escapingBasin → C.ambient.manifold.Point) (C.endInBasin (x, r))
      (mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d)
        C.endInBasin (x, r) (v, s))) = _
  rw [← he]
  exact C.end_primitive x r v s

variable {e : ℕ} {E : LiouvilleDomain e} (C' : Completion E)

/-- A boundary diffeomorphism produces the radius-preserving intrinsic
comparison of the actual escaping basins. Its smooth inverse is constructed
by the same end-coordinate maps, not supplied as a certificate. -/
def collarComparison (b : D.domain.boundary.SmoothEquiv E.domain.boundary) :
    Diffeomorph 𝓘(ℝ, Model d) 𝓘(ℝ, Model e)
      C.escapingBasin C'.escapingBasin ∞ :=
  (C.endDiffeomorph.symm.trans
    (b.prodCongr (Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞))).trans C'.endDiffeomorph

@[simp] theorem collarComparison_endInBasin
    (b : D.domain.boundary.SmoothEquiv E.domain.boundary)
    (x : D.domain.boundary.Point) (r : ℝ) :
    C.collarComparison C' b (C.endInBasin (x, r)) = C'.endInBasin (b x, r) := by
  simp [collarComparison]

@[simp] theorem endCoordinates_collarComparison
    (b : D.domain.boundary.SmoothEquiv E.domain.boundary) (z : C.escapingBasin) :
    C'.endCoordinates (C.collarComparison C' b z) =
      (b (C.endCoordinates z).1, (C.endCoordinates z).2) := by
  change C'.endCoordinates (C'.endInBasin
    (b (C.endCoordinates z).1, (C.endCoordinates z).2)) = _
  rw [C'.endCoordinates_endInBasin]

/-- The produced radius-preserving comparison intertwines the actual
intrinsic complete flows on the two open escaping basins. -/
theorem collarComparison_flowInBasin
    (b : D.domain.boundary.SmoothEquiv E.domain.boundary)
    (t : ℝ) (z : C.escapingBasin) :
    C.collarComparison C' b (C.flowInBasin t z) =
      C'.flowInBasin t (C.collarComparison C' b z) := by
  simp only [flowInBasin, collarComparison_endInBasin, endCoordinates_collarComparison]

/-- The comparison as an actual map into the target completed manifold. -/
def collarComparisonMap (b : D.domain.boundary.SmoothEquiv E.domain.boundary) :
    C.escapingBasin → C'.ambient.manifold.Point :=
  fun z => (C.collarComparison C' b z).val

theorem contMDiff_collarComparisonMap
    (b : D.domain.boundary.SmoothEquiv E.domain.boundary) :
    ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) ∞ (C.collarComparisonMap C' b) :=
  contMDiff_subtype_val.comp (C.collarComparison C' b).contMDiff

@[simp] theorem collarComparisonMap_endInBasin
    (b : D.domain.boundary.SmoothEquiv E.domain.boundary)
    (x : D.domain.boundary.Point) (r : ℝ) :
    C.collarComparisonMap C' b (C.endInBasin (x, r)) = C'.endMap (b x, r) :=
  congrArg Subtype.val (C.collarComparison_endInBasin C' b x r)

private theorem boundaryProd_mfderiv
    (b : D.domain.boundary.SmoothEquiv E.domain.boundary)
    (x : D.domain.boundary.Point) (r : ℝ) (v : Model (d - 1)) (s : ℝ) :
    mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
      ((𝓘(ℝ, Model (e - 1))).prod 𝓘(ℝ, ℝ))
      (fun q : D.domain.boundary.Point × ℝ => (b q.1, q.2)) (x, r) (v, s) =
      (mfderiv 𝓘(ℝ, Model (d - 1)) 𝓘(ℝ, Model (e - 1)) b x v, s) := by
  change (mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
    ((𝓘(ℝ, Model (e - 1))).prod 𝓘(ℝ, ℝ))
    (fun q => ((b ∘ Prod.fst) q, q.2)) (x, r)) (v, s) = _
  rw [mfderiv_prodMk
    ((b.contMDiff.comp contMDiff_fst).mdifferentiableAt (by simp)) mdifferentiableAt_snd,
    mfderiv_comp (x, r) (b.contMDiff.mdifferentiableAt (by simp)) mdifferentiableAt_fst,
    mfderiv_fst, mfderiv_snd]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The produced comparison has exactly the exponential boundary pullback
coefficients on its whole open escaping basin. An arbitrary boundary
diffeomorphism is not asserted to preserve the primitive. -/
theorem collarComparison_primitive
    (b : D.domain.boundary.SmoothEquiv E.domain.boundary)
    (x : D.domain.boundary.Point) (r : ℝ) (v : Model (d - 1)) (s : ℝ) :
    evalOne (C.escapingBasinManifold.pullback C'.ambient.manifold
        (C.collarComparisonMap C' b) C'.ambient.primitive)
      (C.endInBasin (x, r))
      (mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d)
        C.endInBasin (x, r) (v, s)) = Real.exp r *
      evalOne (D.domain.boundary.pullback E.domain.boundary b
        (E.domain.boundaryForm E.liouville.primitive)) x v := by
  let B : D.domain.boundary.Point × ℝ → E.domain.boundary.Point × ℝ :=
    fun q => (b q.1, q.2)
  have hB : ContMDiff ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
      ((𝓘(ℝ, Model (e - 1))).prod 𝓘(ℝ, ℝ)) ∞ B :=
    (b.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd
  have hs : (C.collarComparisonMap C' b ∘ C.endInBasin) = C'.endMap ∘ B := by
    funext q
    exact C.collarComparisonMap_endInBasin C' b q.1 q.2
  have hEnd : ContMDiff ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, Model d) ∞ C.endInBasin := C.endDiffeomorph.contMDiff
  have hd : mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model e)
      (C.collarComparisonMap C' b ∘ C.endInBasin) (x, r) =
    mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model e)
      (C'.endMap ∘ B) (x, r) := by rw [hs]
  rw [mfderiv_comp (x, r)
      ((C.contMDiff_collarComparisonMap C' b).mdifferentiableAt (by simp))
      (hEnd.mdifferentiableAt (by simp)),
    mfderiv_comp (x, r) (C'.smooth_endMap.mdifferentiableAt (by simp))
      (hB.mdifferentiableAt (by simp))] at hd
  have hdv := congrArg (fun L => L (v, s)) hd
  change mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) (C.collarComparisonMap C' b)
      (C.endInBasin (x, r))
      (mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d)
        C.endInBasin (x, r) (v, s)) =
    mfderiv ((𝓘(ℝ, Model (e - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model e)
      C'.endMap (b x, r)
      (mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
        ((𝓘(ℝ, Model (e - 1))).prod 𝓘(ℝ, ℝ)) B (x, r) (v, s)) at hdv
  rw [boundaryProd_mfderiv b] at hdv
  let a : C'.ambient.manifold.Point → Model e [⋀^Fin 1]→L[ℝ] ℝ := C'.ambient.primitive
  change a
    (C.collarComparisonMap C' b (C.endInBasin (x, r)))
    (fun _ => mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) (C.collarComparisonMap C' b)
      (C.endInBasin (x, r))
      (mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d)
        C.endInBasin (x, r) (v, s))) = _
  rw [hdv, C.collarComparisonMap_endInBasin C' b]
  change evalOne C'.ambient.primitive (C'.endMap (b x, r))
    (mfderiv ((𝓘(ℝ, Model (e - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model e)
      C'.endMap (b x, r)
      (mfderiv 𝓘(ℝ, Model (d - 1)) 𝓘(ℝ, Model (e - 1)) b x v, s)) = _
  rw [C'.end_primitive]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Preservation of the actual boundary primitive is sufficient for the
constructed comparison to preserve the completed primitive on the whole
escaping basin, including its negative-radius part. -/
theorem collarComparison_strict_primitive
    (b : D.domain.boundary.SmoothEquiv E.domain.boundary)
    (hb : D.domain.boundary.pullback E.domain.boundary b
      (E.domain.boundaryForm E.liouville.primitive) =
        D.domain.boundaryForm D.liouville.primitive) :
    C.escapingBasinManifold.pullback C'.ambient.manifold
      (C.collarComparisonMap C' b) C'.ambient.primitive = C.basinPrimitive := by
  funext z
  obtain ⟨⟨x, r⟩, rfl⟩ := C.endDiffeomorph.surjective z
  ext vs
  have hvs : vs = fun _ : Fin 1 => vs 0 := by
    funext i
    rw [Fin.eq_zero i]
  rw [hvs]
  let A := C.endDiffeomorph.mfderivToContinuousLinearEquiv (by simp) (x, r)
  obtain ⟨⟨v, s⟩, he⟩ := A.surjective (vs 0)
  change mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d)
    C.endInBasin (x, r) (v, s) = vs 0 at he
  have ht := C.collarComparison_primitive C' b x r v s
  rw [hb] at ht
  have hs := C.basinPrimitive_endInBasin x r v s
  have hc := ht.trans hs.symm
  change evalOne (C.escapingBasinManifold.pullback C'.ambient.manifold
    (C.collarComparisonMap C' b) C'.ambient.primitive) (C.endInBasin (x, r)) (vs 0) =
    evalOne C.basinPrimitive (C.endInBasin (x, r)) (vs 0)
  rwa [he] at hc

/-- A compact presentation that extends the produced intrinsic collar germ
gives an actual completion presentation. The agreement needed to extend the
chosen germ into the compact interior is an explicit remaining hypothesis;
the collar comparison for this compact presentation's own boundary map and
both of its smooth directions are outputs
of `collarComparison`, not additional input maps. -/
def presentationEquivOfIntrinsicCollar {E : LiouvilleDomain d}
    (C' : Completion E) (h : DomainPresentationEquiv D.domain E.domain)
    (U : Set (D.domain.boundary.Point × ℝ)) (hU : IsOpen U)
    (hpos : univ ×ˢ Ici (0 : ℝ) ⊆ U)
    (hcompact : ∀ q ∈ U, ∀ x ∈ D.domain.carrier,
      C.inclusion.map x = C.endMap q →
      C'.inclusion.map (h.extensionEquiv x) =
        C.collarComparisonMap C' h.boundaryEquiv (C.endInBasin q)) :
    CompletionPresentationEquiv C C' h :=
  C.presentationEquivOfCollar C' h U hU hpos (by
    intro q hq x hx he
    rw [hcompact q hq x hx he]
    exact C.collarComparisonMap_endInBasin C' h.boundaryEquiv q.1 q.2)

end Completion
end FsFltz.Geometry
