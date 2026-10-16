import FsFltz.Geometry.IntrinsicBundleLocalCompletionOriginalComparison
import FsFltz.Geometry.IntrinsicNativeCompletionFamilyInverseGerms

/-!
# Real inverse germs of original local completion comparisons

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 163–199, and
`sec:lean`, lines 788–814. The inverse is the inverse of the same strict
slice comparisons used by `ambientReferenceTotalMap`, on the same original
local base. Its real germs take values in the original interior or signed
cylinder patch, so the real parameter extends across both interval endpoints.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Bundle Topology
open FsFltz.Geometry.IntrinsicLiouville
open FsFltz.Geometry.IntrinsicCompletionGluing

namespace FsFltz.Geometry.IntrinsicCompletionGluing

/-- Real-open spatial patch germs of an actual inverse into the original
completion family. The real parameter is free; only its interval values
are inserted into the retained total family. -/
def HasRealOpenPatchInverseGerms {k d : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M]
    [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
    [IsManifold (𝓡∂ (k + 1)) ∞ M] {δ : ℝ}
    (C : Parameter → Half δ (IntrinsicBoundary.Point k M) → M)
    (N : SmoothManifold d) (S : Set Parameter) (f : S × N.Point → TotalSpace C) : Prop :=
  ∀ (s : S) y,
    (∃ U : TopologicalSpace.Opens (ℝ × N.Point), (s.val.val, y) ∈ U ∧
      ∃ γ : U → IntrinsicInterior.Point k M,
        ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model (k + 1)) ∞ γ ∧
        ∀ (v : S) z (h : (v.val.val, z) ∈ U),
          f (v, z) = totalInterior C (v.val, γ ⟨(v.val.val, z), h⟩)) ∨
    (∃ U : TopologicalSpace.Opens (ℝ × N.Point), (s.val.val, y) ∈ U ∧
      ∃ γ : U → IntrinsicBoundary.Point k M × ℝ,
        ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
          ((𝓘(ℝ, Model k)).prod 𝓘(ℝ, ℝ)) ∞ γ ∧
        (∀ z : U, -(γ z).2 < δ) ∧
        ∀ (v : S) z (h : (v.val.val, z) ∈ U),
          ∃ p : Band δ (IntrinsicBoundary.Point k M),
            p.val = (-(γ ⟨(v.val.val, z), h⟩).2, (γ ⟨(v.val.val, z), h⟩).1) ∧
            f (v, z) = totalCylinder C (v.val, p))

end FsFltz.Geometry.IntrinsicCompletionGluing

namespace FsFltz.Geometry.IntrinsicSmoothBundle.LocalCompletionFamily

variable {k n : ℕ} [NeZero n] {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  {E : Parameter → Type*} [∀ s, TopologicalSpace (E s)]
  [TopologicalSpace (Bundle.TotalSpace M E)]
  [SmoothCompactBundle (𝓡∂ (k + 1)) (F := M) E]
  {P : BundlePrimitiveData (k := k) (M := M) E}
  {c : OriginalCompactChart (k := k) (M := M) (E := E)} {t : Parameter}

variable (F : LocalCompletionFamily P c t) (L : OriginalBundleLiouvilleLaws P)
  (g : Trivialization M (π M E)) (hg : CompatibleTrivialization (𝓡∂ (k + 1)) E g)
  (hbase : g.baseSet = univ) (Q : PairDeformation n) (hdim : k + 1 = 2 * n)
  (eAs : ∀ s, Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n)) M
    (Q.pair s).ambientDomain.domain.Point ∞)
  (hp : ∀ s x, ((Q.pair s).ambientDomain.liouville.primitive (eAs s x).val).compContinuousLinearMap
    (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n)) (fun y => (eAs s y).val) x) =
      P.formInTrivialization g s x)
  (hc : ∀ s, HasNativeCoordinateExtensions (k := k)
    (Q.pair s).ambientDomain.domain.extension (fun x => (eAs s x).val))

/-- The actual inverse comparison, with values in the retained total quotient.
Its parameter is supplied in the original local base, never extended by choice. -/
def ambientReferenceTotalInverse : F.base × Q.source.ambientCompletion.ambient.manifold.Point →
    F.localSource := fun z =>
  ⟨sliceIn F.native.patches z.1.val
    ((F.ambientSourceSliceEquiv L g z.1.val Q eAs
      (F.ambientEndpointSliceComparison L g hg hbase z.1.val z.1.property Q hdim eAs hp hc)).symm
        z.2), by simpa only [localSource, Set.mem_preimage,
      TopologicalSpace.Opens.mem_mk, parameter_sliceIn] using z.1.property⟩

@[simp] theorem ambientReferenceTotalInverse_parameter
    (s : F.base) (y : Q.source.ambientCompletion.ambient.manifold.Point) :
    parameter F.native.patches
      (F.ambientReferenceTotalInverse L g hg hbase Q hdim eAs hp hc (s, y)).val = s.val :=
  parameter_sliceIn _ _ _

@[simp] theorem ambientReferenceTotalMap_inverse
    (s : F.base) (y : Q.source.ambientCompletion.ambient.manifold.Point) :
    F.ambientReferenceTotalMap L g hg hbase Q hdim eAs hp hc
      (F.ambientReferenceTotalInverse L g hg hbase Q hdim eAs hp hc (s, y)) = y := by
  rw [ambientReferenceTotalInverse,
    F.ambientReferenceTotalMap_slice L g hg hbase Q hdim eAs hp hc]
  exact Diffeomorph.apply_symm_apply _ y

@[simp] theorem ambientReferenceTotalInverse_map (z : F.localSource) :
    F.ambientReferenceTotalInverse L g hg hbase Q hdim eAs hp hc
      (⟨parameter F.native.patches z.val, z.property⟩,
        F.ambientReferenceTotalMap L g hg hbase Q hdim eAs hp hc z) = z := by
  apply Subtype.ext
  change sliceIn F.native.patches (parameter F.native.patches z.val)
    ((F.ambientSourceSliceEquiv L g _ Q eAs
      (F.ambientEndpointSliceComparison L g hg hbase _ z.property Q hdim eAs hp hc)).symm
        ((F.ambientSourceSliceEquiv L g _ Q eAs
          (F.ambientEndpointSliceComparison L g hg hbase _ z.property Q hdim eAs hp hc))
            ((fiberEquiv F.native.patches _).symm ⟨z.val, rfl⟩))) = z.val
  rw [Diffeomorph.symm_apply_apply]
  exact congrArg Subtype.val ((fiberEquiv F.native.patches _).apply_symm_apply ⟨z.val, rfl⟩)

/-- The parameter-retaining equivalence uses exactly the original forward
total map and the inverses of its strict slices. -/
def ambientReferenceTotalEquiv : F.localSource ≃
    F.base × Q.source.ambientCompletion.ambient.manifold.Point where
  toFun z := (⟨parameter F.native.patches z.val, z.property⟩,
    F.ambientReferenceTotalMap L g hg hbase Q hdim eAs hp hc z)
  invFun := F.ambientReferenceTotalInverse L g hg hbase Q hdim eAs hp hc
  left_inv := F.ambientReferenceTotalInverse_map L g hg hbase Q hdim eAs hp hc
  right_inv z := Prod.ext (Subtype.ext (F.ambientReferenceTotalInverse_parameter
    L g hg hbase Q hdim eAs hp hc z.1 z.2))
      (F.ambientReferenceTotalMap_inverse L g hg hbase Q hdim eAs hp hc z.1 z.2)

/-- The inverse compact equation retains the actual reverse original chart change. -/
theorem ambientReferenceTotalInverse_compact (s : F.base) (x : M) :
    (F.ambientReferenceTotalInverse L g hg hbase Q hdim eAs hp hc
      (s, Q.ambientNativeReferenceMap eAs s.val x)).val =
        original (totalCollar F.native.patches) (s.val, g.coordChange c.val s.val x) := by
  change sliceIn F.native.patches s.val
    ((F.ambientSourceSliceEquiv L g s.val Q eAs
      (F.ambientEndpointSliceComparison L g hg hbase s.val s.property Q hdim eAs hp hc)).symm
        (Q.ambientNativeReferenceMap eAs s.val x)) = _
  rw [PairDeformation.ambientNativeReferenceMap,
    F.ambientSourceSliceEquiv_compact_inverse L g s.val Q eAs,
    sliceIn_original]

end FsFltz.Geometry.IntrinsicSmoothBundle.LocalCompletionFamily

namespace FsFltz.Geometry.IntrinsicSmoothBundle.LocalCompletionFamily

variable {k n : ℕ} [NeZero n] {M : Type} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]
  {E : Parameter → Type*} [∀ s, TopologicalSpace (E s)]
  [TopologicalSpace (Bundle.TotalSpace M E)]
  [SmoothCompactBundle (𝓡∂ (k + 1)) (F := M) E]
  {P : BundlePrimitiveData (k := k) (M := M) E}
  {c : OriginalCompactChart (k := k) (M := M) (E := E)} {t : Parameter}

variable (F : LocalCompletionFamily P c t) (L : OriginalBundleLiouvilleLaws P)
  (g : Trivialization M (π M E)) (hg : CompatibleTrivialization (𝓡∂ (k + 1)) E g)
  (hbase : g.baseSet = univ) (Q : PairDeformation n) (hdim : k + 1 = 2 * n)
  (eAs : ∀ s, Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n)) M
    (Q.pair s).ambientDomain.domain.Point ∞)
  (hp : ∀ s x, ((Q.pair s).ambientDomain.liouville.primitive (eAs s x).val).compContinuousLinearMap
    (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n)) (fun y => (eAs s y).val) x) =
      P.formInTrivialization g s x)
  (hc : ∀ s, HasNativeCoordinateExtensions (k := k)
    (Q.pair s).ambientDomain.domain.extension (fun x => (eAs s x).val))

/-- The actual reverse ordered boundary transition of the original compact bundle. -/
abbrev referenceBoundaryReverseTransition (_F : LocalCompletionFamily P c t) :=
  boundaryFamilyOn (g.baseSet ∩ c.val.baseSet) (g.coordChange c.val)
    (compatibleTransition_boundary g c.val hg (compatibleTrivialization_of_mem c.property))

include hbase in
omit [T2Space M] [SecondCountableTopology M] [IsManifold (𝓡∂ (k + 1)) ∞ M] in
theorem referenceBoundaryTransition_reverse (s : F.base) (x : IntrinsicBoundary.Point k M) :
    F.referenceBoundaryTransition g hg s.val
      (F.referenceBoundaryReverseTransition g hg s.val x) = x := by
  apply Subtype.ext
  rw [boundaryFamilyOn_val _ (F.base_subset_globalOverlap g hbase s.val s.property),
    boundaryFamilyOn_val _ (show s.val ∈ g.baseSet ∩ c.val.baseSet from
      ⟨by rw [hbase]; exact mem_univ _, F.base_subset s.property⟩),
    g.coordChange_coordChange c.val g
      (by rw [hbase]; exact mem_univ _) (F.base_subset s.property),
    g.coordChange_same (by rw [hbase]; exact mem_univ _)]
  rfl

/-- The inverse signed-cylinder formula reverses the original boundary map,
retaining every radius below the unchanged native width. -/
theorem ambientReferenceTotalInverse_cylinder
    (eBs : ∀ u, (IntrinsicBoundary.smoothManifold k M).SmoothEquiv
      (Q.pair u).ambientDomain.domain.boundary)
    (hb : ∀ u b, (Q.pair u).ambientDomain.domain.boundaryInclusion.map (eBs u b) =
      (eAs u b.val).val)
    (hsquareB : ∀ u b, (Q.ambientPresentation u).boundaryEquiv (eBs parameterZero b) = eBs u b)
    (s : F.base) (b : IntrinsicBoundary.Point k M) (r : ℝ) (hr : -r < F.native.width) :
    (F.ambientReferenceTotalInverse L g hg hbase Q hdim eAs hp hc
      (s, (Q.ambientCompletionPresentation s.val).prescribedEndMap
        (eBs parameterZero b, r))).val =
      totalCylinder F.native.patches
        (s.val, ⟨(-r, F.referenceBoundaryReverseTransition g hg s.val b), hr, mem_univ _⟩) := by
  let p : Band F.native.width (IntrinsicBoundary.Point k M) :=
    ⟨(-r, F.referenceBoundaryReverseTransition g hg s.val b), hr, mem_univ _⟩
  let z : F.localSource := ⟨totalCylinder F.native.patches (s.val, p), s.property⟩
  have hz : F.ambientReferenceTotalMap L g hg hbase Q hdim eAs hp hc z =
      (Q.ambientCompletionPresentation s.val).prescribedEndMap (eBs parameterZero b, r) := by
    rw [F.ambientReferenceTotalMap_cylinder L g hg hbase Q hdim eAs hp hc eBs hb hsquareB]
    change (Q.ambientCompletionPresentation s.val).prescribedEndMap
      (eBs parameterZero (F.referenceBoundaryTransition g hg s.val
        (F.referenceBoundaryReverseTransition g hg s.val b)), -(-r)) = _
    rw [F.referenceBoundaryTransition_reverse g hg hbase, neg_neg]
  have h := F.ambientReferenceTotalInverse_map L g hg hbase Q hdim eAs hp hc z
  simpa only [hz, z, parameter_totalCylinder] using congrArg Subtype.val h

/-- Real-open germs of the exact inverse above the fixed compact interior.
The two original inverse coordinate operations are composed with the
local inverse of the fixed reference inclusion. -/
theorem ambientReferenceTotalInverse_realInteriorGerm
    (R : ℝ → Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M M ∞)
    (hR : IsJointlySmoothDiffeomorphFamily (𝓡∂ (k + 1)) R)
    (hsquareA : ∀ s x, (Q.ambientPresentation s).extensionEquiv
      (eAs parameterZero (R s.val x)).val = (eAs s x).val)
    (s : F.base) (u : IntrinsicInterior.Point k M) :
    ∃ U : TopologicalSpace.Opens (ℝ × Q.source.ambientCompletion.ambient.manifold.Point),
      (s.val.val, Q.ambientNativeInteriorReferenceMap (eAs parameterZero) u) ∈ U ∧
      ∃ γ : U → IntrinsicInterior.Point k M,
        ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))) 𝓘(ℝ, Model (k + 1)) ∞ γ ∧
        ∀ (v : F.base) y (h : (v.val.val, y) ∈ U),
          (F.ambientReferenceTotalInverse L g hg hbase Q hdim eAs hp hc (v, y)).val =
            totalInterior F.native.patches (v.val, γ ⟨(v.val.val, y), h⟩) := by
  let f := Q.ambientNativeInteriorReferenceMap (eAs parameterZero)
  let l := Q.isLocalDiffeomorph_ambientNativeInteriorReferenceMap hdim (eAs parameterZero) u
  let ri : ℝ × IntrinsicInterior.Point k M → IntrinsicInterior.Point k M :=
    fun z => ⟨(R z.1).symm z.2.val,
      (IsLocalDiffeomorphAt.isInteriorPoint_iff (by simp)
        ((R z.1).symm.isLocalDiffeomorph z.2.val)).mp z.2.property⟩
  have hri : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (k + 1)))
      𝓘(ℝ, Model (k + 1)) ∞ ri := by
    apply IntrinsicInterior.contMDiff_iff_val.mpr
    exact hR.2.comp (contMDiff_id.prodMap IntrinsicInterior.contMDiff_val)
  let W : Set (ℝ × Q.source.ambientCompletion.ambient.manifold.Point) :=
    Prod.snd ⁻¹' l.localInverse.source
  have hW : IsOpen W := l.localInverse.open_source.preimage continuous_snd
  let q : ℝ × Q.source.ambientCompletion.ambient.manifold.Point →
      ℝ × IntrinsicInterior.Point k M := fun z => (z.1, ri (z.1, l.localInverse z.2))
  have hq : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n)))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (k + 1))) ∞ q W :=
    contMDiffOn_fst.prodMk (hri.comp_contMDiffOn
      (contMDiffOn_fst.prodMk
        (l.localInverse_contMDiffOn.comp contMDiffOn_snd (fun _ hz => hz))))
  have hs : s.val ∈ g.baseSet ∩ c.val.baseSet :=
    ⟨by rw [hbase]; exact mem_univ _, F.base_subset s.property⟩
  obtain ⟨V, hpV, η, hη, heη⟩ :=
    compatibleTransition_interior_germs g c.val hg
      (compatibleTrivialization_of_mem c.property) s.val hs (ri (s.val.val, u))
  let U : TopologicalSpace.Opens (ℝ × Q.source.ambientCompletion.ambient.manifold.Point) :=
    ⟨W ∩ q ⁻¹' V, hq.continuousOn.isOpen_inter_preimage hW V.isOpen⟩
  let qU : U → V := fun z => ⟨q z.val, z.property.2⟩
  have hqU : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n)))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (k + 1))) ∞ qU := by
    apply (ContMDiff.subtypeVal_comp_iff V qU).mp
    intro z
    exact (hq.contMDiffAt (hW.mem_nhds z.property.1)).comp z
      contMDiff_subtype_val.contMDiffAt
  refine ⟨U, ?_, η ∘ qU, hη.comp hqU, ?_⟩
  · refine ⟨l.localInverse_mem_source, ?_⟩
    change (s.val.val, ri (s.val.val, l.localInverse (f u))) ∈ V
    rw [l.localInverse_left_inv l.localInverse_mem_target]
    exact hpV
  · intro v y hy
    let z := ri (v.val.val, l.localInverse y)
    have hv : v.val ∈ g.baseSet ∩ c.val.baseSet :=
      ⟨by rw [hbase]; exact mem_univ _, F.base_subset v.property⟩
    have hηeq := heη v.val hv z hy.2
    have hnative : Q.ambientNativeReferenceMap eAs v.val z.val = y := by
      rw [Q.ambientNativeReferenceMap_eq_compact eAs R hsquareA]
      change Q.source.ambientCompletion.inclusion.map
        (eAs parameterZero (R v.val.val ((R v.val.val).symm (l.localInverse y).val))).val = y
      rw [(R v.val.val).apply_symm_apply]
      exact l.localInverse_right_inv hy.1
    calc
      _ = (F.ambientReferenceTotalInverse L g hg hbase Q hdim eAs hp hc
          (v, Q.ambientNativeReferenceMap eAs v.val z.val)).val :=
        congrArg (fun y => (F.ambientReferenceTotalInverse L g hg hbase Q hdim eAs hp hc
          (v, y)).val) hnative.symm
      _ = original (totalCollar F.native.patches)
          (v.val, g.coordChange c.val v.val z.val) :=
        F.ambientReferenceTotalInverse_compact L g hg hbase Q hdim eAs hp hc v z.val
      _ = _ := ?_
    change original (totalCollar F.native.patches)
      (v.val, g.coordChange c.val v.val z.val) =
        original (totalCollar F.native.patches) (v.val, (η (qU ⟨(v.val.val, y), hy⟩)).val)
    congr 1
    refine Prod.ext ?_ ?_
    · rfl
    exact (congrArg Subtype.val hηeq).trans (interiorFamilyOn_val _ hv z) |>.symm

/-- At every nonnegative reference radius the same total inverse has a
real-open signed-cylinder germ. The inverse function theorem applies to
the prescribed end extension; the original reverse boundary germs then
return to the unchanged local cylinder. -/
theorem ambientReferenceTotalInverse_realEndGerm
    (eBs : ∀ u, (IntrinsicBoundary.smoothManifold k M).SmoothEquiv
      (Q.pair u).ambientDomain.domain.boundary)
    (hb : ∀ u b, (Q.pair u).ambientDomain.domain.boundaryInclusion.map (eBs u b) =
      (eAs u b.val).val)
    (hsquareB : ∀ u b, (Q.ambientPresentation u).boundaryEquiv (eBs parameterZero b) = eBs u b)
    (s : F.base) (b : IntrinsicBoundary.Point k M) (r : ℝ) (hr : 0 ≤ r) :
    ∃ U : TopologicalSpace.Opens (ℝ × Q.source.ambientCompletion.ambient.manifold.Point),
      (s.val.val, Q.source.ambientCompletion.endMap (eBs parameterZero b, r)) ∈ U ∧
      ∃ γ : U → IntrinsicBoundary.Point k M × ℝ,
        ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n)))
          ((𝓘(ℝ, Model k)).prod 𝓘(ℝ, ℝ)) ∞ γ ∧
        (∀ z : U, -(γ z).2 < F.native.width) ∧
        ∀ (v : F.base) y (h : (v.val.val, y) ∈ U),
          ∃ p : Band F.native.width (IntrinsicBoundary.Point k M),
            p.val = (-(γ ⟨(v.val.val, y), h⟩).2, (γ ⟨(v.val.val, y), h⟩).1) ∧
            (F.ambientReferenceTotalInverse L g hg hbase Q hdim eAs hp hc (v, y)).val =
              totalCylinder F.native.patches (v.val, p) := by
  obtain ⟨a, ha, β₀, hβ₀, heβ₀⟩ :=
    Q.source.ambientCompletion.exists_prescribedFamily_end_strip_extension
      (fun u => (Q.pair u).ambientDomain) (fun u => (Q.pair u).ambientCompletion)
      Q.ambientPresentation Q.ambientCompletionPresentation Q.completedAmbientPrimitive_smooth
  let β : ℝ → IntrinsicBoundary.Point k M × ℝ →
      Q.source.ambientCompletion.ambient.manifold.Point :=
    fun u p => β₀ u (eBs parameterZero p.1, p.2)
  have hβ : ContMDiff ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, Model k)).prod 𝓘(ℝ, ℝ)))
      𝓘(ℝ, Model (2 * n)) ∞ (fun z : ℝ × (IntrinsicBoundary.Point k M × ℝ) => β z.1 z.2) :=
    hβ₀.comp (contMDiff_fst.prodMk
      (((eBs parameterZero).contMDiff.comp (contMDiff_fst.comp contMDiff_snd)).prodMk
        (contMDiff_snd.comp contMDiff_snd)))
  let B := (eBs parameterZero).prodCongr (Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞)
  have hl₀ : IsLocalDiffeomorphAt
      ((𝓘(ℝ, Model k)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model (2 * n)) ∞
      (fun p : IntrinsicBoundary.Point k M × ℝ =>
        (Q.ambientCompletionPresentation s.val).prescribedEndMap (eBs parameterZero p.1, p.2))
      (b, r) :=
    (B.isLocalDiffeomorph (b, r)).comp 𝓘(ℝ, Model (2 * n))
      Q.source.ambientCompletion.ambient.manifold.Point
      ((Q.ambientCompletionPresentation s.val).isLocalDiffeomorph_prescribedEndMap (B (b, r)))
  have heq : (fun p : IntrinsicBoundary.Point k M × ℝ => β s.val.val p) =ᶠ[𝓝 (b, r)]
      (fun p : IntrinsicBoundary.Point k M × ℝ =>
        (Q.ambientCompletionPresentation s.val).prescribedEndMap (eBs parameterZero p.1, p.2)) := by
    filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds
      (isOpen_Ioi.mem_nhds (show r ∈ Ioi a from lt_of_lt_of_le ha hr))] with p hp'
    exact heβ₀ s.val (eBs parameterZero p.1) p.2 hp'
  have hbij : Function.Bijective (mfderiv
      ((𝓘(ℝ, Model k)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model (2 * n))
      (fun p : IntrinsicBoundary.Point k M × ℝ => β s.val.val p) (b, r)) := by
    rw [heq.mfderiv_eq]
    exact (tangentSpaceCast 𝓘(ℝ, Model (2 * n))
      ((Q.ambientCompletionPresentation s.val).prescribedEndMap (eBs parameterZero b, r))
      (β s.val.val (b, r))).bijective.comp
        ((hl₀.mfderivToContinuousLinearEquiv (by simp)).bijective)
  let G := fun z : ℝ × (IntrinsicBoundary.Point k M × ℝ) => (z.1, β z.1 z.2)
  have hl : IsLocalDiffeomorphAt
      ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, Model k)).prod 𝓘(ℝ, ℝ)))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))) ∞ G (s.val.val, (b, r)) := by
    have hM : IsManifold ((𝓘(ℝ, Model k)).prod 𝓘(ℝ, ℝ)) ∞
        (IntrinsicBoundary.Point k M × ℝ) := inferInstance
    let : ChartedSpace (Model k × ℝ) (IntrinsicBoundary.Point k M × ℝ) :=
      prodChartedSpace (Model k) (IntrinsicBoundary.Point k M) ℝ ℝ
    rw [← modelWithCornersSelf_prod] at hM hβ hbij ⊢
    exact isLocalDiffeomorphAt_parameterMap_of_bijective_slice
      (fun z : ℝ × (IntrinsicBoundary.Point k M × ℝ) => β z.1 z.2) hβ s.val.val (b, r) hbij
  have hs : s.val ∈ g.baseSet ∩ c.val.baseSet :=
    ⟨by rw [hbase]; exact mem_univ _, F.base_subset s.property⟩
  obtain ⟨V, hpV, η, hη, heη⟩ :=
    ((compatibleTransition_boundary_germs g c.val hg
      (compatibleTrivialization_of_mem c.property)).native_manifold
        (IntrinsicBoundary.smoothManifold k M) (IntrinsicBoundary.smoothManifold k M)) s.val hs b
  let q : ℝ × Q.source.ambientCompletion.ambient.manifold.Point → ℝ × IntrinsicBoundary.Point k M :=
    fun z => (z.1, (hl.localInverse z).2.1)
  have hq : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n)))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model k)) ∞ q hl.localInverse.source :=
    contMDiffOn_fst.prodMk
      (contMDiff_fst.comp_contMDiffOn (contMDiff_snd.comp_contMDiffOn hl.localInverse_contMDiffOn))
  let W := hl.localInverse.source ∩ q ⁻¹' V
  have hW : IsOpen W :=
    hq.continuousOn.isOpen_inter_preimage hl.localInverse.open_source V.isOpen
  let A : Set (ℝ × (IntrinsicBoundary.Point k M × ℝ)) :=
    {z | a < z.2.2 ∧ -z.2.2 < F.native.width}
  have hA : IsOpen A := (isOpen_lt continuous_const (continuous_snd.comp continuous_snd)).inter
    (isOpen_lt (continuous_snd.comp continuous_snd).neg continuous_const)
  let U : TopologicalSpace.Opens (ℝ × Q.source.ambientCompletion.ambient.manifold.Point) :=
    ⟨W ∩ hl.localInverse ⁻¹' A,
      (hl.localInverse_contMDiffOn.mono inter_subset_left).continuousOn.isOpen_inter_preimage hW hA⟩
  let qU : U → V := fun z => ⟨q z.val, z.property.1.2⟩
  have hqU : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n)))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model k)) ∞ qU := by
    apply (ContMDiff.subtypeVal_comp_iff V qU).mp
    intro z
    exact (hq.contMDiffAt (hl.localInverse.open_source.mem_nhds z.property.1.1)).comp z
      contMDiff_subtype_val.contMDiffAt
  let γ : U → IntrinsicBoundary.Point k M × ℝ :=
    fun z => (η (qU z), (hl.localInverse z.val).2.2)
  have hγ : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n)))
      ((𝓘(ℝ, Model k)).prod 𝓘(ℝ, ℝ)) ∞ γ := by
    refine (hη.comp hqU).prodMk ?_
    intro z
    exact (contMDiff_snd.comp_contMDiffOn
      (contMDiff_snd.comp_contMDiffOn hl.localInverse_contMDiffOn)).contMDiffAt
        (hl.localInverse.open_source.mem_nhds z.property.1.1) |>.comp z
          contMDiff_subtype_val.contMDiffAt
  have hpoint : G (s.val.val, (b, r)) =
      (s.val.val, Q.source.ambientCompletion.endMap (eBs parameterZero b, r)) := by
    dsimp [G, β]
    rw [heβ₀ s.val (eBs parameterZero b) r (lt_of_lt_of_le ha hr),
      (Q.ambientCompletionPresentation s.val).prescribedEndMap_nonnegative _ r hr]
    rfl
  have hpU : (s.val.val, Q.source.ambientCompletion.endMap (eBs parameterZero b, r)) ∈ U := by
    rw [← hpoint]
    refine ⟨⟨hl.localInverse_mem_source, ?_⟩, ?_⟩
    · change ((G (s.val.val, (b, r))).1, (hl.localInverse (G (s.val.val, (b, r)))).2.1) ∈ V
      rw [hl.localInverse_left_inv hl.localInverse_mem_target]
      exact hpV
    · change hl.localInverse (G (s.val.val, (b, r))) ∈ A
      rw [hl.localInverse_left_inv hl.localInverse_mem_target]
      exact ⟨lt_of_lt_of_le ha hr, by linarith [F.native.width_pos]⟩
  refine ⟨U, hpU, γ, hγ, (fun z => z.property.2.2), ?_⟩
  intro v y hy
  refine ⟨⟨(-(γ ⟨(v.val.val, y), hy⟩).2, (γ ⟨(v.val.val, y), hy⟩).1),
    hy.2.2, mem_univ _⟩, rfl, ?_⟩
  have hInv := hl.localInverse_right_inv hy.1.1
  have ht : (hl.localInverse (v.val.val, y)).1 = v.val.val := congrArg Prod.fst hInv
  have hβy : β v.val.val (hl.localInverse (v.val.val, y)).2 = y := by
    have h := congrArg Prod.snd hInv
    change β (hl.localInverse (v.val.val, y)).1 (hl.localInverse (v.val.val, y)).2 = y at h
    rwa [ht] at h
  have hv : v.val ∈ g.baseSet ∩ c.val.baseSet :=
    ⟨by rw [hbase]; exact mem_univ _, F.base_subset v.property⟩
  have hηeq := heη v.val hv (hl.localInverse (v.val.val, y)).2.1 hy.1.2
  have he : (Q.ambientCompletionPresentation v.val).prescribedEndMap
      (eBs parameterZero (hl.localInverse (v.val.val, y)).2.1,
        (hl.localInverse (v.val.val, y)).2.2) = y :=
    (heβ₀ v.val _ _ hy.2.1).symm.trans hβy
  calc
    _ = (F.ambientReferenceTotalInverse L g hg hbase Q hdim eAs hp hc
        (v, (Q.ambientCompletionPresentation v.val).prescribedEndMap
          (eBs parameterZero (hl.localInverse (v.val.val, y)).2.1,
            (hl.localInverse (v.val.val, y)).2.2))).val :=
      congrArg (fun y => (F.ambientReferenceTotalInverse L g hg hbase Q hdim eAs hp hc (v, y)).val)
        he.symm
    _ = _ := F.ambientReferenceTotalInverse_cylinder L g hg hbase Q hdim eAs hp hc
      eBs hb hsquareB v _ _ hy.2.2
    _ = _ := by
      congr 1
      apply Prod.ext
      · rfl
      apply Subtype.ext
      apply Prod.ext
      · rfl
      exact hηeq.symm

/-- Actual real germs of the inverse at every reference completion point,
including both original interval endpoints. The reference compact interior
and nonnegative end cover the entire same completion. -/
theorem ambientReferenceTotalInverse_realGerms
    (eBs : ∀ u, (IntrinsicBoundary.smoothManifold k M).SmoothEquiv
      (Q.pair u).ambientDomain.domain.boundary)
    (hb : ∀ u b, (Q.pair u).ambientDomain.domain.boundaryInclusion.map (eBs u b) =
      (eAs u b.val).val)
    (hsquareB : ∀ u b, (Q.ambientPresentation u).boundaryEquiv (eBs parameterZero b) = eBs u b)
    (R : ℝ → Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M M ∞)
    (hR : IsJointlySmoothDiffeomorphFamily (𝓡∂ (k + 1)) R)
    (hsquareA : ∀ s x, (Q.ambientPresentation s).extensionEquiv
      (eAs parameterZero (R s.val x)).val = (eAs s x).val) :
    HasRealOpenPatchInverseGerms F.native.patches
      Q.source.ambientCompletion.ambient.manifold F.base
      (fun z => (F.ambientReferenceTotalInverse L g hg hbase Q hdim eAs hp hc z).val) := by
  intro s y
  let K := Q.source.ambientCompletion
  by_cases hy : y ∈ K.inclusion.map '' interior Q.source.ambientDomain.domain.carrier
  · obtain ⟨x, hx, rfl⟩ := hy
    let xD : Q.source.ambientDomain.domain.Point := ⟨x, interior_subset hx⟩
    have hxD : (𝓡∂ (2 * n)).IsInteriorPoint xD := by
      change xD ∈ (𝓡∂ (2 * n)).interior Q.source.ambientDomain.domain.Point
      rw [Q.source.ambientDomain.domain.interior_eq_interior]
      exact hx
    have hu : (𝓡∂ (k + 1)).IsInteriorPoint ((eAs parameterZero).symm xD) :=
      (IsLocalDiffeomorphAt.isInteriorPoint_iff (by simp)
        ((eAs parameterZero).symm.isLocalDiffeomorph xD)).mp hxD
    let u : IntrinsicInterior.Point k M := ⟨(eAs parameterZero).symm xD, hu⟩
    left
    simpa only [PairDeformation.ambientNativeInteriorReferenceMap, u,
      Diffeomorph.apply_symm_apply, xD, K, PairDeformation.source] using
      F.ambientReferenceTotalInverse_realInteriorGerm L g hg hbase Q hdim eAs hp hc
        R hR hsquareA s u
  · have hyend : y ∈ range (fun p : Q.source.ambientDomain.domain.boundary.Point × Ici (0 : ℝ) =>
        K.endMap (p.1, p.2)) := by
      rw [K.range_nonnegative_endMap]
      exact hy
    obtain ⟨⟨x, ⟨r, hr⟩⟩, rfl⟩ := hyend
    right
    simpa only [Diffeomorph.apply_symm_apply] using
      F.ambientReferenceTotalInverse_realEndGerm L g hg hbase Q hdim eAs hp hc
        eBs hb hsquareB s ((eBs parameterZero).symm x) r hr

end FsFltz.Geometry.IntrinsicSmoothBundle.LocalCompletionFamily
