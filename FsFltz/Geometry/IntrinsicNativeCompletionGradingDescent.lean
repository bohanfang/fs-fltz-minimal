import FsFltz.Geometry.IntrinsicNativeCompletionEndGradingIdentification
import FsFltz.Geometry.IntervalMaslovTransport
import FsFltz.Geometry.NativeGradingCompatibility

/-!
# Prescribed original native grading on the same completed deformation

Source: `geoemtric-part-fsf.tex`, `def:maslov`, lines 212–244;
`g:chain`, lines 407–413; and `sec:lean`, lines 788–814.
Original interior and end coordinate extensions produce local real smooth
extensions of the literal original native slice pullbacks. Their cover gives
the local complex and canonical-square coefficient inputs to the existing
same-deformation grading constructor. Compatibility and endpoint equations
are stated explicitly when not supplied by original-data bridge theorems.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology

namespace FsFltz.Geometry.PairDeformation
open IntrinsicLiouville IntrinsicCompletionGluing

variable {k n : ℕ} [NeZero n] {M : Type} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]
  (Q : PairDeformation n) (hdim : k + 1 = 2 * n)
  (α : Parameter → Form k M 1)
  (e : ∀ t, Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n)) M
    (Q.pair t).ambientDomain.domain.Point ∞)
  (hp : ∀ t x, ((Q.pair t).ambientDomain.liouville.primitive (e t x).val).compContinuousLinearMap
    (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n)) (fun y => (e t y).val) x) = α t x)
  (hc : ∀ t, HasNativeCoordinateExtensions (k := k)
    (Q.pair t).ambientDomain.domain.extension (fun x => (e t x).val))
  (b : ∀ t, (IntrinsicBoundary.smoothManifold k M).SmoothEquiv
    (Q.pair t).ambientDomain.domain.boundary)
  (hb : ∀ t x, (Q.pair t).ambientDomain.domain.boundaryInclusion.map (b t x) = (e t x.val).val)
  (hsquareB : ∀ t x, (Q.ambientPresentation t).boundaryEquiv (b parameterZero x) = b t x)
  (R : ℝ → Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M M ∞)
  (hR : IsJointlySmoothDiffeomorphFamily (𝓡∂ (k + 1)) R)
  (hsquareA : ∀ t x, (Q.ambientPresentation t).extensionEquiv
    (e parameterZero (R t.val x)).val = (e t x).val)
  {δ : ℝ} (hδ : 0 < δ) (C : Parameter → ℝ × IntrinsicBoundary.Point k M → M)
  (hemb : ∀ t, IsOpenEmbedding (fun p : Half δ (IntrinsicBoundary.Point k M) => C t p.val))
  (hC : ∀ t, ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) (𝓡∂ (k + 1)) ∞ (C t)
    (Half δ (IntrinsicBoundary.Point k M)))
  (hboundary : ∀ t (p : Half δ (IntrinsicBoundary.Point k M)),
    (𝓡∂ (k + 1)).IsBoundaryPoint (C t p.val) ↔ p.val.1 = 0)
  (hinv : ∀ t p, p ∈ Half δ (IntrinsicBoundary.Point k M) →
    ∃ g : M → ℝ × IntrinsicBoundary.Point k M,
      ContMDiffAt (𝓡∂ (k + 1)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) ∞ g (C t p) ∧
        ∀ᶠ q in 𝓝[Half δ (IntrinsicBoundary.Point k M)] p, g (C t q) = q)
  (hzero : ∀ t x, C t (0, x) = x.val)
  (hjoint : IsOpenEmbedding (totalCollar
    (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)))
  (hmix : HasRealMixedGerms (δ := δ) C)
  (hode : ∀ t x, IsMIntegralCurveOn (fun s => C t (s, x))
    (fun z => -liouvilleVector (α t) (exteriorDerivative (α t)) z) (Ico 0 δ))
  (q : TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) →
    (Q.pair parameterZero).ambientCompletion.ambient.manifold.Point)
  (hqnative : ∀ t x,
    q (original (totalCollar (fun t p => C t p.val)) (t, x)) = Q.ambientNativeReferenceMap e t x)
  (hqend : ∀ (t : Parameter) (p : Band δ (IntrinsicBoundary.Point k M)),
    q (totalCylinder (fun t p => C t p.val) (t, p)) =
      (Q.ambientCompletionPresentation t).prescribedEndMap (b parameterZero p.val.2, -p.val.1))


local instance nativeGradingDescentBandCharts : ChartedSpace (Model (k + 1)) (Band δ (IntrinsicBoundary.Point k M)) :=
  bandChartedSpace δ

local instance nativeGradingDescentProductCharts : ChartedSpace (Model k × ℝ) (IntrinsicBoundary.Point k M × ℝ) :=
  prodChartedSpace (Model k) (IntrinsicBoundary.Point k M) ℝ ℝ

local instance nativeGradingDescentProductSmooth : IsManifold 𝓘(ℝ, Model k × ℝ) ∞ (IntrinsicBoundary.Point k M × ℝ) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, Model k)) (I' := 𝓘(ℝ, ℝ))
    (IntrinsicBoundary.Point k M) ℝ

variable
  (Jnative : ∀ s : Parameter, Space (fun p : Half δ (IntrinsicBoundary.Point k M) => C s p.val) →
    Model (k + 1) →L[ℝ] Model (k + 1))
  (Tnative : ∀ s : Parameter, Space (fun p : Half δ (IntrinsicBoundary.Point k M) => C s p.val) →
    ContinuousMultilinearMap ℝ (fun _ : Fin n ⊕ Fin n => Model (k + 1)) ℂ)

open scoped Classical in
/-- The original native complex field pulled back through the actual native
slice comparison; only its interval values enter the grading constructor. -/
def ambientNativeSlicePullbackComplex : ℝ → AlmostComplexField Q.source.ambientManifold :=
  fun t y => if ht : t ∈ parameterInterval then
    let s : Parameter := ⟨t, ht⟩
    letI := completionChartedSpace hδ (C s) (hemb s) (hboundary s) (hzero s)
    let Sinv := (Q.ambientNativeSliceDiffeomorph hdim α e hp hc b hb hsquareB R hR hsquareA
      hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend s).symm
    let D := mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (k + 1)) Sinv y
    D.inverse.comp ((Jnative s (Sinv y)).comp D)
  else 0

/-- The full original native canonical-square tensor pulled back through
that same slice comparison and every tangent slot. -/
def ambientNativeSlicePullbackTensor (s : Parameter) (y : Q.source.ambientManifold.Point) :
    SquaredCanonicalTensor n :=
  letI := completionChartedSpace hδ (C s) (hemb s) (hboundary s) (hzero s)
  let Sinv := (Q.ambientNativeSliceDiffeomorph hdim α e hp hc b hb hsquareB R hR hsquareA
    hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend s).symm
  let D := mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (k + 1)) Sinv y
  (Tnative s (Sinv y)).compContinuousLinearMap (fun _ => D)

/-- Literal interval formula for the original slice complex pullback. -/
theorem ambientNativeSlicePullbackComplex_apply (s : Parameter) (y : Q.source.ambientManifold.Point) :
    letI := completionChartedSpace hδ (C s) (hemb s) (hboundary s) (hzero s)
    let Sinv := (Q.ambientNativeSliceDiffeomorph hdim α e hp hc b hb hsquareB R hR hsquareA
      hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend s).symm
    let D := mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (k + 1)) Sinv y
    Q.ambientNativeSlicePullbackComplex hdim α e hp hc b hb hsquareB R hR hsquareA
      hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend Jnative s.val y =
      D.inverse.comp ((Jnative s (Sinv y)).comp D) := by
  dsimp only
  unfold ambientNativeSlicePullbackComplex
  split
  · rfl
  · rename_i h
    exact (h s.property).elim

/-- Original coordinate regularity on interior source charts. These are
ordinary real-open coordinate extensions of the original native fields,
with no descended coframe or target local extension supplied. -/
def HasNativeInteriorGradingCoordinateExtensions
    (P : Model (2 * n) ≃L[ℝ] Model (k + 1)) : Prop :=
  ∀ (t : Parameter) (u : IntrinsicInterior.Point k M),
    ∃ V : Set (ℝ × Model (k + 1)), IsOpen V ∧
      (t.val, chartAt (Model (k + 1)) u u) ∈ V ∧
      ∃ K : (ℝ × Model (k + 1)) → Model (k + 1) →L[ℝ] Model (k + 1),
        ContDiffOn ℝ ∞ K V ∧
        (∀ (s : Parameter) w, (s.val, w) ∈ V → ∀ v, K (s.val, w) (K (s.val, w) v) = -v) ∧
        ∃ T : (ℝ × Model (k + 1)) →
          ContinuousMultilinearMap ℝ (fun _ : Fin n ⊕ Fin n => Model (k + 1)) ℂ,
          ContDiffOn ℝ ∞ T V ∧
          (∀ (s : Parameter) w, (s.val, w) ∈ V →
            IsSquaredCanonicalTensor
              (P.symm.toContinuousLinearMap.comp ((K (s.val, w)).comp P.toContinuousLinearMap))
              ((T (s.val, w)).compContinuousLinearMap (fun _ => P.toContinuousLinearMap))) ∧
          T (t.val, chartAt (Model (k + 1)) u u) ≠ 0 ∧
          ∀ (s : Parameter) (w : IntrinsicInterior.Point k M),
            w ∈ (chartAt (Model (k + 1)) u).source →
            (s.val, chartAt (Model (k + 1)) u w) ∈ V →
            letI := completionChartedSpace hδ (C s) (hemb s) (hboundary s) (hzero s)
            let j := interiorIn (fun p : Half δ (IntrinsicBoundary.Point k M) => C s p.val)
            let H := (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1))
              (chartAt (Model (k + 1)) u) w).comp
              (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) j w).inverse
            K (s.val, chartAt (Model (k + 1)) u w) = H.comp ((Jnative s (j w)).comp H.inverse) ∧
            T (s.val, chartAt (Model (k + 1)) u w) =
              (Tnative s (j w)).compContinuousLinearMap (fun _ => H.inverse)

/-- The analogous original coordinate regularity on the nonnegative end
charts. All matching equations refer to the source cylinder and chart. -/
def HasNativeEndGradingCoordinateExtensions
    (P : Model (2 * n) ≃L[ℝ] (Model k × ℝ)) : Prop :=
  ∀ (t : Parameter) (x : IntrinsicBoundary.Point k M) (r : ℝ), 0 ≤ r →
    ∃ V : Set (ℝ × (Model k × ℝ)), IsOpen V ∧
      (t.val, chartAt (Model k × ℝ) (x, r) (x, r)) ∈ V ∧
      ∃ K : (ℝ × (Model k × ℝ)) → (Model k × ℝ) →L[ℝ] (Model k × ℝ),
        ContDiffOn ℝ ∞ K V ∧
        (∀ (s : Parameter) w, (s.val, w) ∈ V → ∀ v, K (s.val, w) (K (s.val, w) v) = -v) ∧
        ∃ T : (ℝ × (Model k × ℝ)) →
          ContinuousMultilinearMap ℝ (fun _ : Fin n ⊕ Fin n => (Model k × ℝ)) ℂ,
          ContDiffOn ℝ ∞ T V ∧
          (∀ (s : Parameter) w, (s.val, w) ∈ V →
            IsSquaredCanonicalTensor
              (P.symm.toContinuousLinearMap.comp ((K (s.val, w)).comp P.toContinuousLinearMap))
              ((T (s.val, w)).compContinuousLinearMap (fun _ => P.toContinuousLinearMap))) ∧
          T (t.val, chartAt (Model k × ℝ) (x, r) (x, r)) ≠ 0 ∧
          ∀ (s : Parameter) (p : Band δ (IntrinsicBoundary.Point k M)),
            letI := completionChartedSpace hδ (C s) (hemb s) (hboundary s) (hzero s)
            let w := endBandCoordinates p
            w ∈ (chartAt (Model k × ℝ) (x, r)).source →
            (s.val, chartAt (Model k × ℝ) (x, r) w) ∈ V →
            let j := cylinder (fun p : Half δ (IntrinsicBoundary.Point k M) => C s p.val)
            let H := (mfderiv 𝓘(ℝ, Model k × ℝ) 𝓘(ℝ, Model k × ℝ)
              (chartAt (Model k × ℝ) (x, r)) w).comp
              ((mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model k × ℝ) endBandCoordinates p).comp
                (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) j p).inverse)
            K (s.val, chartAt (Model k × ℝ) (x, r) w) = H.comp ((Jnative s (j p)).comp H.inverse) ∧
            T (s.val, chartAt (Model k × ℝ) (x, r) w) =
              (Tnative s (j p)).compContinuousLinearMap (fun _ => H.inverse)

local notation "Jref" => Q.ambientNativeSlicePullbackComplex hdim α e hp hc b hb hsquareB R hR hsquareA
  hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend Jnative
local notation "Tref" => Q.ambientNativeSlicePullbackTensor hdim α e hp hc b hb hsquareB R hR hsquareA
  hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend Tnative

variable (PI : Model (2 * n) ≃L[ℝ] Model (k + 1))
  (PE : Model (2 * n) ≃L[ℝ] (Model k × ℝ))
  (hinterior : HasNativeInteriorGradingCoordinateExtensions hδ C hemb hboundary hzero Jnative Tnative PI)
  (hend : HasNativeEndGradingCoordinateExtensions hδ C hemb hboundary hzero Jnative Tnative PE)

include hinterior hend in
/-- Both original source branches cover the completed interval family and
produce real-open smooth coframes and full tensors matching the very same
original slice pullbacks. -/
theorem exists_local_ambientNativeSlice_prescribedGradingExtension
    (t : Parameter) (y : Q.source.ambientManifold.Point) :
    ∃ U : Set (ℝ × Q.source.ambientManifold.Point), IsOpen U ∧ (t.val, y) ∈ U ∧
      ∃ B : (ℝ × Q.source.ambientManifold.Point) → Model (2 * n) →L[ℝ] TangentCoordinates n,
        IsSmoothVerticalCoframeOn Q.source.ambientManifold B U ∧
        (∀ z ∈ U, (B z).IsInvertible) ∧
        IsSmoothVerticalEndomorphismOn Q.source.ambientManifold
          (fun z => coframeComplexStructure (B z)) U ∧
        ∃ S : ℝ × Q.source.ambientManifold.Point → SquaredCanonicalTensor n,
          IsSmoothVerticalSquaredTensorOn Q.source.ambientManifold S U ∧
          (∀ z ∈ U, IsSquaredCanonicalTensor (coframeComplexStructure (B z)) (S z)) ∧
          (∀ z ∈ U, S z ≠ 0) ∧
          ∀ (s : Parameter) z, (s.val, z) ∈ U →
            coframeComplexStructure (B (s.val, z)) = Jref s.val z ∧ S (s.val, z) = Tref s z := by
  let K := Q.source.ambientCompletion
  let D := Q.source.ambientDomain.domain
  by_cases hy : y ∈ K.inclusion.map '' interior D.carrier
  · obtain ⟨x, hx, rfl⟩ := hy
    let v : D.Point := ⟨x, interior_subset hx⟩
    have hv : (𝓡∂ (2 * n)).IsInteriorPoint v := by
      change v ∈ (𝓡∂ (2 * n)).interior D.Point
      rw [D.interior_eq_interior]
      exact hx
    let u₀ : IntrinsicInterior.Point k M := ⟨(e parameterZero).symm v,
      (IsLocalDiffeomorphAt.isInteriorPoint_iff (by simp)
        ((e parameterZero).symm.isLocalDiffeomorph v)).mp hv⟩
    let u := IntrinsicInterior.restrictDiffeomorph ((R t.val).symm) u₀
    obtain ⟨V, hV, hpV, Ksource, hK, hsq, Tsource, hT, hcan, hne, hcoords⟩ := hinterior t u
    obtain ⟨U, hU, hpU, B, hB, hBi, hJ, S, hS, hScan, hnz, hm⟩ :=
      Q.exists_ambientNativeSlice_interiorPrescribedGradingExtension hdim α e hp hc b hb
        hsquareB R hR hsquareA hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend
        t u PI V hV hpV Ksource hK hsq Tsource hT hcan hne Jnative Tnative
        (fun s w hw hwV => (hcoords s w hw hwV).1)
        (fun s w hw hwV => (hcoords s w hw hwV).2)
    have hcenter : Q.ambientNativeReferenceMap e t u.val = K.inclusion.map x := by
      rw [Q.ambientNativeReferenceMap_eq_compact e R hsquareA]
      change K.inclusion.map ((e parameterZero) ((R t.val)
        ((R t.val).symm ((e parameterZero).symm v)))).val = K.inclusion.map x
      rw [(R t.val).apply_symm_apply, (e parameterZero).apply_symm_apply]
    refine ⟨U, hU, hcenter ▸ hpU, B, hB, hBi, hJ, S, hS, hScan, hnz, ?_⟩
    intro s z hz
    have hj := Q.ambientNativeSlicePullbackComplex_apply hdim α e hp hc b hb hsquareB R hR
      hsquareA hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend Jnative s z
    exact ⟨(hm s z hz).1.trans hj.symm, (hm s z hz).2⟩
  · have hyend : y ∈ range (fun p : D.boundary.Point × Ici (0 : ℝ) => K.endMap (p.1, p.2)) := by
      rw [K.range_nonnegative_endMap]
      exact hy
    obtain ⟨⟨x, ⟨r, hr⟩⟩, rfl⟩ := hyend
    let x₀ := (b parameterZero).symm x
    obtain ⟨V, hV, hpV, Ksource, hK, hsq, Tsource, hT, hcan, hne, hcoords⟩ := hend t x₀ r hr
    obtain ⟨L, U, hU, hpU, g, hg, hgp, hgchart, heq, hUV, hB, hBi, hJ, hS, hScan, hnz, _, hm⟩ :=
      Q.exists_ambientNativeSlice_endPrescribedGradingExtension hdim α e hp hc b hb
        hsquareB R hR hsquareA hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend
        t x₀ r hr PE V hV hpV Ksource hK hsq Tsource hT hcan hne Jnative Tnative hcoords
    let φ := fun z : ℝ × Q.source.ambientManifold.Point => chartAt (Model k × ℝ) (x₀, r) (g z)
    let B := pullbackCoordinateVerticalCoframe Q.source.ambientManifold φ L
    let S := fun z : ℝ × Q.source.ambientManifold.Point =>
      coordinateSquaredCoframeCoefficient (L (z.1, φ z)) (Tsource (z.1, φ z)) • coframeSquaredGenerator (B z)
    refine ⟨U, hU, ?_, B, hB, hBi, hJ, S, hS, hScan, hnz, ?_⟩
    · simpa only [x₀, Diffeomorph.apply_symm_apply] using hpU
    · intro s z hz
      have hj := Q.ambientNativeSlicePullbackComplex_apply hdim α e hp hc b hb hsquareB R hR
        hsquareA hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend Jnative s z
      exact ⟨(hm s z hz).1.trans hj.symm, (hm s z hz).2⟩

include hinterior hend in
/-- Original source coordinate regularity produces the target local complex
extension witnesses; none of these witnesses is assumed. -/
theorem ambientNativeSlicePullbackComplex_localExtensions :
    HasLocalSmoothIntervalComplexExtensions Q.source.ambientManifold Jref := by
  intro p
  obtain ⟨U, hU, hpU, B, hB, hBi, hJ, S, hS, hcan, hnz, hm⟩ :=
    Q.exists_local_ambientNativeSlice_prescribedGradingExtension hdim α e hp hc b hb
      hsquareB R hR hsquareA hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend
      Jnative Tnative PI PE hinterior hend p.1 p.2
  exact ⟨U, hU, hpU, (fun z => coframeComplexStructure (B z)), hJ,
    fun z hz => (hm z.1 z.2 hz).1⟩

include hinterior hend in
/-- The actual prescribed slice pullback is complex and its full tensor is
canonical and nonzero, by the proved local native reconstruction. -/
theorem ambientNativeSlicePullbackTensor_laws (s : Parameter) (y : Q.source.ambientManifold.Point) :
    (∀ v, Jref s.val y (Jref s.val y v) = -v) ∧
      IsSquaredCanonicalTensor (Jref s.val y) (Tref s y) ∧ Tref s y ≠ 0 := by
  obtain ⟨U, hU, hpU, B, hB, hBi, hJ, S, hS, hcan, hnz, hm⟩ :=
    Q.exists_local_ambientNativeSlice_prescribedGradingExtension hdim α e hp hc b hb
      hsquareB R hR hsquareA hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend
      Jnative Tnative PI PE hinterior hend s y
  obtain ⟨hBJ, hST⟩ := hm s y hpU
  refine ⟨?_, ?_, ?_⟩
  · rw [← hBJ]
    exact coframeComplexStructure_sq _ (hBi _ hpU)
  · rw [← hBJ, ← hST]
    exact hcan _ hpU
  · rw [← hST]
    exact hnz _ hpU

/-- The genuine squared canonical section associated with the full original
native tensor, using the natural canonical-square multiplication equivalence. -/
def ambientNativeSlicePullbackTensorSection (p : Parameter × Q.source.ambientManifold.Point) :
    CanonicalTensorSquare (Jref p.1.val p.2) :=
  (canonicalSquareEquivOfComplexStructure _
    (Q.ambientNativeSlicePullbackTensor_laws hdim α e hp hc b hb hsquareB R hR hsquareA
      hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend
      Jnative Tnative PI PE hinterior hend p.1 p.2).1).symm
    ⟨Tref p.1 p.2,
      (Q.ambientNativeSlicePullbackTensor_laws hdim α e hp hc b hb hsquareB R hR hsquareA
        hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend
        Jnative Tnative PI PE hinterior hend p.1 p.2).2.1⟩

local notation "sectionRef" => Q.ambientNativeSlicePullbackTensorSection hdim α e hp hc b hb hsquareB R hR hsquareA
  hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend Jnative Tnative PI PE hinterior hend

/-- Natural square multiplication recovers the entire prescribed tensor. -/
theorem canonicalSquareMap_ambientNativeSlicePullbackTensorSection
    (p : Parameter × Q.source.ambientManifold.Point) :
    (canonicalSquareMap (Jref p.1.val p.2) (sectionRef p)).val = Tref p.1 p.2 := by
  exact congrArg Subtype.val ((canonicalSquareEquivOfComplexStructure _ _).apply_symm_apply _)

/-- The section does not vanish because its original full tensor does not. -/
theorem ambientNativeSlicePullbackTensorSection_ne_zero
    (p : Parameter × Q.source.ambientManifold.Point) : sectionRef p ≠ 0 := by
  intro hzeroSection
  have hm := Q.canonicalSquareMap_ambientNativeSlicePullbackTensorSection hdim α e hp hc b hb
    hsquareB R hR hsquareA hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend
    Jnative Tnative PI PE hinterior hend p
  have hnz := (Q.ambientNativeSlicePullbackTensor_laws hdim α e hp hc b hb hsquareB R hR
    hsquareA hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend
    Jnative Tnative PI PE hinterior hend p.1 p.2).2.2
  apply hnz
  rw [← hm, hzeroSection, map_zero]
  rfl

include hinterior hend in
/-- Smooth local scalar coordinates of the genuine prescribed section are
extracted from the produced full tensors in the produced coframes. -/
theorem ambientNativeSlicePullbackTensorSection_localCoefficients :
    HasLocalSmoothIntervalTensorCoefficients Q.source.ambientManifold Jref sectionRef := by
  intro p
  obtain ⟨U, hU, hpU, B, hB, hBi, hJ, S, hS, hcan, hnz, hm⟩ :=
    Q.exists_local_ambientNativeSlice_prescribedGradingExtension hdim α e hp hc b hb
      hsquareB R hR hsquareA hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend
      Jnative Tnative PI PE hinterior hend p.1 p.2
  let c : IntervalCanonicalChart Q.source.ambientManifold Jref :=
    { domain := U
      isOpen_domain := hU
      coframe := B
      smooth_coframe := hB
      invertible_coframe := hBi
      intertwines_coframe := by
        intro z hz ht
        have hBJ := (hm ⟨z.1, ht⟩ z.2 hz).1
        rw [← hBJ]
        exact coframeComplexStructure_intertwines _ (hBi z hz) }
  refine ⟨c, U, hU, Subset.refl _, hpU,
    (fun z => squaredCoframeCoefficient (B z) (S z)),
    c.smooth_coefficient hU (Subset.refl _) S hS, ?_⟩
  intro z hz
  have hST := (hm z.1 z.2 hz).2
  have hmap := Q.canonicalSquareMap_ambientNativeSlicePullbackTensorSection hdim α e hp hc b hb
    hsquareB R hR hsquareA hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend
    Jnative Tnative PI PE hinterior hend z
  change squaredCoframeCoefficient (B (z.1.val, z.2)) (S (z.1.val, z.2)) = _
  calc
    _ = squaredCoframeCoefficient (B (z.1.val, z.2)) (Tref z.1 z.2) :=
      congrArg (squaredCoframeCoefficient (B (z.1.val, z.2))) hST
    _ = squaredCoframeCoefficient (B (z.1.val, z.2))
        (canonicalSquareMap (Jref z.1.val z.2) (sectionRef z)).val :=
      congrArg (squaredCoframeCoefficient (B (z.1.val, z.2))) hmap.symm
    _ = _ := c.coefficient_squareMap z (sectionRef z)

variable
  (hbp : ∀ t, (IntrinsicBoundary.smoothManifold k M).pullback
    (Q.pair t).ambientDomain.domain.boundary (b t)
    ((Q.pair t).ambientDomain.domain.boundaryForm (Q.pair t).ambientDomain.liouville.primitive) =
      IntrinsicBoundary.restrictForm (α t))
  (Λ : ∀ t, (completionManifold hδ (C t) (hemb t) (hC t)
    (hboundary t) (hinv t) (hzero t)).Form 1)
  (hΛnative : ∀ t, letI := completionChartedSpace hδ (C t) (hemb t) (hboundary t) (hzero t)
    ∀ x, (Λ t (original (fun p => C t p.val) x)).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1))
        (original (fun p : Half δ (IntrinsicBoundary.Point k M) => C t p.val)) x) = α t x)
  (hΛcylinder : ∀ t, (bandManifold δ (IntrinsicBoundary.smoothManifold k M)).pullback
    (completionManifold hδ (C t) (hemb t) (hC t) (hboundary t) (hinv t) (hzero t))
    (cylinder (fun p => C t p.val)) (Λ t) = cylinderPrimitive δ (α t))
  (hΛsmooth : ∀ s, (completionManifold hδ (C s) (hemb s) (hC s)
    (hboundary s) (hinv s) (hzero s)).IsSmoothForm (Λ s))
  (hnative : ∀ s, IsCompatibleAlmostComplex
    (completionManifold hδ (C s) (hemb s) (hC s) (hboundary s) (hinv s) (hzero s))
    ((completionManifold hδ (C s) (hemb s) (hC s) (hboundary s) (hinv s) (hzero s)).exteriorDerivative
      (Λ s)) (Jnative s))

include hinterior hend hbp hΛnative hΛcylinder hΛsmooth hnative in
/-- Compatibility is inherited from the original native primitive and
complex field. The represented smoothness is produced by the original
coordinate cover and the exterior form is the actual completed primitive. -/
theorem ambientNativeSlicePullbackComplex_compatible (s : Parameter) :
    IsCompatibleAlmostComplex Q.source.ambientManifold
      (Q.source.ambientManifold.exteriorDerivative (Q.completedPrimitive s)) (Jref s.val) := by
  have hJ := Q.ambientNativeSlicePullbackComplex_localExtensions hdim α e hp hc b hb
    hsquareB R hR hsquareA hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend
    Jnative Tnative PI PE hinterior hend
  exact Q.ambientNativeSliceDiffeomorph_symm_compatible hdim α e hp hc b hb hsquareB R hR hsquareA
    hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend
    hbp Λ hΛnative hΛcylinder s (hΛsmooth s) (Jnative s) (hnative s) (Jref s.val)
    (hJ.slice s) (fun y => Q.ambientNativeSlicePullbackComplex_apply hdim α e hp hc b hb
      hsquareB R hR hsquareA hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend Jnative s y)

include hinterior hend hbp hΛnative hΛcylinder hΛsmooth hnative in
/-- Original native coordinate extensions and compatibility construct a
grading on this very deformation. Every interval value is the literal
original slice pullback; endpoint representative equations remain explicit. -/
theorem exists_gradedPairDeformation_of_nativeGradingCoordinateExtensions
    (source : Q.source.Maslov) (target : Q.target.Maslov)
    (eta : ℝ → Q.source.ambientManifold.Form 2)
    (heta : ∀ t : Parameter, eta t.val =
      Q.source.ambientManifold.exteriorDerivative (Q.completedPrimitive t))
    (hJ₀ : Jref 0 = pullbackAlmostComplex Q.source.ambientManifold
      Q.source.ambientManifold (Q.ambientCompletionPresentation parameterZero).equiv source.J)
    (hJ₁ : Jref 1 = pullbackAlmostComplex Q.source.ambientManifold
      Q.target.ambientManifold (Q.ambientCompletionPresentation parameterOne).equiv target.J)
    (hT₀ : ∀ x, Tref parameterZero x =
      pullbackSquaredTensor Q.source.ambientManifold Q.source.ambientManifold
        (Q.ambientCompletionPresentation parameterZero).equiv source.tensor x)
    (hT₁ : ∀ x, Tref parameterOne x =
      pullbackSquaredTensor Q.source.ambientManifold Q.target.ambientManifold
        (Q.ambientCompletionPresentation parameterOne).equiv target.tensor x) :
    ∃ g : GradedPairDeformation Q source target,
      (∀ t : Parameter, g.family.J t.val = Jref t.val) ∧
      ∀ (s : Parameter) y, g.family.tensor s.val y = Tref s y := by
  have hJ := Q.ambientNativeSlicePullbackComplex_localExtensions hdim α e hp hc b hb
    hsquareB R hR hsquareA hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend
    Jnative Tnative PI PE hinterior hend
  have hs := Q.ambientNativeSlicePullbackTensorSection_localCoefficients hdim α e hp hc b hb
    hsquareB R hR hsquareA hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend
    Jnative Tnative PI PE hinterior hend
  have hnz := Q.ambientNativeSlicePullbackTensorSection_ne_zero hdim α e hp hc b hb
    hsquareB R hR hsquareA hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend
    Jnative Tnative PI PE hinterior hend
  have hmap := Q.canonicalSquareMap_ambientNativeSlicePullbackTensorSection hdim α e hp hc b hb
    hsquareB R hR hsquareA hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend
    Jnative Tnative PI PE hinterior hend
  have hcompatible : ∀ t ∈ parameterInterval,
      IsCompatibleAlmostComplex Q.source.ambientManifold (eta t) (Jref t) := by
    intro t ht
    let s : Parameter := ⟨t, ht⟩
    have h := Q.ambientNativeSlicePullbackComplex_compatible hdim α e hp hc b hb hsquareB R hR
      hsquareA hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend
      Jnative Tnative PI PE hinterior hend hbp Λ hΛnative hΛcylinder hΛsmooth hnative s
    exact (heta s).symm ▸ h
  obtain ⟨g, hgJ, hgT⟩ := GradedPairDeformation.exists_of_localExtensions eta heta Jref hcompatible
    hJ sectionRef hnz hs hJ₀ hJ₁
    (fun x => (hmap (parameterZero, x)).trans (hT₀ x))
    (fun x => (hmap (parameterOne, x)).trans (hT₁ x))
  exact ⟨g, hgJ, fun s y => (hgT (s, y)).trans (hmap (s, y))⟩

end FsFltz.Geometry.PairDeformation
