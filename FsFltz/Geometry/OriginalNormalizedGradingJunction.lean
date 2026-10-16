import FsFltz.Geometry.MaslovEmbeddingTensor
import FsFltz.Geometry.OriginalHolomorphicGradingJunction
import FsFltz.Geometry.HolomorphicRankTwoMaslovHomotopy
import FsFltz.Geometry.TailoringCompletedGradingMarked
import FsFltz.Geometry.TailoringCompletedGradingHomotopy
import FsFltz.Geometry.CompletionCompactCompression

/-!
# Grading across the retained holomorphic-to-tailoring normalization

Source: `geometric-part-fsf-proof.tex`, `eq:normalizedrounding`, lines
1260–1262, common markings, lines 1270–1314, `lem:grading`, lines
1981–2089, and `sec:assembly`, lines 2148–2158;
`geoemtric-part-fsf.tex`, `def:maslov`, lines 212–244.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz.Geometry
open SmoothManifold

/-- Restrict to the actual open image and pull back the native primitive
datum through the constructed embedding inverse. -/
private def nativeEmbeddingMaslov {n : ℕ} {M N : SmoothManifold (2 * n)}
    {α : N.Form 1} (s : MaslovRepresentative N (N.exteriorDerivative α))
    (hα : N.IsSmoothForm α) (j : M.SmoothEmbedding N) :
    MaslovRepresentative M (M.exteriorDerivative (M.pullback N j.map α)) :=
  ((MaslovHomotopy.refl s).family.pullbackPrimitiveEmbedding (fun _ _ => hα) j).representative
    parameterZero

private theorem nativeEmbeddingMaslov_tensor_apply {n : ℕ}
    {M N : SmoothManifold (2 * n)} {α : N.Form 1}
    (s : MaslovRepresentative N (N.exteriorDerivative α))
    (hα : N.IsSmoothForm α) (j : M.SmoothEmbedding N) (x : M.Point) :
    (nativeEmbeddingMaslov s hα j).tensor x =
      (s.tensor (j.map x)).compContinuousLinearMap
        (fun _ => mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) j.map x) :=
  MaslovFamily.pullbackPrimitiveEmbedding_tensor_apply _ _ j 0 x

private theorem nativeEmbeddingMaslov_homotopic {n : ℕ}
    {M N : SmoothManifold (2 * n)} {α : N.Form 1}
    {s r : MaslovRepresentative N (N.exteriorDerivative α)}
    (h : MaslovHomotopic s r) (hα : N.IsSmoothForm α) (j : M.SmoothEmbedding N) :
    MaslovHomotopic (nativeEmbeddingMaslov s hα j) (nativeEmbeddingMaslov r hα j) := by
  obtain ⟨H⟩ := h
  refine ⟨{
    family := H.family.pullbackPrimitiveEmbedding (fun _ _ => hα) j
    sourceJ := ?_
    targetJ := ?_
    sourceSection := ?_
    targetSection := ?_ }⟩
  · change pullbackAlmostComplex M (N.restrict j.openRange) j.rangeDiffeomorph
      (fun x => H.family.J 0 x.val) = _
    rw [H.sourceJ]
    rfl
  · change pullbackAlmostComplex M (N.restrict j.openRange) j.rangeDiffeomorph
      (fun x => H.family.J 1 x.val) = _
    rw [H.targetJ]
    rfl
  · change pullbackSquaredTensor M (N.restrict j.openRange) j.rangeDiffeomorph
      (fun x => H.family.tensor 0 x.val) = _
    rw [H.sourceSection]
    rfl
  · change pullbackSquaredTensor M (N.restrict j.openRange) j.rangeDiffeomorph
      (fun x => H.family.tensor 1 x.val) = _
    rw [H.targetSection]
    rfl

/-- Equality of smooth native maps on the full compact carrier detects
their tensor pullbacks on the completion, including boundary derivatives. -/
private theorem tensorPullback_eq_of_eqOn_compact {n : ℕ}
    (D : CompactDomain (2 * n)) (M N : SmoothManifold (2 * n))
    (i : D.extension.SmoothEmbedding M) (f g : M.SmoothMap N)
    (he : ∀ x ∈ D.carrier, f (i.map x) = g (i.map x))
    (τ : N.Point → SquaredCanonicalTensor n) (x : D.extension.Point) (hx : x ∈ D.carrier) :
    (τ (f (i.map x))).compContinuousLinearMap
        (fun _ => mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) f (i.map x)) =
      (τ (g (i.map x))).compContinuousLinearMap
        (fun _ => mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) g (i.map x)) := by
  have hd := D.mfderiv_eq_of_eqOn_carrier N
    (fun _ _ => (f.contMDiff.comp i.map.contMDiff).mdifferentiableAt (by simp))
    (fun _ _ => (g.contMDiff.comp i.map.contMDiff).mdifferentiableAt (by simp)) he x hx
  rw [mfderiv_comp x (f.contMDiff.mdifferentiableAt (by simp))
      (i.map.contMDiff.mdifferentiableAt (by simp)),
    mfderiv_comp x (g.contMDiff.mdifferentiableAt (by simp))
      (i.map.contMDiff.mdifferentiableAt (by simp))] at hd
  have hs : Function.Surjective
      (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) i.map x) :=
    LinearMap.injective_iff_surjective.mp (i.immersion x)
  have hfg : mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) f (i.map x) =
      mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) g (i.map x) := by
    ext v
    obtain ⟨w, rfl⟩ := hs v
    exact congrArg (fun A => A w) hd
  rw [hfg, he x hx]

end FsFltz.Geometry

namespace FsFltz
open Geometry Geometry.SmoothManifold

namespace PotentialTailoringMarkedPrefix
variable {n : ℕ} {I : ToricInput n} {φ : RealSpace n → ℝ}
  {β Cplus Aminus K : ℝ} {m : RoundingChoice}

/-- The actual native zero-time homotopy extends through the retained
outer collar and grades this same normalized junction and tailoring arrow. -/
theorem normalized_junction_gradedLift
    (P : PotentialTailoringMarkedPrefix I φ β Cplus Aminus K m)
    (hφ : ContDiff ℝ ∞ φ) {c : ℝ} (hc : 0 < c)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hπ : ∀ s ∈ parameterInterval, ∀ y, 0 ≤ (lgManifold n).planePairing (lambdaPotentialForm φ)
      (tailoringFamily I β s) y (nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower y))
    (hK : 0 ≤ K)
    (f : MaslovFamily P.tailoring.deformation.source.ambientManifold
      P.tailoring.deformation.completedSymplecticExtension)
    (hfT : ∀ t : Parameter, f.tensor t.val = pullbackSquaredTensor
      P.tailoring.deformation.source.ambientManifold
      (P.tailoring_ambient_marking.family.collars parameterZero).localizedDomain.domain.extension
      (P.tailoring_ambient_marking.zeroOuterComparison t)
      (P.tailoring_ambient_marking.family.completedNativeTensor
        (P.tailoring_ambient_marking.domainPrimitiveFamily (αN := fun s : ℝ =>
          (lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ) (tailoringFamily I β s) K))
        (P.tailoring_ambient_marking.domainMaslovFamily
          (isSmoothFormFamily_tailoringPrimitive I β K hφ)
          (tailoringNativeMaslovFamily I hφ hc hlower β hπ K hK)).tensor t.val))
    (u : P.holomorphic.deformation.target.Maslov)
    (hu : IsLogarithmicGrading (P.holomorphic_ambient_marking.marking parameterOne).equiv u) :
    Nonempty (GradedCompletionIdentification P.junction u
      (P.tailoring.deformation.maslovFamilyRepresentative f parameterZero)) := by
  let R := P.tailoring_ambient_marking
  let C := R.family.collars parameterZero
  let αN := fun s : ℝ => (lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ)
    (tailoringFamily I β s) K
  have hαN := isSmoothFormFamily_tailoringPrimitive I β K hφ
  let N := tailoringNativeMaslovFamily I hφ hc hlower β hπ K hK
  let sN := tailoringNativeMaslov I hφ hc hlower β 0
    (hπ 0 ⟨le_rfl, zero_le_one⟩) K hK
  let rN := tailoringZeroPrescribedMaslov I hφ hc hlower β K hK
  let a := nativeEmbeddingMaslov sN (hαN.slice ⟨le_rfl, zero_le_one⟩) R.nativeEmbedding
  let b := nativeEmbeddingMaslov rN (hαN.slice ⟨le_rfl, zero_le_one⟩) R.nativeEmbedding
  let sD : MaslovRepresentative R.domain.extension
      (R.domain.extension.exteriorDerivative (R.liouville parameterZero).primitive) :=
    { a with compatible := by rw [R.native_primitive parameterZero]; exact a.compatible }
  let rD : MaslovRepresentative R.domain.extension
      (R.domain.extension.exteriorDerivative (R.liouville parameterZero).primitive) :=
    { b with compatible := by rw [R.native_primitive parameterZero]; exact b.compatible }
  have hdom : MaslovHomotopic sD rD := by
    obtain ⟨H⟩ := nativeEmbeddingMaslov_homotopic
      (tailoringNativeMaslov_zeroTime_homotopic_prescribed I hφ hc hlower β _ K hK)
      (hαN.slice ⟨le_rfl, zero_le_one⟩) R.nativeEmbedding
    refine ⟨{
      family := { H.family with compatible := ?_ }
      sourceJ := H.sourceJ
      targetJ := H.targetJ
      sourceSection := H.sourceSection
      targetSection := H.targetSection }⟩
    intro t ht
    rw [R.native_primitive parameterZero]
    exact H.family.compatible t ht
  have hcyl := C.cylindricalMaslovOfNative_homotopic hdom
  let e := P.junction.ambientEquiv.trans (R.marking parameterZero).equiv
  have heform : P.holomorphic.deformation.target.ambientManifold.pullback
      C.cylindricalCompletion.ambient.manifold e
      (C.cylindricalCompletion.ambient.manifold.exteriorDerivative
        C.cylindricalCompletion.ambient.primitive) =
      P.holomorphic.deformation.target.ambientSymplecticForm := by
    change P.holomorphic.deformation.target.ambientManifold.pullback
      C.cylindricalCompletion.ambient.manifold
      ((R.marking parameterZero).equiv ∘ P.junction.ambientEquiv) _ = _
    rw [P.holomorphic.deformation.target.ambientManifold.pullback_comp
      P.tailoring.deformation.source.ambientManifold C.cylindricalCompletion.ambient.manifold
      (P.junction.ambientEquiv.mdifferentiable (by simp))
      ((R.marking parameterZero).equiv.mdifferentiable (by simp))]
    have hm : P.tailoring.deformation.source.ambientManifold.pullback
        C.cylindricalCompletion.ambient.manifold (R.marking parameterZero).equiv
        (C.cylindricalCompletion.ambient.manifold.exteriorDerivative
          C.cylindricalCompletion.ambient.primitive) =
        P.tailoring.deformation.source.ambientSymplecticForm := by
      exact (P.tailoring.deformation.source.ambientManifold.exteriorDerivative_pullback
        C.cylindricalCompletion.ambient.manifold (R.marking parameterZero).equiv.toContMDiffMap
        _ C.cylindricalCompletion.ambient.smooth_primitive).symm.trans
          (congrArg P.tailoring.deformation.source.ambientManifold.exteriorDerivative
            (R.marking parameterZero).primitive)
    rw [hm]
    exact P.junction.pullback_symplecticForm
  let sc := (C.cylindricalMaslovOfNative sD).pullbackTo e heform
  let rc := (C.cylindricalMaslovOfNative rD).pullbackTo e heform
  have hsc : MaslovHomotopic sc rc := hcyl.pullback e heform
  have hcompact (x) (hx : x ∈ P.holomorphic.deformation.target.ambientDomain.domain.carrier) :
      e (P.holomorphic.deformation.target.ambientCompletion.inclusion.map x) ∈
        C.localizedDomain.domain.carrier := by
    obtain ⟨y, hy, heq, hq⟩ := P.junction_ambient x hx
    change (R.marking parameterZero).equiv
      (P.junction.ambientEquiv (P.holomorphic.deformation.target.ambientCompletion.inclusion.map x)) ∈ _
    rw [hq]
    have hinc := (R.marking parameterZero).inclusion ⟨y, hy⟩
    change (R.marking parameterZero).equiv
      (P.tailoring.deformation.source.ambientCompletion.inclusion.map y) = _ at hinc
    rw [hinc]
    have him : (P.tailoring.embedding parameterZero).map y ∈
        tailoringRoundedDomain I φ β 0 (Real.exp β) (Cplus ^ 2 * β ^ 2 / 2) m := by
      exact (Set.ext_iff.mp (P.tailoring.ambient_image parameterZero) _).mp ⟨y, hy, rfl⟩
    have hbound := (tailoringRoundedDomain_subset I φ β 0 (Cplus ^ 2 * β ^ 2 / 2)
      (Real.exp_pos β) m him).1
    have hout : (P.tailoring.embedding parameterZero).map y ∈
        R.nativeEmbedding.map '' R.domain.carrier := by
      rw [R.native_image]
      exact sub_nonpos.mpr hbound
    obtain ⟨z, hz, hmap⟩ := hout
    have hid : (R.inclusion parameterZero ⟨y, hy⟩).val.val = z := by
      apply R.nativeEmbedding.embedding.injective
      exact (R.compact_square parameterZero ⟨y, hy⟩).trans hmap.symm
    change (R.inclusion parameterZero ⟨y, hy⟩).val.val ∈ R.domain.carrier
    rw [hid]
    exact hz
  let sf := (P.tailoring.deformation.maslovFamilyRepresentative f parameterZero).pullbackTo
    P.junction.ambientEquiv P.junction.pullback_symplecticForm
  have hnative : MaslovHomotopic sc sf := by
    apply P.holomorphic.deformation.target.ambientCompletion.maslovHomotopic_of_eq_on_compact
      (P.holomorphic.ambient_nonempty parameterOne)
    intro x hx
    have hrep := R.maslovFamilyRepresentative_tensor_eq_cylindrical_of_marked_mem_carrier
      f (R.domainPrimitiveFamily (αN := αN)) (R.domainMaslovFamily hαN N).tensor hfT
      parameterZero sD rfl
      (P.junction.ambientEquiv (P.holomorphic.deformation.target.ambientCompletion.inclusion.map x))
      (hcompact x hx)
    change ((P.tailoring.deformation.maslovFamilyRepresentative f parameterZero).tensor
      (P.junction.ambientEquiv (P.holomorphic.deformation.target.ambientCompletion.inclusion.map x))).compContinuousLinearMap
        (fun _ => mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n))
        P.junction.ambientEquiv (P.holomorphic.deformation.target.ambientCompletion.inclusion.map x)) =
      pullbackSquaredTensor _ _ e (C.cylindricalMaslovOfNative sD).tensor
        (P.holomorphic.deformation.target.ambientCompletion.inclusion.map x)
    rw [hrep]
    exact congrFun (pullbackSquaredTensor_trans _ _ _ P.junction.ambientEquiv
      (R.marking parameterZero).equiv (C.cylindricalMaslovOfNative sD).tensor).symm _
  have hprescribed : MaslovHomotopic u rc := by
    apply P.holomorphic.deformation.target.ambientCompletion.maslovHomotopic_of_eq_on_compact
      (P.holomorphic.ambient_nonempty parameterOne)
    intro x hx
    let M := P.holomorphic.deformation.target.ambientManifold
    let z := P.holomorphic.deformation.target.ambientCompletion.inclusion.map x
    let jC := R.nativeEmbedding.comp C.originalInclusion
    let g : M.SmoothMap (lgManifold n) :=
      ⟨jC.map ∘ e, jC.map.contMDiff.comp e.contMDiff⟩
    let h : M.SmoothMap (lgManifold n) :=
      (P.holomorphic_ambient_marking.marking parameterOne).equiv.toContMDiffMap
    have hG : ∀ w ∈ P.holomorphic.deformation.target.ambientDomain.domain.carrier,
        g (P.holomorphic.deformation.target.ambientCompletion.inclusion.map w) =
          h (P.holomorphic.deformation.target.ambientCompletion.inclusion.map w) := by
      intro w hw
      obtain ⟨y, hy, heq, hq⟩ := P.junction_ambient w hw
      change jC.map ((R.marking parameterZero).equiv
        (P.junction.ambientEquiv (P.holomorphic.deformation.target.ambientCompletion.inclusion.map w))) = _
      rw [hq]
      have hinc := (R.marking parameterZero).inclusion ⟨y, hy⟩
      change (R.marking parameterZero).equiv
        (P.tailoring.deformation.source.ambientCompletion.inclusion.map y) = _ at hinc
      rw [hinc]
      exact (R.compact_square parameterZero ⟨y, hy⟩).trans
        (heq.trans ((P.holomorphic_ambient_marking.marking parameterOne).inclusion ⟨w, hw⟩).symm)
    have hdg : mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) g z =
        (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) R.nativeEmbedding.map
          (e z).val.val).comp
          (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) e z) := by
      have h₁ := mfderiv_comp (f := e) (g := jC.map) z
        (jC.map.contMDiff.mdifferentiableAt (by simp))
        (e.contMDiff.mdifferentiableAt (by simp))
      have h₂ := mfderiv_comp (f := C.originalInclusion.map) (g := R.nativeEmbedding.map) (e z)
        (R.nativeEmbedding.map.contMDiff.mdifferentiableAt (by simp))
        (C.originalInclusion.map.contMDiff.mdifferentiableAt (by simp))
      rw [C.mfderiv_originalInclusion] at h₂
      have h₂' : mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) jC.map (e z) =
          mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) R.nativeEmbedding.map
            (e z).val.val := by
        ext v
        exact congrArg (fun A => A v) h₂
      exact h₁.trans (congrArg (fun A => A.comp
        (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) e z)) h₂')
    have hrc : rc.tensor z = (logarithmicSquaredVolumeTensor n (g z)).compContinuousLinearMap
        (fun _ => mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) g z) := by
      change ((C.cylindricalMaslovOfNative rD).tensor (e z)).compContinuousLinearMap
        (fun _ => mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) e z) = _
      rw [(C.cylindricalMaslovOfNative_eq_on_carrier rD (e z) (hcompact x hx)).2]
      change (b.tensor (e z).val.val).compContinuousLinearMap
        (fun _ => mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) e z) = _
      rw [nativeEmbeddingMaslov_tensor_apply rN _ R.nativeEmbedding, hdg]
      ext v
      rfl
    rw [hrc]
    have hpull := tensorPullback_eq_of_eqOn_compact
      P.holomorphic.deformation.target.ambientDomain.domain M (lgManifold n)
      P.holomorphic.deformation.target.ambientCompletion.inclusion g h hG
      (logarithmicSquaredVolumeTensor n) x hx
    rw [hpull]
    ext v
    change logarithmicSquaredVolumeTensor n (h z)
      (fun i => mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) h z (v i)) = u.tensor z v
    calc
      _ = coordinateSquaredVolumeValue (fun i => logarithmicTangentCoordinates
          (lgManifold n) id (h z)
          (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) h z (v i))) :=
        logarithmicSquaredVolumeTensor_apply _ _
      _ = coordinateSquaredVolumeValue (fun i => logarithmicTangentCoordinates M
          (P.holomorphic_ambient_marking.marking parameterOne).equiv z (v i)) := by
        apply congrArg coordinateSquaredVolumeValue
        funext i
        exact (logarithmicTangentCoordinates_naturality M
          (P.holomorphic_ambient_marking.marking parameterOne).equiv z (v i)).symm
      _ = u.tensor z v := (hu z v).symm
  exact (P.junction.gradedLift_iff_class_eq u _).mpr
    (Quot.sound (hprescribed.trans (hsc.symm.trans hnative)))

end PotentialTailoringMarkedPrefix

namespace PotentialTailoringOriginalMarkedPrefix
variable {n : ℕ} {I : ToricInput n} {φ : RealSpace n → ℝ}
  {β Cplus Aminus originalK K : ℝ} {m : RoundingChoice}

/-- The prescribed original grading extends along every arrow of the
retained five-arrow prefix, using this same selected tailoring family. -/
theorem graded_chain_of_tailoring_formula
    (P : PotentialTailoringOriginalMarkedPrefix I φ β Cplus Aminus originalK K m)
    (hφ : ContDiff ℝ ∞ φ) {c : ℝ} (hc : 0 < c)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hπ : ∀ s ∈ parameterInterval, ∀ y, 0 ≤ (lgManifold n).planePairing (lambdaPotentialForm φ)
      (tailoringFamily I β s) y (nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower y))
    (hK : 0 ≤ K)
    (f : MaslovFamily P.marked.tailoring.deformation.source.ambientManifold
      P.marked.tailoring.deformation.completedSymplecticExtension)
    (hfT : ∀ t : Parameter, f.tensor t.val = pullbackSquaredTensor
      P.marked.tailoring.deformation.source.ambientManifold
      (P.marked.tailoring_ambient_marking.family.collars parameterZero).localizedDomain.domain.extension
      (P.marked.tailoring_ambient_marking.zeroOuterComparison t)
      (P.marked.tailoring_ambient_marking.family.completedNativeTensor
        (P.marked.tailoring_ambient_marking.domainPrimitiveFamily (αN := fun s : ℝ =>
          (lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ) (tailoringFamily I β s) K))
        (P.marked.tailoring_ambient_marking.domainMaslovFamily
          (isSmoothFormFamily_tailoringPrimitive I β K hφ)
          (tailoringNativeMaslovFamily I hφ hc hlower β hπ K hK)).tensor t.val))
    (gTail : Nonempty (GradedPairDeformation P.marked.tailoring.deformation
      (P.marked.tailoring.deformation.maslovFamilyRepresentative f parameterZero)
      (P.marked.tailoring.deformation.maslovFamilyRepresentative f parameterOne))) :
    Nonempty (GradedComparisonChain P.original.pair P.chain P.originalMaslov
      (P.marked.tailoring.deformation.maslovFamilyRepresentative f parameterOne)) := by
  obtain ⟨u, hu, _, ⟨gH⟩⟩ := P.exists_graded_holomorphicChain hφ hc hlower hK
  obtain ⟨gJ⟩ := P.marked.normalized_junction_gradedLift hφ hc hlower hπ hK f hfT u hu
  obtain ⟨gT⟩ := gTail
  rw [P.chain_eq_holomorphicChain]
  exact ⟨(gH.cons (.identification gJ)).cons (.deformation gT)⟩

/-- The native family and retained marking produce one completed
tailoring family, its full tensor formula, and the grade of the whole
retained prefix ending at that same family's terminal representative. -/
theorem exists_graded_chain_with_tailoring_formula
    (P : PotentialTailoringOriginalMarkedPrefix I φ β Cplus Aminus originalK K m)
    (hφ : ContDiff ℝ ∞ φ) {c : ℝ} (hc : 0 < c)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hπ : ∀ s ∈ parameterInterval, ∀ y, 0 ≤ (lgManifold n).planePairing (lambdaPotentialForm φ)
      (tailoringFamily I β s) y (nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower y))
    (hK : 0 ≤ K) :
    ∃ f : MaslovFamily P.marked.tailoring.deformation.source.ambientManifold
      P.marked.tailoring.deformation.completedSymplecticExtension,
      (∀ t : Parameter, f.tensor t.val = pullbackSquaredTensor
        P.marked.tailoring.deformation.source.ambientManifold
        (P.marked.tailoring_ambient_marking.family.collars parameterZero).localizedDomain.domain.extension
        (P.marked.tailoring_ambient_marking.zeroOuterComparison t)
        (P.marked.tailoring_ambient_marking.family.completedNativeTensor
          (P.marked.tailoring_ambient_marking.domainPrimitiveFamily (αN := fun s : ℝ =>
            (lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ) (tailoringFamily I β s) K))
          (P.marked.tailoring_ambient_marking.domainMaslovFamily
            (isSmoothFormFamily_tailoringPrimitive I β K hφ)
            (tailoringNativeMaslovFamily I hφ hc hlower β hπ K hK)).tensor t.val)) ∧
      Nonempty (GradedPairDeformation P.marked.tailoring.deformation
        (P.marked.tailoring.deformation.maslovFamilyRepresentative f parameterZero)
        (P.marked.tailoring.deformation.maslovFamilyRepresentative f parameterOne)) ∧
      Nonempty (GradedComparisonChain P.original.pair P.chain P.originalMaslov
        (P.marked.tailoring.deformation.maslovFamilyRepresentative f parameterOne)) := by
  obtain ⟨f, gT, _, hfT⟩ := P.marked.tailoring_ambient_marking.exists_completedGrading
    (isSmoothFormFamily_tailoringPrimitive I β K hφ)
    (tailoringNativeMaslovFamily I hφ hc hlower β hπ K hK)
  exact ⟨f, hfT, gT, P.graded_chain_of_tailoring_formula hφ hc hlower hπ hK f hfT gT⟩

end PotentialTailoringOriginalMarkedPrefix
end FsFltz
