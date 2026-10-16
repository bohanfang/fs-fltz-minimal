import FsFltz.Geometry.IntrinsicNativeCompletionFamilySmooth
import FsFltz.Geometry.IntrinsicCompletionFamilySlices

/-!
# Inverting the comparison of the original completion family

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 142–158;
`def:chain`, lines 163–199; and `sec:lean`, lines 788–814.
The original attachment has unique native or strictly outward representatives.
The literal compact and cylindrical formulas therefore construct an inverse
to its parameter-preserving comparison with the same reference completion.
No inverse or correspondence is supplied as a hypothesis.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology

namespace FsFltz.Geometry.IntrinsicCompletionGluing

variable {T M B : Type*} [TopologicalSpace T] [TopologicalSpace M]
  [TopologicalSpace B] {δ : ℝ} (c : T → Half δ B → M)

omit [TopologicalSpace M] in
/-- The actual attachment has native representatives and strictly outward
cylinder representatives. Inward cylinder points are already native points. -/
theorem total_original_negative_cylinder_cover (z : TotalSpace c) :
    (∃ t x, original (totalCollar c) (t, x) = z) ∨
      ∃ (t : T) (p : Band δ B), p.val.1 < 0 ∧ totalCylinder c (t, p) = z := by
  have hz := (normalEquiv (totalCollar c)).symm_apply_apply z
  cases h : normalEquiv (totalCollar c) z with
  | inl x =>
    rw [h] at hz
    exact Or.inl ⟨x.1, x.2, hz⟩
  | inr p =>
    rw [h] at hz
    let q := parameterBandHomeomorph.symm p.val
    refine Or.inr ⟨q.1, q.2, p.property, ?_⟩
    change cylinder (totalCollar c) (parameterBandHomeomorph q) = z
    rw [Homeomorph.apply_symm_apply]
    exact hz

end FsFltz.Geometry.IntrinsicCompletionGluing

namespace FsFltz.Geometry.PairDeformation
open IntrinsicLiouville IntrinsicCompletionGluing

variable {k n : ℕ} [NeZero n] {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]

/-- The comparison retains the actual projection to the parameter interval. -/
def ambientNativeTotalComparison (Q : PairDeformation n) {δ : ℝ}
    (C : Parameter → ℝ × IntrinsicBoundary.Point k M → M)
    (q : TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) →
      (Q.pair parameterZero).ambientCompletion.ambient.manifold.Point)
    (z : TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)) :
    Parameter × (Q.pair parameterZero).ambientCompletion.ambient.manifold.Point :=
  (parameter (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) z, q z)

variable [IsManifold (𝓡∂ (k + 1)) ∞ M] [T2Space M] [SecondCountableTopology M]

/-- The exact native and cylinder formulas give a bijection to the same
reference completion, without an inverse or topological comparison premise. -/
theorem bijective_ambientNativeTotalComparison
    (Q : PairDeformation n)
    (e : ∀ t, Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n)) M
      (Q.pair t).ambientDomain.domain.Point ∞)
    (b : ∀ t, (IntrinsicBoundary.smoothManifold k M).SmoothEquiv
      (Q.pair t).ambientDomain.domain.boundary)
    (R : ℝ → Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M M ∞)
    (hsquare : ∀ t x, (Q.ambientPresentation t).extensionEquiv
      (e parameterZero (R t.val x)).val = (e t x).val)
    {δ : ℝ} (hδ : 0 < δ) (C : Parameter → ℝ × IntrinsicBoundary.Point k M → M)
    (q : TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) →
      (Q.pair parameterZero).ambientCompletion.ambient.manifold.Point)
    (hqnative : ∀ t x,
      q (original (totalCollar (fun t p => C t p.val)) (t, x)) = Q.ambientNativeReferenceMap e t x)
    (hqend : ∀ (t : Parameter) (p : Band δ (IntrinsicBoundary.Point k M)),
      q (totalCylinder (fun t p => C t p.val) (t, p)) =
        (Q.ambientCompletionPresentation t).prescribedEndMap (b parameterZero p.val.2, -p.val.1)) :
    Function.Bijective (Q.ambientNativeTotalComparison C q) := by
  let c := fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val
  let K := (Q.pair parameterZero).ambientCompletion
  have hn (t : Parameter) (x : M) :
      q (original (totalCollar c) (t, x)) =
        K.inclusion.map (e parameterZero (R t.val x)).val :=
    (hqnative t x).trans (Q.ambientNativeReferenceMap_eq_compact e R hsquare t x)
  have he (t : Parameter) (p : Band δ (IntrinsicBoundary.Point k M)) (hp : p.val.1 < 0) :
      q (totalCylinder c (t, p)) = K.endMap (b parameterZero p.val.2, -p.val.1) :=
    (hqend t p).trans ((Q.ambientCompletionPresentation t).prescribedEndMap_nonnegative
      _ _ (neg_nonneg.mpr hp.le))
  have hsep (t : Parameter) (x : M) (s : Parameter)
      (p : Band δ (IntrinsicBoundary.Point k M)) (hp : p.val.1 < 0) :
      q (original (totalCollar c) (t, x)) ≠ q (totalCylinder c (s, p)) := by
    rw [hn, he s p hp]
    intro h
    exact K.overlap _ _ (neg_pos.mpr hp) ⟨_, (e parameterZero (R t.val x)).property, h⟩
  constructor
  · intro z w h
    have ht := congrArg Prod.fst h
    have hq := congrArg Prod.snd h
    change parameter c z = parameter c w at ht
    change q z = q w at hq
    rcases total_original_negative_cylinder_cover c z with ⟨t, x, rfl⟩ | ⟨t, p, hp, rfl⟩ <;>
      rcases total_original_negative_cylinder_cover c w with ⟨s, y, rfl⟩ | ⟨s, u, hu, rfl⟩
    · change t = s at ht
      subst s
      rw [hn, hn] at hq
      have hx : x = y := (R t.val).injective ((e parameterZero).injective
        (Subtype.ext (K.inclusion.embedding.injective hq)))
      rw [hx]
    · exact False.elim (hsep t x s u hu hq)
    · exact False.elim (hsep s y t p hp hq.symm)
    · change t = s at ht
      subst s
      rw [he t p hp, he t u hu] at hq
      have hcoord := K.endMap_injective hq
      have hpu : p = u := by
        apply Subtype.ext
        exact Prod.ext (neg_injective (congrArg Prod.snd hcoord))
          ((b parameterZero).injective (congrArg Prod.fst hcoord))
      rw [hpu]
  · rintro ⟨t, y⟩
    have hy : y ∈ K.inclusion.map '' (Q.pair parameterZero).ambientDomain.domain.carrier ∪
        K.endMap '' (univ ×ˢ Ici (0 : ℝ)) := by rw [K.covering]; trivial
    rcases hy with ⟨x, hx, hxy⟩ | ⟨⟨v, r⟩, ⟨_, hr⟩, hvry⟩
    · let u := (R t.val).symm ((e parameterZero).symm ⟨x, hx⟩)
      refine ⟨original (totalCollar c) (t, u), Prod.ext rfl ?_⟩
      change q (original (totalCollar c) (t, u)) = y
      rw [hn]
      simpa only [u, Diffeomorph.apply_symm_apply] using hxy
    · change 0 ≤ r at hr
      let p : Band δ (IntrinsicBoundary.Point k M) :=
        ⟨(-r, (b parameterZero).symm v), ⟨show -r < δ by linarith, mem_univ _⟩⟩
      refine ⟨totalCylinder c (t, p), Prod.ext rfl ?_⟩
      change q (totalCylinder c (t, p)) = y
      rw [hqend, (Q.ambientCompletionPresentation t).prescribedEndMap_nonnegative _ _
        (show 0 ≤ -p.val.1 from by dsimp [p]; linarith)]
      simpa only [p, Diffeomorph.apply_symm_apply, neg_neg] using hvry

/-- The fixed reference inclusion of the original native interior. -/
def ambientNativeInteriorReferenceMap (Q : PairDeformation n)
    (e₀ : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n)) M
      (Q.pair parameterZero).ambientDomain.domain.Point ∞)
    (u : IntrinsicInterior.Point k M) :
    (Q.pair parameterZero).ambientCompletion.ambient.manifold.Point :=
  (Q.pair parameterZero).ambientCompletion.inclusion.map (e₀ u.val).val

omit [T2Space M] [SecondCountableTopology M] in
/-- The fixed native interior map has actual local smooth inverses in the
given reference completion. Its differential is the composition of the
native interior, compact carrier, and completion inclusion differentials. -/
theorem isLocalDiffeomorph_ambientNativeInteriorReferenceMap
    (Q : PairDeformation n) (hdim : k + 1 = 2 * n)
    (e₀ : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n)) M
      (Q.pair parameterZero).ambientDomain.domain.Point ∞) :
    IsLocalDiffeomorph 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (2 * n)) ∞
      (Q.ambientNativeInteriorReferenceMap e₀) := by
  let D := (Q.pair parameterZero).ambientDomain.domain
  let K := (Q.pair parameterZero).ambientCompletion
  let j : IntrinsicInterior.Point k M → D.Point := fun u => e₀ u.val
  have hj : ContMDiff 𝓘(ℝ, Model (k + 1)) (𝓡∂ (2 * n)) ∞ j :=
    e₀.contMDiff.comp IntrinsicInterior.contMDiff_val
  let i : IntrinsicInterior.Point k M → D.extension.Point := fun u => (j u).val
  have hi : ContMDiff 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (2 * n)) ∞ i :=
    D.contMDiff_subtype_val.comp hj
  have hf : ContMDiff 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (2 * n)) ∞
      (Q.ambientNativeInteriorReferenceMap e₀) := K.inclusion.map.contMDiff.comp hi
  intro u
  have hjinj : Function.Injective (mfderiv 𝓘(ℝ, Model (k + 1)) (𝓡∂ (2 * n)) j u) := by
    change Function.Injective (mfderiv 𝓘(ℝ, Model (k + 1)) (𝓡∂ (2 * n))
      (e₀ ∘ (Subtype.val : IntrinsicInterior.Point k M → M)) u)
    rw [mfderiv_comp u (e₀.contMDiff.mdifferentiableAt (by simp))
      (IntrinsicInterior.contMDiff_val.mdifferentiableAt (by simp))]
    exact (e₀.isInvertible_mfderiv (by simp)).injective.comp
      (IntrinsicInterior.injective_mfderiv_val u)
  have hiinj : Function.Injective (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (2 * n)) i u) := by
    change Function.Injective (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (2 * n))
      ((Subtype.val : D.Point → D.extension.Point) ∘ j) u)
    rw [mfderiv_comp u (D.contMDiff_subtype_val.mdifferentiableAt (by simp))
      (hj.mdifferentiableAt (by simp))]
    exact (D.injective_mfderiv_subtype_val (j u)).comp hjinj
  have hfinj : Function.Injective (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (2 * n))
      (Q.ambientNativeInteriorReferenceMap e₀) u) := by
    change Function.Injective (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (2 * n))
      (K.inclusion.map ∘ i) u)
    rw [mfderiv_comp u (K.inclusion.map.contMDiff.mdifferentiableAt (by simp))
      (hi.mdifferentiableAt (by simp))]
    exact (K.inclusion.immersion (i u)).comp hiinj
  have hbij : Function.Bijective (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (2 * n))
      (Q.ambientNativeInteriorReferenceMap e₀) u) := by
    refine ⟨hfinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hfinj⟩
    change Module.finrank ℝ (Model (k + 1)) = Module.finrank ℝ (Model (2 * n))
    rw [hdim]
  exact isLocalDiffeomorphAt_of_bijective_mfderiv_manifold isOpen_univ hf.contMDiffOn
    (mem_univ u) hbij

section Inverse

variable (Q : PairDeformation n)
  (e : ∀ t, Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n)) M
    (Q.pair t).ambientDomain.domain.Point ∞)
  (b : ∀ t, (IntrinsicBoundary.smoothManifold k M).SmoothEquiv
    (Q.pair t).ambientDomain.domain.boundary)
  (R : ℝ → Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M M ∞)
  (hsquare : ∀ t x, (Q.ambientPresentation t).extensionEquiv
    (e parameterZero (R t.val x)).val = (e t x).val)
  {δ : ℝ} (hδ : 0 < δ) (C : Parameter → ℝ × IntrinsicBoundary.Point k M → M)
  (q : TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) →
    (Q.pair parameterZero).ambientCompletion.ambient.manifold.Point)
  (hqnative : ∀ t x,
    q (original (totalCollar (fun t p => C t p.val)) (t, x)) = Q.ambientNativeReferenceMap e t x)
  (hqend : ∀ (t : Parameter) (p : Band δ (IntrinsicBoundary.Point k M)),
    q (totalCylinder (fun t p => C t p.val) (t, p)) =
      (Q.ambientCompletionPresentation t).prescribedEndMap (b parameterZero p.val.2, -p.val.1))

/-- The inverse is constructed from the proved bijection of the original
quotient comparison. Its forward function is the literal prescribed map. -/
def ambientNativeTotalEquiv :
    TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) ≃
      Parameter × (Q.pair parameterZero).ambientCompletion.ambient.manifold.Point :=
  Equiv.ofBijective (Q.ambientNativeTotalComparison C q)
    (Q.bijective_ambientNativeTotalComparison e b R hsquare hδ C q hqnative hqend)

@[simp] theorem ambientNativeTotalEquiv_apply
    (z : TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)) :
    Q.ambientNativeTotalEquiv e b R hsquare hδ C q hqnative hqend z =
      (parameter (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) z, q z) := rfl

/-- The constructed inverse retains every prescribed native point. -/
theorem ambientNativeTotalEquiv_symm_native (t : Parameter) (x : M) :
    (Q.ambientNativeTotalEquiv e b R hsquare hδ C q hqnative hqend).symm
      (t, Q.ambientNativeReferenceMap e t x) =
        original (totalCollar (fun t p => C t p.val)) (t, x) := by
  apply (Q.ambientNativeTotalEquiv e b R hsquare hδ C q hqnative hqend).injective
  rw [Equiv.apply_symm_apply]
  apply Prod.ext
  · rfl
  · exact (hqnative t x).symm

/-- The constructed inverse has the exact full-cylinder formula, including
the original inward collar and its seam, rather than only the outward end. -/
theorem ambientNativeTotalEquiv_symm_cylinder
    (t : Parameter) (p : Band δ (IntrinsicBoundary.Point k M)) :
    (Q.ambientNativeTotalEquiv e b R hsquare hδ C q hqnative hqend).symm
      (t, (Q.ambientCompletionPresentation t).prescribedEndMap
        (b parameterZero p.val.2, -p.val.1)) =
          totalCylinder (fun t p => C t p.val) (t, p) := by
  apply (Q.ambientNativeTotalEquiv e b R hsquare hδ C q hqnative hqend).injective
  rw [Equiv.apply_symm_apply]
  apply Prod.ext
  · rfl
  · exact (hqend t p).symm

/-- Every nonnegative reference radius is retained by the inverse, with
the actual parameter and the native boundary point unchanged. -/
theorem ambientNativeTotalEquiv_symm_end
    (t : Parameter) (x : IntrinsicBoundary.Point k M) (r : ℝ) (hr : 0 ≤ r) :
    (Q.ambientNativeTotalEquiv e b R hsquare hδ C q hqnative hqend).symm
      (t, (Q.pair parameterZero).ambientCompletion.endMap (b parameterZero x, r)) =
        totalCylinder (fun t p => C t p.val)
          (t, ⟨(-r, x), ⟨show -r < δ by linarith, mem_univ _⟩⟩) := by
  let p : Band δ (IntrinsicBoundary.Point k M) :=
    ⟨(-r, x), ⟨show -r < δ by linarith, mem_univ _⟩⟩
  have h := Q.ambientNativeTotalEquiv_symm_cylinder e b R hsquare hδ C q hqnative hqend t p
  rw [(Q.ambientCompletionPresentation t).prescribedEndMap_nonnegative _ _
    (show 0 ≤ -p.val.1 from by dsimp [p]; linarith)] at h
  simpa only [p, neg_neg] using h

/-- The inverse lands in the exact original parameter fiber. -/
@[simp] theorem parameter_ambientNativeTotalEquiv_symm
    (p : Parameter × (Q.pair parameterZero).ambientCompletion.ambient.manifold.Point) :
    parameter (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)
      ((Q.ambientNativeTotalEquiv e b R hsquare hδ C q hqnative hqend).symm p) = p.1 :=
  congrArg Prod.fst ((Q.ambientNativeTotalEquiv e b R hsquare hδ C q hqnative hqend).apply_symm_apply p)

/-- The actual inverse is jointly smooth above the fixed native interior.
The fixed reference inclusion supplies a local inverse, and the original
joint native family supplies the inverse coordinate change `R_t⁻¹`. -/
theorem contMDiffAt_ambientNativeTotalEquiv_symm_interior
    (hdim : k + 1 = 2 * n)
    (hR : IsJointlySmoothDiffeomorphFamily (𝓡∂ (k + 1)) R)
    (hboundary : ∀ t (p : Half δ (IntrinsicBoundary.Point k M)),
      (𝓡∂ (k + 1)).IsBoundaryPoint (C t p.val) ↔ p.val.1 = 0)
    (hzero : ∀ t x, C t (0, x) = x.val)
    (hjoint : IsOpenEmbedding (totalCollar
      (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)))
    (hmix : HasRealMixedGerms (δ := δ) C)
    (t : Parameter) (u : IntrinsicInterior.Point k M) :
    letI := totalFamilyChartedSpace hδ C hzero hjoint
    ContMDiffAt (familyModel (2 * n)) (familyModel (k + 1)) ∞
      (Q.ambientNativeTotalEquiv e b R hsquare hδ C q hqnative hqend).symm
      (t, Q.ambientNativeInteriorReferenceMap (e parameterZero) u) := by
  let := totalFamilyChartedSpace hδ C hzero hjoint
  let c := fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val
  let A := Q.ambientNativeTotalEquiv e b R hsquare hδ C q hqnative hqend
  let f := Q.ambientNativeInteriorReferenceMap (e parameterZero)
  let l := Q.isLocalDiffeomorph_ambientNativeInteriorReferenceMap hdim (e parameterZero) u
  let ri : Parameter × IntrinsicInterior.Point k M → IntrinsicInterior.Point k M :=
    fun p => ⟨(R p.1.val).symm p.2.val,
      (IsLocalDiffeomorphAt.isInteriorPoint_iff (by simp)
        ((R p.1.val).symm.isLocalDiffeomorph p.2.val)).mp p.2.property⟩
  have hri : ContMDiff (familyModel (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ ri := by
    apply IntrinsicInterior.contMDiff_iff_val.mpr
    exact hR.2.comp (contMDiff_subtypeVal_Icc.prodMap IntrinsicInterior.contMDiff_val)
  let r : Parameter × (Q.pair parameterZero).ambientCompletion.ambient.manifold.Point →
      TotalSpace c := fun p => totalInterior c (p.1, ri (p.1, l.localInverse p.2))
  have hr : ContMDiffAt (familyModel (2 * n)) (familyModel (k + 1)) ∞ r (t, f u) := by
    apply (contMDiff_totalInterior hδ C hboundary hzero hjoint hmix).contMDiffAt.comp
    apply contMDiffAt_fst.prodMk
    apply hri.contMDiffAt.comp
    apply contMDiffAt_fst.prodMk
    exact (l.localInverse_contMDiffOn.contMDiffAt
      (l.localInverse.open_source.mem_nhds l.localInverse_mem_source)).comp (t, f u)
        (contMDiffAt_snd : ContMDiffAt (familyModel (2 * n)) 𝓘(ℝ, Model (2 * n)) ∞
          Prod.snd (t, f u))
  apply hr.congr_of_eventuallyEq
  have hn : ∀ᶠ p in 𝓝 (t, f u), p.2 ∈ l.localInverse.source :=
    continuous_snd.continuousAt.eventually
      (l.localInverse.open_source.mem_nhds l.localInverse_mem_source)
  filter_upwards [hn] with p hp
  apply A.injective
  rw [Equiv.apply_symm_apply]
  apply Prod.ext
  · rfl
  · change p.2 = q (original (totalCollar c) (p.1, (ri (p.1, l.localInverse p.2)).val))
    rw [hqnative, Q.ambientNativeReferenceMap_eq_compact e R hsquare]
    change p.2 = (Q.pair parameterZero).ambientCompletion.inclusion.map
      (e parameterZero (R p.1.val ((R p.1.val).symm (l.localInverse p.2).val))).val
    rw [(R p.1.val).apply_symm_apply]
    exact (l.localInverse_right_inv hp).symm

/-- The native interior inverse germ applies at every actual reference
compact interior point. The given compact atlas and the original native
diffeomorphism identify the two interior notions. -/
theorem contMDiffAt_ambientNativeTotalEquiv_symm_compactInterior
    (hdim : k + 1 = 2 * n)
    (hR : IsJointlySmoothDiffeomorphFamily (𝓡∂ (k + 1)) R)
    (hboundary : ∀ t (p : Half δ (IntrinsicBoundary.Point k M)),
      (𝓡∂ (k + 1)).IsBoundaryPoint (C t p.val) ↔ p.val.1 = 0)
    (hzero : ∀ t x, C t (0, x) = x.val)
    (hjoint : IsOpenEmbedding (totalCollar
      (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)))
    (hmix : HasRealMixedGerms (δ := δ) C)
    (t : Parameter)
    (x : (Q.pair parameterZero).ambientDomain.domain.extension.Point)
    (hx : x ∈ interior (Q.pair parameterZero).ambientDomain.domain.carrier) :
    letI := totalFamilyChartedSpace hδ C hzero hjoint
    ContMDiffAt (familyModel (2 * n)) (familyModel (k + 1)) ∞
      (Q.ambientNativeTotalEquiv e b R hsquare hδ C q hqnative hqend).symm
      (t, (Q.pair parameterZero).ambientCompletion.inclusion.map x) := by
  let D := (Q.pair parameterZero).ambientDomain.domain
  let y : D.Point := ⟨x, interior_subset hx⟩
  have hy : (𝓡∂ (2 * n)).IsInteriorPoint y := by
    change y ∈ (𝓡∂ (2 * n)).interior D.Point
    rw [D.interior_eq_interior]
    exact hx
  let u : IntrinsicInterior.Point k M := ⟨(e parameterZero).symm y,
    (IsLocalDiffeomorphAt.isInteriorPoint_iff (by simp)
      ((e parameterZero).symm.isLocalDiffeomorph y)).mp hy⟩
  have h := Q.contMDiffAt_ambientNativeTotalEquiv_symm_interior e b R hsquare hδ C q
    hqnative hqend hdim hR hboundary hzero hjoint hmix t u
  simpa only [ambientNativeInteriorReferenceMap, u, Diffeomorph.apply_symm_apply] using h

end Inverse

end FsFltz.Geometry.PairDeformation
