import FsFltz.Geometry.IntrinsicCollarGluingInclusion

/-!
# Actual differentials of the native attachment maps

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 119–160, and `sec:lean`,
lines 783–814. The rank results use smooth inverse germs and actual chain
rules. No rank assumption is added to the native collar data.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff
open Set Filter Topology

namespace FsFltz.Geometry.IntrinsicCollarGluing

variable {k : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]
  {δ : ℝ} (hδ : 0 < δ)
  (C : ℝ × IntrinsicBoundary.Point k M → M)
  (hemb : IsOpenEmbedding (fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val))
  (hC : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) (𝓡∂ (k + 1)) ∞ C
    (Half δ (IntrinsicBoundary.Point k M)))
  (hboundary : ∀ p : Half δ (IntrinsicBoundary.Point k M),
    (𝓡∂ (k + 1)).IsBoundaryPoint (C p.val) ↔ p.val.1 = 0)
  (hinv : ∀ p ∈ Half δ (IntrinsicBoundary.Point k M),
    ∃ g : M → ℝ × IntrinsicBoundary.Point k M,
      ContMDiffAt (𝓡∂ (k + 1)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) ∞ g (C p) ∧
        ∀ᶠ q in 𝓝[Half δ (IntrinsicBoundary.Point k M)] p, g (C q) = q)
  (hzero : ∀ b : IntrinsicBoundary.Point k M, C (0, b) = b.val)

local instance differentialBandCharts : ChartedSpace (Model (k + 1))
    (Band δ (IntrinsicBoundary.Point k M)) :=
  bandChartedSpace δ

local instance differentialBandSmooth : IsManifold 𝓘(ℝ, Model (k + 1)) ∞
    (Band δ (IntrinsicBoundary.Point k M)) :=
  band_isManifold δ

include hC hinv in
/-- The actual interior patch differential is injective. -/
theorem injective_mfderiv_interiorIn (x : IntrinsicInterior.Point k M) :
    letI := extensionChartedSpace hδ C hemb hboundary hzero
    Function.Injective (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1))
      (interiorIn (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val)) x) :=
  injective_mfderiv_openCover_inclusion _ _ (native_open_cover hδ C hzero)
    (extension_isManifold hδ C hemb hC hboundary hinv hzero) x

include hC hinv in
/-- The actual interior patch differential is bijective. -/
theorem bijective_mfderiv_interiorIn (x : IntrinsicInterior.Point k M) :
    letI := extensionChartedSpace hδ C hemb hboundary hzero
    Function.Bijective (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1))
      (interiorIn (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val)) x) := by
  let := extensionChartedSpace hδ C hemb hboundary hzero
  have hi := injective_mfderiv_interiorIn hδ C hemb hC hboundary hinv hzero x
  exact ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩

include hC hinv in
/-- The cylinder differential is injective because its constructed smooth
inverse germ is an actual left inverse near each cylinder point. -/
theorem injective_mfderiv_cylinder (p : Band δ (IntrinsicBoundary.Point k M)) :
    letI := extensionChartedSpace hδ C hemb hboundary hzero
    Function.Injective (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1))
      (cylinder (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val)) p) := by
  let := extensionChartedSpace hδ C hemb hboundary hzero
  let := extension_isManifold hδ C hemb hC hboundary hinv hzero
  let j := cylinder (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val)
  obtain ⟨g, hg, hgp, heq⟩ := cylinder_inverse_germ hδ C hemb hC hboundary hinv hzero p
  have hji := cylinder_injective
    (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) hemb.injective
  have hleft : g ∘ j =ᶠ[𝓝 p] id := by
    have hn := (continuous_cylinder
      (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val)).continuousAt.eventually heq
    filter_upwards [hn] with q hq
    exact hji hq
  have hd := mfderiv_comp p (hg.mdifferentiableAt (by simp))
    ((contMDiff_cylinder hδ C hemb hC hboundary hinv hzero).mdifferentiableAt (by simp))
  have hid : mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) (g ∘ j) p =
      ContinuousLinearMap.id ℝ _ := by
    exact (hleft.mfderiv_eq (I := 𝓘(ℝ, Model (k + 1))) (I' := 𝓘(ℝ, Model (k + 1)))).trans
      (by rw [mfderiv_id]; rfl)
  rw [hid] at hd
  intro v w hvw
  have heval (a : TangentSpace 𝓘(ℝ, Model (k + 1)) p) := congrArg (fun A => A a) hd
  exact (heval v).trans ((congrArg (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) g (j p)) hvw).trans
    (heval w).symm)

include hC hinv in
/-- The actual cylinder differential is an isomorphism of the equal finite-dimensional tangents. -/
theorem bijective_mfderiv_cylinder (p : Band δ (IntrinsicBoundary.Point k M)) :
    letI := extensionChartedSpace hδ C hemb hboundary hzero
    Function.Bijective (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1))
      (cylinder (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val)) p) := by
  let := extensionChartedSpace hδ C hemb hboundary hzero
  have hi := injective_mfderiv_cylinder hδ C hemb hC hboundary hinv hzero p
  exact ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩

/-- The native half collar has a unique full one-sided manifold differential. -/
theorem uniqueMDiffWithinAt_half (p : Half δ (IntrinsicBoundary.Point k M)) :
    UniqueMDiffWithinAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k))
      (Half δ (IntrinsicBoundary.Point k M)) p.val :=
  ((uniqueDiffOn_Ico 0 δ) _ p.property.1).uniqueMDiffWithinAt.prod
    (uniqueMDiffWithinAt_univ (I := 𝓘(ℝ, Model k)))

include hC in
/-- Differentiating a produced native left inverse shows its actual differential
is bijective, including at time zero. -/
theorem bijective_mfderiv_collar_inverse (p : Half δ (IntrinsicBoundary.Point k M))
    (g : M → ℝ × IntrinsicBoundary.Point k M)
    (hg : ContMDiffAt (𝓡∂ (k + 1)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) ∞ g (C p.val))
    (heq : g ∘ C =ᶠ[𝓝[Half δ (IntrinsicBoundary.Point k M)] p.val] id) :
    Function.Bijective (mfderiv (𝓡∂ (k + 1))
      (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) g (C p.val)) := by
  have hs := uniqueMDiffWithinAt_half p
  have hgp := heq.eq_of_nhdsWithin p.property
  change g (C p.val) = p.val at hgp
  have hid : mfderivWithin (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k))
      (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) (g ∘ C)
      (Half δ (IntrinsicBoundary.Point k M)) p.val = ContinuousLinearMap.id ℝ _ := by
    exact (heq.mfderivWithin_eq_of_mem
      (I := 𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) (I' := 𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) p.property).trans
        (by rw [mfderivWithin_id hs]; rfl)
  have hd := mfderivWithin_comp p.val
    ((hg.mdifferentiableAt (by simp)).mdifferentiableWithinAt (s := univ))
    ((hC p.val p.property).mdifferentiableWithinAt (by simp))
    (fun _ _ => mem_univ _) hs
  rw [mfderivWithin_univ, hid] at hd
  have hsurj : Function.Surjective (mfderiv (𝓡∂ (k + 1))
      (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) g (C p.val)) := by
    intro v
    refine ⟨mfderivWithin (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) (𝓡∂ (k + 1)) C
      (Half δ (IntrinsicBoundary.Point k M)) p.val v, ?_⟩
    exact (congrArg (fun A => A v) hd).symm
  have hfin : Module.finrank ℝ (Model (k + 1)) = Module.finrank ℝ (ℝ × Model k) := by
    simp [Model, Module.finrank_prod, Nat.add_comm]
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mpr hsurj, hsurj⟩

include hC hinv in
/-- The actual original inclusion has injective differential at every point
of the same half collar, including its boundary seam. -/
theorem injective_mfderiv_original_collar (p : Half δ (IntrinsicBoundary.Point k M)) :
    letI := extensionChartedSpace hδ C hemb hboundary hzero
    Function.Injective (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1))
      (original (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val)) (C p.val)) := by
  let := extensionChartedSpace hδ C hemb hboundary hzero
  let := extension_isManifold hδ C hemb hC hboundary hinv hzero
  let j := cylinder (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val)
  let o := original (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val)
  obtain ⟨g, hg, _, heq⟩ := original_cylinder_germ hδ C hemb hinv p
  have heq' : o =ᶠ[𝓝 (C p.val)] j ∘ g := heq
  let f : M → ℝ × IntrinsicBoundary.Point k M := Subtype.val ∘ g
  have hf : ContMDiffAt (𝓡∂ (k + 1)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) ∞ f (C p.val) :=
    (contMDiff_band_val δ).contMDiffAt.comp (C p.val) hg
  have hleft : f ∘ C =ᶠ[𝓝[Half δ (IntrinsicBoundary.Point k M)] p.val] id := by
    have hn := (hC p.val p.property).continuousWithinAt.eventually heq
    filter_upwards [hn, self_mem_nhdsWithin] with q hq hqs
    have hrel := original_collar_eq_cylinder hδ
      (fun r : Half δ (IntrinsicBoundary.Point k M) => C r.val) ⟨q, hqs⟩
    have hgg := cylinder_injective
      (fun r : Half δ (IntrinsicBoundary.Point k M) => C r.val) hemb.injective
        (hq.symm.trans hrel)
    exact congrArg Subtype.val hgg
  have hfi := (bijective_mfderiv_collar_inverse C hC p f hf hleft).1
  have hdval := mfderiv_comp (C p.val)
    ((contMDiff_band_val δ).mdifferentiableAt (by simp)) (hg.mdifferentiableAt (by simp))
  have hgi : Function.Injective (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) g (C p.val)) := by
    intro v w hvw
    apply hfi
    change mfderiv (𝓡∂ (k + 1)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) (Subtype.val ∘ g)
      (C p.val) v = _
    rw [hdval]
    exact congrArg (mfderiv 𝓘(ℝ, Model (k + 1))
      (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) Subtype.val (g (C p.val))) hvw
  have hd := mfderiv_comp (C p.val)
    ((contMDiff_cylinder hδ C hemb hC hboundary hinv hzero).mdifferentiableAt (by simp))
    (hg.mdifferentiableAt (by simp))
  have heqd : mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) o (C p.val) =
      mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) (j ∘ g) (C p.val) :=
    (heq'.mfderiv_eq (I := 𝓡∂ (k + 1)) (I' := 𝓘(ℝ, Model (k + 1)))).trans (by rfl)
  rw [heqd, hd]
  exact (injective_mfderiv_cylinder hδ C hemb hC hboundary hinv hzero (g (C p.val))).comp hgi

include hC hinv in
/-- The original native inclusion has injective actual differential everywhere. -/
theorem injective_mfderiv_original (x : M) :
    letI := extensionChartedSpace hδ C hemb hboundary hzero
    Function.Injective (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1))
      (original (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val)) x) := by
  let := extensionChartedSpace hδ C hemb hboundary hzero
  let := extension_isManifold hδ C hemb hC hboundary hinv hzero
  rcases (𝓡∂ (k + 1)).isInteriorPoint_or_isBoundaryPoint x with hx | hx
  · let u : IntrinsicInterior.Point k M := ⟨x, hx⟩
    have hd := mfderiv_comp u
      ((contMDiff_original hδ C hemb hC hboundary hinv hzero).mdifferentiableAt (by simp))
      (IntrinsicInterior.contMDiff_val.mdifferentiableAt (by simp))
    have hi := injective_mfderiv_interiorIn hδ C hemb hC hboundary hinv hzero u
    have hs := (IntrinsicInterior.bijective_mfderiv_val u).2
    intro v w hvw
    obtain ⟨a, ha⟩ := hs v
    obtain ⟨b, hb⟩ := hs w
    apply (ha.symm.trans ?_).trans hb
    apply congrArg (mfderiv 𝓘(ℝ, Model (k + 1)) (𝓡∂ (k + 1)) Subtype.val u)
    apply hi
    change mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1))
      ((original (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val)) ∘ Subtype.val) u a =
        mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1))
          ((original (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val)) ∘ Subtype.val) u b
    rw [hd]
    change mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1))
      (original (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val)) x
      (mfderiv 𝓘(ℝ, Model (k + 1)) (𝓡∂ (k + 1)) Subtype.val u a) =
        mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1))
          (original (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val)) x
          (mfderiv 𝓘(ℝ, Model (k + 1)) (𝓡∂ (k + 1)) Subtype.val u b)
    rw [ha, hb]
    exact hvw
  · let b : IntrinsicBoundary.Point k M := ⟨x, hx⟩
    let p : Half δ (IntrinsicBoundary.Point k M) :=
      ⟨(0, b), ⟨le_rfl, hδ⟩, mem_univ _⟩
    have hi := injective_mfderiv_original_collar hδ C hemb hC hboundary hinv hzero p
    have hpx : C p.val = x := hzero b
    rwa [hpx] at hi

include hC hinv in
/-- The original inclusion identifies actual tangent spaces also along the seam. -/
theorem bijective_mfderiv_original (x : M) :
    letI := extensionChartedSpace hδ C hemb hboundary hzero
    Function.Bijective (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1))
      (original (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val)) x) := by
  let := extensionChartedSpace hδ C hemb hboundary hzero
  have hi := injective_mfderiv_original hδ C hemb hC hboundary hinv hzero x
  exact ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩

end FsFltz.Geometry.IntrinsicCollarGluing
