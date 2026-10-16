import FsFltz.Geometry.IntrinsicGluedForm

/-!
# Full original primitive preservation on the native collar quotient

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 119–160, and `sec:lean`,
lines 783–814. The actual original inclusion pulls the single glued primitive
back to the original native primitive, including the seam. The full one-sided
collar primitive law and the produced native inverse make the seam proof a
chain-rule calculation on all tangent vectors.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
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

local instance restrictionBandCharts : ChartedSpace (Model (k + 1))
    (Band δ (IntrinsicBoundary.Point k M)) := bandChartedSpace δ

local instance restrictionBandSmooth : IsManifold 𝓘(ℝ, Model (k + 1)) ∞
    (Band δ (IntrinsicBoundary.Point k M)) := band_isManifold δ

include hC hinv in
/-- The native one-sided collar differential is onto the full native tangent,
including at time zero. This follows from its produced smooth inverse. -/
theorem surjective_mfderivWithin_collar (p : Half δ (IntrinsicBoundary.Point k M)) :
    Function.Surjective (mfderivWithin (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k))
      (𝓡∂ (k + 1)) C (Half δ (IntrinsicBoundary.Point k M)) p.val) := by
  obtain ⟨g, hg, heq⟩ := hinv p.val p.property
  have heq' : g ∘ C =ᶠ[𝓝[Half δ (IntrinsicBoundary.Point k M)] p.val] id := heq
  have hgi := (bijective_mfderiv_collar_inverse C hC p g hg heq').1
  have hs := uniqueMDiffWithinAt_half p
  have hid : mfderivWithin (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k))
      (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) (g ∘ C)
      (Half δ (IntrinsicBoundary.Point k M)) p.val = ContinuousLinearMap.id ℝ _ := by
    exact (heq'.mfderivWithin_eq_of_mem
      (I := 𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) (I' := 𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k))
      p.property).trans (by rw [mfderivWithin_id hs]; rfl)
  have hd := mfderivWithin_comp p.val
    ((hg.mdifferentiableAt (by simp)).mdifferentiableWithinAt (s := univ))
    ((hC p.val p.property).mdifferentiableWithinAt (by simp))
    (fun _ _ => mem_univ _) hs
  rw [mfderivWithin_univ, hid] at hd
  intro v
  refine ⟨mfderiv (𝓡∂ (k + 1)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) g (C p.val) v, ?_⟩
  apply hgi
  exact (congrArg (fun A => A
    (mfderiv (𝓡∂ (k + 1)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) g (C p.val) v)) hd).symm

variable [T2Space M] [SecondCountableTopology M]

private theorem pullback_gluedPrimitive_original_collar
    (α : IntrinsicLiouville.Form k M 1)
    (hα : IntrinsicLiouville.IsLocallyExtendibleForm α)
    (Z : (x : M) → TangentSpace (𝓡∂ (k + 1)) x)
    (hZ : IntrinsicLiouville.Contraction α (IntrinsicLiouville.exteriorDerivative α) Z)
    (hode : ∀ y, IsMIntegralCurveOn (fun t => C (t, y)) (fun x => -Z x) (Ico 0 δ))
    (p : Half δ (IntrinsicBoundary.Point k M)) :
    letI := extensionChartedSpace hδ C hemb hboundary hzero
    (gluedPrimitive hδ C hemb hC hboundary hinv hzero α
      (original (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) (C p.val))).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1))
        (original (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val)) (C p.val)) =
      α (C p.val) := by
  let := extensionChartedSpace hδ C hemb hboundary hzero
  let := extension_isManifold hδ C hemb hC hboundary hinv hzero
  let j := cylinder (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val)
  let o := original (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val)
  let β := gluedPrimitive hδ C hemb hC hboundary hinv hzero α
  obtain ⟨g, hg, hgp, heq⟩ := original_cylinder_germ hδ C hemb hinv p
  have heq' : o =ᶠ[𝓝 (C p.val)] j ∘ g := heq
  have hop : o (C p.val) = j (g (C p.val)) := heq'.eq_of_nhds
  let f : M → ℝ × IntrinsicBoundary.Point k M := Subtype.val ∘ g
  have hf : ContMDiffAt (𝓡∂ (k + 1)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) ∞ f (C p.val) :=
    (contMDiff_band_val δ).contMDiffAt.comp (C p.val) hg
  have hleft : f ∘ C =ᶠ[𝓝[Half δ (IntrinsicBoundary.Point k M)] p.val] id := by
    have hn := (hC p.val p.property).continuousWithinAt.eventually heq
    filter_upwards [hn, self_mem_nhdsWithin] with q hq hqs
    have hrel := original_collar_eq_cylinder hδ
      (fun r : Half δ (IntrinsicBoundary.Point k M) => C r.val) ⟨q, hqs⟩
    exact congrArg Subtype.val (cylinder_injective
      (fun r : Half δ (IntrinsicBoundary.Point k M) => C r.val) hemb.injective
        (hq.symm.trans hrel))
  have hs := uniqueMDiffWithinAt_half p
  have hid : mfderivWithin (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k))
      (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) (f ∘ C)
      (Half δ (IntrinsicBoundary.Point k M)) p.val = ContinuousLinearMap.id ℝ _ := by
    exact (hleft.mfderivWithin_eq_of_mem
      (I := 𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) (I' := 𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k))
      p.property).trans (by rw [mfderivWithin_id hs]; rfl)
  have hd := mfderivWithin_comp p.val
    ((hf.mdifferentiableAt (by simp)).mdifferentiableWithinAt (s := univ))
    ((hC p.val p.property).mdifferentiableWithinAt (by simp))
    (fun _ _ => mem_univ _) hs
  rw [mfderivWithin_univ, hid] at hd
  have hdval := mfderiv_comp (C p.val)
    ((contMDiff_band_val δ).mdifferentiableAt (by simp)) (hg.mdifferentiableAt (by simp))
  have hproj := mfderiv_comp
    (I := 𝓘(ℝ, Model (k + 1))) (I' := 𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k))
    (I'' := 𝓘(ℝ, Model k))
    (f := (Subtype.val : Band δ (IntrinsicBoundary.Point k M) → _))
    (g := (Prod.snd : ℝ × IntrinsicBoundary.Point k M → _)) (g (C p.val))
    ((contMDiff_snd (n := ∞)).mdifferentiableAt (by simp))
    ((contMDiff_band_val δ).mdifferentiableAt (by simp))
  rw [mfderiv_snd] at hproj
  have hjg := mfderiv_comp (C p.val)
    ((contMDiff_cylinder hδ C hemb hC hboundary hinv hzero).mdifferentiableAt (by simp))
    (hg.mdifferentiableAt (by simp))
  have ho : mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) o (C p.val) =
      mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) (j ∘ g) (C p.val) :=
    (heq'.mfderiv_eq (I := 𝓡∂ (k + 1)) (I' := 𝓘(ℝ, Model (k + 1)))).trans (by rfl)
  have hrestrict := congrFun
    (pullback_gluedPrimitive_cylinder hδ C hemb hC hboundary hinv hzero α hα Z hZ hode)
    (g (C p.val))
  ext vs
  have hvs : vs = fun _ => vs 0 := by funext i; rw [Fin.eq_zero i]
  obtain ⟨w, hw⟩ := surjective_mfderivWithin_collar C hC hinv p (vs 0)
  let dC := mfderivWithin (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) (𝓡∂ (k + 1)) C
    (Half δ (IntrinsicBoundary.Point k M)) p.val
  let dg := mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) g (C p.val)
  have hv : mfderiv (𝓡∂ (k + 1)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) f
      (C p.val) (dC w) = w := (congrArg (fun A => A w) hd).symm
  have hsp : mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model k)
      boundaryProjection (g (C p.val)) (dg (dC w)) = w.2 := by
    change mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model k)
      (Prod.snd ∘ (Subtype.val : Band δ (IntrinsicBoundary.Point k M) → _))
      (g (C p.val)) (dg (dC w)) = w.2
    rw [hproj]
    change mfderiv (𝓡∂ (k + 1)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) (Subtype.val ∘ g)
      (C p.val) (dC w) = w at hv
    rw [hdval] at hv
    exact congrArg Prod.snd hv
  have hβ : β (o (C p.val)) (fun _ =>
      mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) o (C p.val) (dC w)) =
      cylinderPrimitive δ α (g (C p.val)) (fun _ => dg (dC w)) := by
    rw [hop, ho, hjg]
    exact congrArg (fun A => A (fun _ => dg (dC w))) hrestrict
  have hfull := IntrinsicLiouville.inward_boundary_pullbackWithin_eq_exp_mul_of_liouville
    α hα Z hZ C hδ hC hode hzero p.property.1 p.val.2 w.1 w.2
  rw [hvs]
  change β (o (C p.val)) (fun _ =>
    mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) o (C p.val) (vs 0)) =
      α (C p.val) (fun _ => vs 0)
  rw [← hw, hβ, cylinderPrimitive_eval, hsp, hgp]
  exact hfull.symm

/-- The actual original inclusion preserves the native primitive on every
native tangent, including all tangents based at the boundary seam. -/
theorem pullback_gluedPrimitive_original
    (α : IntrinsicLiouville.Form k M 1)
    (hα : IntrinsicLiouville.IsLocallyExtendibleForm α)
    (Z : (x : M) → TangentSpace (𝓡∂ (k + 1)) x)
    (hZ : IntrinsicLiouville.Contraction α (IntrinsicLiouville.exteriorDerivative α) Z)
    (hode : ∀ y, IsMIntegralCurveOn (fun t => C (t, y)) (fun x => -Z x) (Ico 0 δ)) :
    letI := extensionChartedSpace hδ C hemb hboundary hzero
    (fun x => (gluedPrimitive hδ C hemb hC hboundary hinv hzero α
      (original (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) x)).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1))
        (original (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val)) x)) = α := by
  let := extensionChartedSpace hδ C hemb hboundary hzero
  let := extension_isManifold hδ C hemb hC hboundary hinv hzero
  let o := original (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val)
  let β := gluedPrimitive hδ C hemb hC hboundary hinv hzero α
  funext x
  rcases (𝓡∂ (k + 1)).isInteriorPoint_or_isBoundaryPoint x with hx | hx
  · let u : IntrinsicInterior.Point k M := ⟨x, hx⟩
    have hrestrict := congrFun
      (pullback_gluedPrimitive_interior hδ C hemb hC hboundary hinv hzero α) u
    have hd := mfderiv_comp u
      ((contMDiff_original hδ C hemb hC hboundary hinv hzero).mdifferentiableAt (by simp))
      (IntrinsicInterior.contMDiff_val.mdifferentiableAt (by simp))
    ext vs
    have hvs : vs = fun _ => vs 0 := by funext i; rw [Fin.eq_zero i]
    obtain ⟨v, hv⟩ := (IntrinsicInterior.bijective_mfderiv_val u).2 (vs 0)
    have heval := congrArg (fun A => A (fun _ => v)) hrestrict
    change β (o x) (fun _ => mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1))
      (o ∘ (Subtype.val : IntrinsicInterior.Point k M → M)) u v) =
        α x (fun _ => mfderiv 𝓘(ℝ, Model (k + 1)) (𝓡∂ (k + 1))
          (Subtype.val : IntrinsicInterior.Point k M → M) u v) at heval
    rw [hd] at heval
    change β (o x) (fun _ => mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) o x
      (mfderiv 𝓘(ℝ, Model (k + 1)) (𝓡∂ (k + 1))
        (Subtype.val : IntrinsicInterior.Point k M → M) u v)) =
        α x (fun _ => mfderiv 𝓘(ℝ, Model (k + 1)) (𝓡∂ (k + 1))
          (Subtype.val : IntrinsicInterior.Point k M → M) u v) at heval
    rw [hv] at heval
    rw [hvs]
    exact heval
  · let b : IntrinsicBoundary.Point k M := ⟨x, hx⟩
    let p : Half δ (IntrinsicBoundary.Point k M) :=
      ⟨(0, b), ⟨le_rfl, hδ⟩, mem_univ _⟩
    have h := pullback_gluedPrimitive_original_collar hδ C hemb hC hboundary hinv hzero
      α hα Z hZ hode p
    have hp : C p.val = x := hzero b
    rwa [hp] at h

end FsFltz.Geometry.IntrinsicCollarGluing
