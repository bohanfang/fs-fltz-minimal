import FsFltz.Geometry.NativeCompactFormRestriction
import FsFltz.Geometry.BoundaryPresentationBridge
import FsFltz.Geometry.BoundaryIntrinsicEquiv
import FsFltz.Geometry.IntrinsicPairFamilyTransport
import FsFltz.Geometry.IntrinsicZeroNativeRibbonFamily
import FsFltz.Geometry.IntrinsicNativeCompactDiffeomorph
import FsFltz.Geometry.CompletionFamilyEquations

/-!
# Native restriction of ribbon maps and their full witnessing equation

Source: `geoemtric-part-fsf.tex`, conventions 119–122, `def:pair`,
132–160, `def:chain`, 163–169, and `sec:lean`, 788–814.
Restriction to the actual compact carrier has target-valued real chart
extensions through spatial boundary points and parameter endpoints. The
boundary witness and the full ribbon primitive equation are retained.
These are soundness producers for existing encoded data; they construct
neither a toric comparison chain nor a new target proposition.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry.CompactDomain

variable {k d : ℕ} (D : CompactDomain (k + 1)) (N : SmoothManifold d)

/-- Restriction of an actual jointly smooth map family has local
manifold-valued extensions on real open chart neighborhoods, including at
the native boundary and both interval endpoints. -/
theorem isLocallyExtendibleMapFamily_restrict
    (f : Parameter → D.extension.Point → N.Point)
    (hf : D.extension.IsSmoothIntervalMapFamily N f) :
    IntrinsicLiouville.IsLocallyExtendibleMapFamily (k := k) N
      (fun t (x : D.Point) => f t x.val) := by
  obtain ⟨f', ⟨V, hV, hVcover, hf'⟩, heq⟩ := hf
  rintro e ⟨c, rfl⟩ t x hx
  let P : Set (ℝ × Model (k + 1)) := univ ×ˢ c.extension.target
  let q : ℝ × Model (k + 1) → ℝ × D.extension.Point :=
    fun p => (p.1, c.extension.invFun p.2)
  have hP : IsOpen P := isOpen_univ.prod c.extension.open_target
  have hq : ContMDiffOn 𝓘(ℝ, ℝ × Model (k + 1))
      (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model (k + 1))) ∞ q P :=
    contDiff_fst.contMDiff.contMDiffOn.prodMk
      (c.extension.contMDiffOn_invFun.comp contDiff_snd.contMDiff.contMDiffOn
        (fun _ hp => hp.2))
  let U : TopologicalSpace.Opens (ℝ × Model (k + 1)) :=
    ⟨P ∩ q ⁻¹' V, hq.continuousOn.isOpen_inter_preimage hP hV⟩
  have hy : c.chart.extend (𝓡∂ (k + 1)) x ∈
      (c.chart.extend (𝓡∂ (k + 1))).target :=
    (c.chart.extend (𝓡∂ (k + 1))).map_source
      (by simpa only [c.chart.extend_source] using hx)
  have htx : (t.val, c.chart.extend (𝓡∂ (k + 1)) x) ∈ U := by
    refine ⟨⟨mem_univ _, (c.extend_target_eq D ▸ hy).1⟩, ?_⟩
    change (t.val, c.extension.invFun (c.chart.extend (𝓡∂ (k + 1)) x)) ∈ V
    rw [← c.val_extend_symm D hy, c.chart.extend_left_inv hx]
    exact hVcover ⟨t.property, mem_univ _⟩
  let β : U → N.Point := fun p => f' p.val.1 (c.extension.invFun p.val.2)
  have hβ : ContMDiff 𝓘(ℝ, ℝ × Model (k + 1)) 𝓘(ℝ, Model d) ∞ β := by
    intro p
    exact ((hf'.contMDiffAt (hV.mem_nhds p.property.2)).comp _
      (hq.contMDiffAt (hP.mem_nhds p.property.1))).comp p
        _root_.contMDiff_subtype_val.contMDiffAt
  refine ⟨U, htx, β, hβ, ?_⟩
  intro s y hy hsy
  have hyt : c.chart.extend (𝓡∂ (k + 1)) y ∈
      (c.chart.extend (𝓡∂ (k + 1))).target :=
    (c.chart.extend (𝓡∂ (k + 1))).map_source
      (by simpa only [c.chart.extend_source] using hy)
  change f' s.val (c.extension.invFun (c.chart.extend (𝓡∂ (k + 1)) y)) = f s y.val
  rw [← c.val_extend_symm D hyt, c.chart.extend_left_inv hy, heq s]

/-- A carrier map with an actual smooth ambient extension has real source
and target chart germs. This also applies to a specified inverse map, using
its own ambient neighborhood. -/
theorem isLocallyExtendibleNativeMap_of_ambientRestriction
    (E : CompactDomain (k + 1))
    (f : D.extension.Point → E.extension.Point) (h : D.Point → E.Point)
    (W : Set D.extension.Point) (hW : IsOpen W) (hcover : D.carrier ⊆ W)
    (hf : ContMDiffOn 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ f W)
    (hsquare : ∀ x, f x.val = (h x).val) :
    IntrinsicLiouville.IsLocallyExtendibleNativeMap (k := k) h := by
  rintro e ⟨c, rfl⟩ x hx a ⟨c', rfl⟩ hax
  let S : Set (Model (k + 1)) := c.extension.target ∩ c.extension.invFun ⁻¹' W
  have hS : IsOpen S := c.extension.contMDiffOn_invFun.continuousOn.isOpen_inter_preimage
    c.extension.open_target hW
  let g : Model (k + 1) → E.extension.Point := f ∘ c.extension.invFun
  have hg : ContMDiffOn 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ g S :=
    hf.comp (c.extension.contMDiffOn_invFun.mono inter_subset_left) (fun _ hy => hy.2)
  let U : Set (Model (k + 1)) := S ∩ g ⁻¹' c'.extension.source
  have hU : IsOpen U := hg.continuousOn.isOpen_inter_preimage hS c'.extension.open_source
  have hcx : c.chart.extend (𝓡∂ (k + 1)) x ∈
      (c.chart.extend (𝓡∂ (k + 1))).target :=
    (c.chart.extend (𝓡∂ (k + 1))).map_source
      (by simpa only [c.chart.extend_source] using hx)
  have hval : c.extension.invFun (c.chart.extend (𝓡∂ (k + 1)) x) = x.val := by
    rw [← c.val_extend_symm D hcx, c.chart.extend_left_inv hx]
  refine ⟨U, c'.extension ∘ g, hU, ?_, ?_, ?_⟩
  · refine ⟨⟨(c.extend_target_eq D ▸ hcx).1, ?_⟩, ?_⟩
    · change c.extension.invFun (c.chart.extend (𝓡∂ (k + 1)) x) ∈ W
      rw [hval]
      exact hcover x.property
    · change f (c.extension.invFun (c.chart.extend (𝓡∂ (k + 1)) x)) ∈ c'.extension.source
      rw [hval, hsquare]
      rwa [c'.source_eq] at hax
  · exact (c'.extension.contMDiffOn_toFun.comp (hg.mono inter_subset_left)
      (fun _ hy => hy.2)).contDiffOn
  · intro y hy hyU
    have hcy : c.chart.extend (𝓡∂ (k + 1)) y ∈
        (c.chart.extend (𝓡∂ (k + 1))).target :=
      (c.chart.extend (𝓡∂ (k + 1))).map_source
        (by simpa only [c.chart.extend_source] using hy)
    have hvaly : c.extension.invFun (c.chart.extend (𝓡∂ (k + 1)) y) = y.val := by
      rw [← c.val_extend_symm D hcy, c.chart.extend_left_inv hy]
    have hay : h y ∈ c'.chart.source := by
      rw [c'.source_eq]
      have hp : g (c.chart.extend (𝓡∂ (k + 1)) y) ∈ c'.extension.source := hyU.2
      simpa only [g, Function.comp_apply, hvaly, hsquare, mem_preimage] using hp
    change c'.extension (f (c.extension.invFun (c.chart.extend (𝓡∂ (k + 1)) y))) =
      (c'.chart (h y)).val
    rw [hvaly, hsquare, c'.toFun_eq _ hay]

end FsFltz.Geometry.CompactDomain





namespace FsFltz.Geometry.SmoothManifold

/-- The coefficient extension already carried by an encoded scalar family
produces actual local manifold germs. No extra off-interval assumption is
required of its prescribed values. -/
theorem isLocallyExtendibleIntervalScalarFamily_of_smoothIntervalFamily
    {d : ℕ} (M : SmoothManifold d) (b : Parameter → M.Point → ℝ)
    (hb : M.IsSmoothIntervalScalarFamily b) :
    M.IsLocallyExtendibleIntervalScalarFamily b := by
  obtain ⟨b', hb', heq⟩ := hb
  intro t x
  let c := chartAt (Model d) x
  obtain ⟨V, hV, hVcover, hcoeff⟩ := hb' x
  let P : Set (ℝ × M.Point) := univ ×ˢ c.source
  let q : ℝ × M.Point → ℝ × Model d := fun p => (p.1, c p.2)
  have hP : IsOpen P := isOpen_univ.prod c.open_source
  have hq : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model d))
      𝓘(ℝ, ℝ × Model d) ∞ q P :=
    contMDiff_fst.contMDiffOn.prodMk_space
      ((contMDiffOn_chart (I := 𝓘(ℝ, Model d)) (n := ∞) (x := x)).comp
        contMDiff_snd.contMDiffOn (fun _ hp => hp.2))
  let U : Set (ℝ × M.Point) := P ∩ q ⁻¹' V
  have hU : IsOpen U := hq.continuousOn.isOpen_inter_preimage hP hV
  let g : ℝ × M.Point → ℝ := fun p => b' p.1 (c.symm (c p.2))
  refine ⟨U, g, hU, ⟨⟨mem_univ _, mem_chart_source _ _⟩,
    hVcover ⟨t.property, mem_chart_target _ _⟩⟩, ?_, ?_⟩
  · exact hcoeff.contMDiffOn.comp (hq.mono inter_subset_left) (fun _ hp => hp.2)
  · intro s y hy
    change b' s.val (c.symm (c y)) = b s y
    rw [c.left_inv hy.1.2, heq s]

end FsFltz.Geometry.SmoothManifold

namespace FsFltz.Geometry.CompactDomain

/-- The actual compact ribbon map, with values in the independently
constructed smooth frontier of the ambient compact domain. -/
def nativeRibbonMap {a k : ℕ} (D : CompactDomain (a + 1))
    (F : CompactDomain (k + 1)) (j : F.extension.Point → D.boundary.Point) :
    F.Point → D.FrontierPoint := fun x => D.boundaryDiffeomorph (j x.val)

/-- The prescribed positive witness on the actual intrinsic frontier. -/
def nativeBoundaryWitness {a : ℕ} (D : CompactDomain (a + 1))
    (b : D.boundary.Point → ℝ) : D.FrontierPoint → ℝ :=
  b ∘ D.boundaryDiffeomorph.symm

theorem nativeBoundaryWitness_positive {a : ℕ} (D : CompactDomain (a + 1))
    (b : D.boundary.Point → ℝ) (hb : ∀ x, 0 < b x) (x : D.FrontierPoint) :
    0 < D.nativeBoundaryWitness b x := hb _

/-- Joint ribbon restrictions retain the prescribed map in the actual
intrinsic frontier; its germs are real open in both time and space. -/
theorem nativeRibbonMapFamily_extendible {a k : ℕ} (D : CompactDomain (a + 1))
    (F : CompactDomain (k + 1))
    (j : Parameter → F.extension.Point → D.boundary.Point)
    (hj : F.extension.IsSmoothIntervalMapFamily D.boundary j) :
    IntrinsicLiouville.IsLocallyExtendibleMapFamily (k := k) D.intrinsicBoundary
      (fun t => D.nativeRibbonMap F (j t)) :=
  (F.isLocallyExtendibleMapFamily_restrict D.boundary j hj).comp_contMDiff
    D.boundary D.intrinsicBoundary _ D.boundaryDiffeomorph D.boundaryDiffeomorph.contMDiff

/-- The prescribed boundary scalar family has real local germs on the
actual intrinsic boundary, with all its interval values unchanged. -/
theorem nativeBoundaryWitnessFamily_extendible {a : ℕ} (D : CompactDomain (a + 1))
    (b : Parameter → D.boundary.Point → ℝ)
    (hb : D.boundary.IsSmoothIntervalScalarFamily b) :
    D.intrinsicBoundary.IsLocallyExtendibleIntervalScalarFamily
      (fun t => D.nativeBoundaryWitness (b t)) :=
  SmoothManifold.IsLocallyExtendibleIntervalScalarFamily.comp_contMDiff
    D.intrinsicBoundary D.boundary b
    (D.boundary.isLocallyExtendibleIntervalScalarFamily_of_smoothIntervalFamily b hb)
    D.boundaryDiffeomorph.symm D.boundaryDiffeomorph.symm.contMDiff

/-- The entire witnessing equation restricts to every compact point and
every native tangent direction. Both forms and the ribbon map are actual
differential pullbacks, including at the ribbon boundary. -/
theorem nativeRibbonMap_witness_pullback {a k : ℕ} (D : CompactDomain (a + 1))
    (F : CompactDomain (k + 1)) (j : F.extension.SmoothMap D.boundary)
    (b : D.boundary.Point → ℝ) (lam : D.extension.Form 1) (mu : F.extension.Form 1)
    (hribbon : ∀ x ∈ F.carrier,
      F.extension.pullback D.boundary j
        (fun y => b y • D.boundaryForm lam y) x = mu x) (x : F.Point) :
    (D.nativeBoundaryWitness b (D.nativeRibbonMap F j x) •
      D.intrinsicBoundaryForm lam (D.nativeRibbonMap F j x)).compContinuousLinearMap
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model a) (D.nativeRibbonMap F j) x) =
      F.restrictForm mu x := by
  let f : F.Point → D.boundary.Point := fun y => j y.val
  have hf : ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, Model a) ∞ f :=
    j.contMDiff.comp F.contMDiff_subtype_val
  have hd₁ := mfderiv_comp (f := (Subtype.val : F.Point → F.extension.Point))
    (g := j) x (j.contMDiff.mdifferentiableAt (by simp))
      (F.contMDiff_subtype_val.mdifferentiableAt (by simp))
  have hd₂ := mfderiv_comp (f := f) (g := D.boundaryDiffeomorph) x
    (D.boundaryDiffeomorph.contMDiff.mdifferentiableAt (by simp))
      (hf.mdifferentiableAt (by simp))
  change mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model a) (D.nativeRibbonMap F j) x = _ at hd₂
  change mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model a) f x = _ at hd₁
  erw [hd₁] at hd₂
  have hb : D.nativeBoundaryWitness b (D.nativeRibbonMap F j x) = b (j x.val) :=
    congrArg b (D.boundaryDiffeomorph.symm_apply_apply (j x.val))
  erw [hb, hd₂]
  ext vs
  have hp := congrArg (fun A => A (fun i =>
    mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model a) j x.val
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1))
        (Subtype.val : F.Point → F.extension.Point) x (vs i))))
    (congrFun (D.pullback_intrinsicBoundaryForm lam) (j x.val))
  have hr := congrArg (fun A => A (fun i =>
    mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1))
      (Subtype.val : F.Point → F.extension.Point) x (vs i))) (hribbon x.val x.property)
  change b (j x.val) * D.intrinsicBoundaryForm lam (D.boundaryDiffeomorph (j x.val))
    (fun i => mfderiv 𝓘(ℝ, Model a) 𝓘(ℝ, Model a) D.boundaryDiffeomorph (j x.val)
      (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model a) j x.val
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1))
          (Subtype.val : F.Point → F.extension.Point) x (vs i)))) = _
  exact (congrArg (fun r : ℝ => b (j x.val) * r) hp).trans hr

end FsFltz.Geometry.CompactDomain


namespace FsFltz.Geometry.CompactDomain

/-- In dimension zero the actual discrete carrier retains genuine local
real-time target-valued germs, including at both interval endpoints. -/
theorem zero_isLocallyExtendibleMapFamily_restrict {d : ℕ} (D : CompactDomain 0)
    (N : SmoothManifold d) (f : Parameter → D.extension.Point → N.Point)
    (hf : D.extension.IsSmoothIntervalMapFamily N f) :
    IntrinsicZeroLiouville.IsLocallyExtendibleRibbonMapFamily N
      (fun t (x : D.Point) => f t x.val) := by
  obtain ⟨f', ⟨V, hV, hVcover, hf'⟩, heq⟩ := hf
  let q : ℝ × D.Point → ℝ × D.extension.Point := fun p => (p.1, p.2.val)
  have hq : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model 0))
      (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model 0)) ∞ q :=
    contMDiff_fst.prodMk (D.zero_contMDiff_subtype_val.comp contMDiff_snd)
  let U : TopologicalSpace.Opens (ℝ × D.Point) := ⟨q ⁻¹' V, hV.preimage hq.continuous⟩
  let g : U → N.Point := fun p => f' p.val.1 p.val.2.val
  have hg : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model 0)) 𝓘(ℝ, Model d) ∞ g := by
    intro p
    exact ((hf'.contMDiffAt (hV.mem_nhds p.property)).comp _ hq.contMDiffAt).comp p
      _root_.contMDiff_subtype_val.contMDiffAt
  intro t x
  refine ⟨U, hVcover ⟨t.property, mem_univ _⟩, g, hg, ?_⟩
  intro s y hy
  exact congrFun (heq s) y.val

/-- Actual differential restriction to a zero-dimensional native carrier. -/
def zeroRestrictForm (D : CompactDomain 0) {r : ℕ} (η : D.extension.Form r) :
    (x : D.Point) → TangentSpace 𝓘(ℝ, Model 0) x [⋀^Fin r]→L[ℝ] ℝ :=
  fun x => (η x.val).compContinuousLinearMap
    (mfderiv 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0)
      (Subtype.val : D.Point → D.extension.Point) x)

/-- The zero-dimensional ribbon map into the actual smooth frontier. -/
def nativeZeroRibbonMap {a : ℕ} (D : CompactDomain (a + 1)) (F : CompactDomain 0)
    (j : F.extension.Point → D.boundary.Point) : F.Point → D.FrontierPoint :=
  fun x => D.boundaryDiffeomorph (j x.val)

theorem nativeZeroRibbonMapFamily_extendible {a : ℕ} (D : CompactDomain (a + 1))
    (F : CompactDomain 0) (j : Parameter → F.extension.Point → D.boundary.Point)
    (hj : F.extension.IsSmoothIntervalMapFamily D.boundary j) :
    IntrinsicZeroLiouville.IsLocallyExtendibleRibbonMapFamily D.intrinsicBoundary
      (fun t => D.nativeZeroRibbonMap F (j t)) := by
  intro t x
  obtain ⟨U, hxU, g, hg, heq⟩ := F.zero_isLocallyExtendibleMapFamily_restrict D.boundary j hj t x
  exact ⟨U, hxU, D.boundaryDiffeomorph ∘ g,
    D.boundaryDiffeomorph.contMDiff.comp hg,
    fun s y hy => congrArg D.boundaryDiffeomorph (heq s y hy)⟩

/-- Both sides of the full witnessing equation vanish on a
zero-dimensional ribbon's tangent space. The map and witness themselves
are still the exact prescribed data, and are not replaced by an empty law. -/
theorem nativeZeroRibbonMap_witness_pullback {a : ℕ} (D : CompactDomain (a + 1))
    (F : CompactDomain 0) (j : F.extension.Point → D.boundary.Point)
    (b : D.boundary.Point → ℝ) (lam : D.extension.Form 1) (mu : F.extension.Form 1)
    (x : F.Point) :
    (D.nativeBoundaryWitness b (D.nativeZeroRibbonMap F j x) •
      D.intrinsicBoundaryForm lam (D.nativeZeroRibbonMap F j x)).compContinuousLinearMap
        (mfderiv 𝓘(ℝ, Model 0) 𝓘(ℝ, Model a) (D.nativeZeroRibbonMap F j) x) =
      F.zeroRestrictForm mu x := by
  ext vs
  have hvs : vs = 0 := funext (fun _ => PiLp.ext (fun i => Fin.elim0 i))
  rw [hvs]
  simp

end FsFltz.Geometry.CompactDomain


namespace FsFltz.Geometry.PairDeformation

/-- The exact ribbon map on the deformation's fixed extension spaces. -/
def fixedRibbonMap {n : ℕ} (Q : PairDeformation n) (t : Parameter) :
    (Q.pair parameterZero).ribbonDomain.domain.extension.SmoothMap
      (Q.pair parameterZero).ambientDomain.domain.boundary :=
  ⟨fun x => (Q.ambientPresentation t).boundaryEquiv.symm
      ((Q.pair t).ribbonEmbedding.map ((Q.ribbonPresentation t).extensionEquiv x)),
    (Q.ambientPresentation t).boundaryEquiv.symm.contMDiff.comp
      ((Q.pair t).ribbonEmbedding.map.contMDiff.comp
        (Q.ribbonPresentation t).extensionEquiv.contMDiff)⟩

/-- The exact witness on the deformation's fixed boundary presentation. -/
def fixedWitness {n : ℕ} (Q : PairDeformation n) (t : Parameter) :
    (Q.pair parameterZero).ambientDomain.domain.boundary.Point → ℝ :=
  fun x => (Q.pair t).witness ((Q.ambientPresentation t).boundaryEquiv x)

theorem fixedWitness_positive {n : ℕ} (Q : PairDeformation n) (t : Parameter)
    (x : (Q.pair parameterZero).ambientDomain.domain.boundary.Point) :
    0 < Q.fixedWitness t x := (Q.pair t).positive_witness _

/-- The actual fixed-boundary witness has real local parameter germs. -/
theorem fixedWitness_extendible {n : ℕ} (Q : PairDeformation n) :
    (Q.pair parameterZero).ambientDomain.domain.boundary.IsLocallyExtendibleIntervalScalarFamily
      Q.fixedWitness :=
  SmoothManifold.isLocallyExtendibleIntervalScalarFamily_of_smoothIntervalFamily
    _ _ Q.witness_smooth

/-- The transported ribbon primitive obeys the full witnessing equation
on the fixed source carrier. This derives from the boundary presentation
square and the original full covector equation at the transported point. -/
theorem fixedRibbonMap_witness_pullback {n : ℕ} (Q : PairDeformation n) (t : Parameter)
    (x : (Q.pair parameterZero).ribbonDomain.domain.extension.Point)
    (hx : x ∈ (Q.pair parameterZero).ribbonDomain.domain.carrier) :
    (Q.pair parameterZero).ribbonDomain.domain.extension.pullback
      (Q.pair parameterZero).ambientDomain.domain.boundary (Q.fixedRibbonMap t)
      (fun y => Q.fixedWitness t y •
        (Q.pair parameterZero).ambientDomain.domain.boundaryForm
          ((Q.pair parameterZero).ambientDomain.domain.extension.pullback
            (Q.pair t).ambientDomain.domain.extension (Q.ambientPresentation t).extensionEquiv
            (Q.pair t).ambientDomain.liouville.primitive) y) x =
      (Q.pair parameterZero).ribbonDomain.domain.extension.pullback
        (Q.pair t).ribbonDomain.domain.extension (Q.ribbonPresentation t).extensionEquiv
        (Q.pair t).ribbonDomain.liouville.primitive x := by
  let A := (Q.pair parameterZero).ambientDomain.domain
  let F := (Q.pair parameterZero).ribbonDomain.domain
  let P := Q.pair t
  let B := (Q.ambientPresentation t).boundaryEquiv
  let R := (Q.ribbonPresentation t).extensionEquiv
  let α := P.ambientDomain.domain.boundaryForm P.ambientDomain.liouville.primitive
  rw [(Q.ambientPresentation t).boundaryForm_pullback]
  change F.extension.pullback A.boundary (Q.fixedRibbonMap t)
    (A.boundary.pullback P.ambientDomain.domain.boundary B (fun y => P.witness y • α y)) x = _
  rw [← F.extension.pullback_comp A.boundary P.ambientDomain.domain.boundary
    ((Q.fixedRibbonMap t).contMDiff.mdifferentiable (by simp))
    (B.contMDiff.mdifferentiable (by simp))]
  have hs : (B ∘ Q.fixedRibbonMap t : F.extension.Point → P.ambientDomain.domain.boundary.Point) =
      P.ribbonEmbedding.map ∘ R := by
    funext y
    exact B.apply_symm_apply _
  rw [hs, F.extension.pullback_comp P.ribbonDomain.domain.extension P.ambientDomain.domain.boundary
    (R.contMDiff.mdifferentiable (by simp))
    (P.ribbonEmbedding.map.contMDiff.mdifferentiable (by simp))]
  ext vs
  exact congrArg (fun A => A (fun i =>
    mfderiv 𝓘(ℝ, Model (2 * n - 2)) 𝓘(ℝ, Model (2 * n - 2)) R x (vs i)))
    (P.ribbon_primitive (R x) (((Q.ribbonPresentation t).mem_carrier_iff x).mpr hx))

private theorem ribbonMap_native_extendible_reindex {d k e : ℕ}
    (F : CompactDomain d) (N : SmoothManifold e) (hdim : d = k + 1)
    (f : Parameter → F.extension.Point → N.Point)
    (hf : F.extension.IsSmoothIntervalMapFamily N f) :
    let F' : CompactDomain (k + 1) := hdim ▸ F
    let f' : Parameter → F'.extension.Point → N.Point :=
      hdim.rec (motive := fun _ h => Parameter → (h ▸ F).extension.Point → N.Point) f
    @IntrinsicLiouville.IsLocallyExtendibleMapFamily k e F'.Point inferInstance
      (CompactDomain.halfSpaceChartedSpace F') N (fun t x => f' t x.val) := by
  cases hdim
  exact F.isLocallyExtendibleMapFamily_restrict N f hf

/-- The encoded deformation's exact joint ribbon map restricts to real
native germs on its fixed compact ribbon, without any additional family
regularity premise. -/
theorem ribbonMap_native_extendible {n k : ℕ} (Q : PairDeformation n)
    (hdim : 2 * n - 2 = k + 1) :
    let F₀ := (Q.pair parameterZero).ribbonDomain.domain
    let N := (Q.pair parameterZero).ambientDomain.domain.boundary
    let F : CompactDomain (k + 1) := hdim ▸ F₀
    let j : Parameter → F.extension.Point → N.Point :=
      hdim.rec (motive := fun _ h => Parameter → (h ▸ F₀).extension.Point → N.Point)
        (fun t => Q.fixedRibbonMap t)
    @IntrinsicLiouville.IsLocallyExtendibleMapFamily k (2 * n - 1) F.Point inferInstance
      (CompactDomain.halfSpaceChartedSpace F) N (fun t x => j t x.val) :=
  ribbonMap_native_extendible_reindex _ _ hdim _ Q.ribbonEmbedding_smooth

/-- Dimension one retains the actual zero-dimensional compact ribbon and
the same jointly smooth map, including its interval endpoint germs. -/
theorem zeroRibbonMap_native_extendible (Q : PairDeformation 1) :
    IntrinsicZeroLiouville.IsLocallyExtendibleRibbonMapFamily
      (Q.pair parameterZero).ambientDomain.domain.boundary
      (fun t (x : (Q.pair parameterZero).ribbonDomain.domain.Point) => Q.fixedRibbonMap t x.val) :=
  (Q.pair parameterZero).ribbonDomain.domain.zero_isLocallyExtendibleMapFamily_restrict
    _ _ Q.ribbonEmbedding_smooth

end FsFltz.Geometry.PairDeformation
