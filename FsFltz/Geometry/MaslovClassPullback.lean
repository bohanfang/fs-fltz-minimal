import FsFltz.Geometry.MaslovPullback
import FsFltz.Geometry.MaslovHomotopy
import FsFltz.Geometry.MaslovTransport

/-!
# Smooth pullback of ambient Maslov classes

Source: `geoemtric-part-fsf.tex`, `def:maslov`, lines 212–244;
`g:chain`, lines 407–413; `sec:lean`, lines 794–814.
The smooth extension of the whole family is produced from the actual marking
and chart derivatives. No pullback-homotopy or regularity certificate is an
input. Identification with the rank-one canonical bundle and independence
under a change of compatible complex structure remain separate foundations.
-/

noncomputable section
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry

namespace SmoothNearInterval

/-- Open local extensions assemble into one open extension. This does not
require a uniform parameter collar on a noncompact spatial set. -/
theorem of_local {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {s : Set E} {f : ℝ × E → F}
    (h : ∀ p ∈ parameterInterval ×ˢ s, ∃ U : Set (ℝ × E),
      IsOpen U ∧ p ∈ U ∧ ContDiffOn ℝ ∞ f U) : SmoothNearInterval s f := by
  let A := {U : Set (ℝ × E) // IsOpen U ∧ ContDiffOn ℝ ∞ f U}
  refine ⟨⋃ U : A, U.val, isOpen_iUnion (fun U => U.property.1), ?_, ?_⟩
  · intro p hp
    rcases h p hp with ⟨U, hU, hpU, hfU⟩
    exact mem_iUnion.mpr ⟨⟨U, hU, hfU⟩, hpU⟩
  · exact ContDiffOn.iUnion_of_isOpen (fun U => U.property.2) (fun U => U.property.1)

end SmoothNearInterval

private def markingChartDomain {d : ℕ} (M N : SmoothManifold d)
    (f : M.SmoothEquiv N) (a : M.Point) (b : N.Point) : Set (Model d) :=
  (chartAt (Model d) a).target ∩
    (f ∘ (chartAt (Model d) a).symm) ⁻¹' (chartAt (Model d) b).source

private theorem isOpen_markingChartDomain {d : ℕ} (M N : SmoothManifold d)
    (f : M.SmoothEquiv N) (a : M.Point) (b : N.Point) :
    IsOpen (markingChartDomain M N f a b) :=
  (f.contMDiff.continuous.comp_continuousOn
    (chartAt (Model d) a).continuousOn_symm).isOpen_inter_preimage
      (chartAt (Model d) a).open_target (chartAt (Model d) b).open_source

set_option backward.isDefEq.respectTransparency false in
private theorem contDiffOn_markingChart {d : ℕ} (M N : SmoothManifold d)
    (f : M.SmoothEquiv N) (a : M.Point) (b : N.Point) :
    ContDiffOn ℝ ∞ (chartAt (Model d) b ∘ f ∘ (chartAt (Model d) a).symm)
      (markingChartDomain M N f a b) := by
  intro y hy
  have hA : ContMDiffAt 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) ∞
      (chartAt (Model d) a).symm y :=
    (contMDiffOn_chart_symm (I := 𝓘(ℝ, Model d)) (x := a)).contMDiffAt
    ((chartAt (Model d) a).open_target.mem_nhds hy.1)
  have hB : ContMDiffAt 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) ∞
      (chartAt (Model d) b) (f ((chartAt (Model d) a).symm y)) :=
    (contMDiffOn_chart (I := 𝓘(ℝ, Model d)) (x := b)).contMDiffAt
    ((chartAt (Model d) b).open_source.mem_nhds hy.2)
  exact (hB.comp y (f.contMDiff.contMDiffAt.comp y hA)).contDiffAt.contDiffWithinAt

private theorem markingChart_mapsTo_inverse {d : ℕ} (M N : SmoothManifold d)
    (f : M.SmoothEquiv N) (a : M.Point) (b : N.Point) :
    MapsTo (chartAt (Model d) b ∘ f ∘ (chartAt (Model d) a).symm)
      (markingChartDomain M N f a b) (markingChartDomain N M f.symm b a) := by
  intro y hy
  have hb : f ((chartAt (Model d) a).symm y) ∈ (chartAt (Model d) b).source := hy.2
  refine ⟨(chartAt (Model d) b).map_source hy.2, ?_⟩
  change f.symm ((chartAt (Model d) b).symm
    ((chartAt (Model d) b) (f ((chartAt (Model d) a).symm y)))) ∈
      (chartAt (Model d) a).source
  rw [(chartAt (Model d) b).left_inv hb, f.symm_apply_apply]
  exact (chartAt (Model d) a).map_target hy.1

set_option backward.isDefEq.respectTransparency false in
private theorem smooth_marking_chart_family {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (M N : SmoothManifold d) (f : M.SmoothEquiv N) (a : M.Point) (b : N.Point)
    (A : ℝ × Model d → F) (hA : SmoothNearInterval (chartAt (Model d) b).target A)
    (p : ℝ × Model d) (ht : p.1 ∈ parameterInterval)
    (hy : p.2 ∈ markingChartDomain M N f a b) :
    let g := chartAt (Model d) b ∘ f ∘ (chartAt (Model d) a).symm
    let h := chartAt (Model d) a ∘ f.symm ∘ (chartAt (Model d) b).symm
    ∃ U : Set (ℝ × Model d), IsOpen U ∧ p ∈ U ∧
      (∀ q ∈ U, q.2 ∈ markingChartDomain M N f a b) ∧
      ContDiffOn ℝ ∞ (fun q => A (q.1, g q.2)) U ∧
      ContDiffOn ℝ ∞ (fun q => fderiv ℝ g q.2) U ∧
      ContDiffOn ℝ ∞ (fun q => fderiv ℝ h (g q.2)) U := by
  dsimp only
  let D := markingChartDomain M N f a b
  let D' := markingChartDomain N M f.symm b a
  let g := chartAt (Model d) b ∘ f ∘ (chartAt (Model d) a).symm
  let h := chartAt (Model d) a ∘ f.symm ∘ (chartAt (Model d) b).symm
  let Q : Set (ℝ × Model d) := univ ×ˢ D
  let R : ℝ × Model d → ℝ × Model d := fun q => (q.1, g q.2)
  have hD : IsOpen D := isOpen_markingChartDomain M N f a b
  have hD' : IsOpen D' := isOpen_markingChartDomain N M f.symm b a
  have hQ : IsOpen Q := isOpen_univ.prod hD
  have hg : ContDiffOn ℝ ∞ g D := contDiffOn_markingChart M N f a b
  have hh : ContDiffOn ℝ ∞ h D' := contDiffOn_markingChart N M f.symm b a
  have hmap : MapsTo g D D' := markingChart_mapsTo_inverse M N f a b
  have hsnd : MapsTo (Prod.snd : ℝ × Model d → Model d) Q D := fun _ hq => hq.2
  have hR : ContDiffOn ℝ ∞ R Q :=
    contDiff_fst.contDiffOn.prodMk (hg.comp contDiff_snd.contDiffOn hsnd)
  rcases hA with ⟨V, hV, hsub, hAV⟩
  let U := Q ∩ R ⁻¹' V
  have hU : IsOpen U := hR.continuousOn.isOpen_inter_preimage hQ hV
  refine ⟨U, hU, ⟨⟨mem_univ _, hy⟩, hsub ⟨ht,
    (chartAt (Model d) b).map_source hy.2⟩⟩, ?_, ?_, ?_, ?_⟩
  · exact fun _ hq => hq.1.2
  · exact hAV.comp (hR.mono inter_subset_left) (fun _ hq => hq.2)
  · exact ((hg.fderiv_of_isOpen hD (by simp)).comp
      contDiff_snd.contDiffOn hsnd).mono inter_subset_left
  · exact (((hh.fderiv_of_isOpen hD' (by simp)).comp hg hmap).comp
      contDiff_snd.contDiffOn hsnd).mono inter_subset_left

private theorem contDiffAt_squaredTensor_comp_family {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
    (a : E → SquaredCanonicalTensor n)
    (B : E → Model (2 * n) →L[ℝ] Model (2 * n)) (z : E)
    (ha : ContDiffAt ℝ ∞ a z) (hB : ContDiffAt ℝ ∞ B z) :
    ContDiffAt ℝ ∞ (fun y => (a y).compContinuousLinearMap (fun _ => B y)) z := by
  let C := ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℝ
    (fun _ : Fin n ⊕ Fin n => Model (2 * n))
    (fun _ : Fin n ⊕ Fin n => Model (2 * n)) ℂ
  have hC : ContDiff ℝ ∞ (fun L => C L) :=
    ContinuousMultilinearMap.contDiff (𝕜 := ℝ)
      (F := SquaredCanonicalTensor n →L[ℝ] SquaredCanonicalTensor n) C
  exact (hC.contDiffAt.comp z (contDiffAt_pi.mpr (fun _ => hB))).clm_apply ha

/-- Pullback preserves the actual joint smooth extension of squared sections.
Spatial chart overlaps and target parameter neighborhoods furnish the open
source neighborhood; no uniform collar is assumed. -/
theorem smoothNearInterval_squaredTensor_pullback {n : ℕ}
    (M N : SmoothManifold (2 * n)) (f : M.SmoothEquiv N)
    (s : ℝ → N.Point → SquaredCanonicalTensor n)
    (hs : ∀ b, SmoothNearInterval (chartAt (Model (2 * n)) b).target
      (fun p => squaredTensorInChart N b (s p.1) p.2))
    (a : M.Point) : SmoothNearInterval (chartAt (Model (2 * n)) a).target
      (fun p => squaredTensorInChart M a (pullbackSquaredTensor M N f (s p.1)) p.2) := by
  apply SmoothNearInterval.of_local
  intro p hp
  let b := f ((chartAt (Model (2 * n)) a).symm p.2)
  have hb : p.2 ∈ markingChartDomain M N f a b := ⟨hp.2, mem_chart_source _ _⟩
  rcases smooth_marking_chart_family M N f a b _ (hs b) p hp.1 hb with
    ⟨U, hU, hpU, hdomain, hcoeff, hforward, _⟩
  refine ⟨U, hU, hpU, ?_⟩
  intro q hq
  have hc := hcoeff.contDiffAt (hU.mem_nhds hq)
  have hD := hforward.contDiffAt (hU.mem_nhds hq)
  have hsm := contDiffAt_squaredTensor_comp_family _ _ q hc hD
  have heq : (fun p => squaredTensorInChart M a
      (pullbackSquaredTensor M N f (s p.1)) p.2) =ᶠ[𝓝 q]
      (fun p => (squaredTensorInChart N b (s p.1)
        ((chartAt (Model (2 * n)) b ∘ f ∘ (chartAt (Model (2 * n)) a).symm) p.2)).compContinuousLinearMap
          (fun _ => fderiv ℝ
            (chartAt (Model (2 * n)) b ∘ f ∘ (chartAt (Model (2 * n)) a).symm) p.2)) := by
    filter_upwards [hU.mem_nhds hq] with p hp
    exact squaredTensorInChart_pullback M N f (s p.1) a b p.2
      (hdomain p hp).1 (hdomain p hp).2
  exact (hsm.congr_of_eventuallyEq heq).contDiffWithinAt

/-- Conjugation by the actual forward and inverse chart derivatives
preserves joint smoothness of an almost complex family. -/
theorem smoothNearInterval_almostComplex_pullback {n : ℕ}
    (M N : SmoothManifold (2 * n)) (f : M.SmoothEquiv N)
    (J : ℝ → AlmostComplexField N)
    (hJ : ∀ b, SmoothNearInterval (chartAt (Model (2 * n)) b).target
      (fun p => almostComplexInChart N b (J p.1) p.2))
    (a : M.Point) : SmoothNearInterval (chartAt (Model (2 * n)) a).target
      (fun p => almostComplexInChart M a (pullbackAlmostComplex M N f (J p.1)) p.2) := by
  apply SmoothNearInterval.of_local
  intro p hp
  let b := f ((chartAt (Model (2 * n)) a).symm p.2)
  have hb : p.2 ∈ markingChartDomain M N f a b := ⟨hp.2, mem_chart_source _ _⟩
  rcases smooth_marking_chart_family M N f a b _ (hJ b) p hp.1 hb with
    ⟨U, hU, hpU, hdomain, hcoeff, hforward, hbackward⟩
  refine ⟨U, hU, hpU, ?_⟩
  intro q hq
  have hsm := (hbackward.contDiffAt (hU.mem_nhds hq)).clm_comp
    ((hcoeff.contDiffAt (hU.mem_nhds hq)).clm_comp
      (hforward.contDiffAt (hU.mem_nhds hq)))
  have heq : (fun p => almostComplexInChart M a
      (pullbackAlmostComplex M N f (J p.1)) p.2) =ᶠ[𝓝 q]
      (fun p => (fderiv ℝ (chartAt (Model (2 * n)) a ∘ f.symm ∘
          (chartAt (Model (2 * n)) b).symm)
          ((chartAt (Model (2 * n)) b ∘ f ∘ (chartAt (Model (2 * n)) a).symm) p.2)).comp
        ((almostComplexInChart N b (J p.1)
          ((chartAt (Model (2 * n)) b ∘ f ∘ (chartAt (Model (2 * n)) a).symm) p.2)).comp
            (fderiv ℝ (chartAt (Model (2 * n)) b ∘ f ∘
              (chartAt (Model (2 * n)) a).symm) p.2))) := by
    filter_upwards [hU.mem_nhds hq] with p hp
    exact almostComplexInChart_pullback M N f (J p.1) a b p.2
      (hdomain p hp).1 (hdomain p hp).2
  exact (hsm.congr_of_eventuallyEq heq).contDiffWithinAt

/-- Pull back an entire compatible family with its actual smooth extension. -/
def MaslovFamily.pullback {n : ℕ} {M N : SmoothManifold (2 * n)}
    {eta : ℝ → N.Form 2} (h : MaslovFamily N eta) (f : M.SmoothEquiv N) :
    MaslovFamily M (fun t => M.pullback N f (eta t)) where
  J := fun t => pullbackAlmostComplex M N f (h.J t)
  tensor := fun t => pullbackSquaredTensor M N f (h.tensor t)
  compatible := fun t ht => isCompatibleAlmostComplex_pullback M N f (eta t)
    (h.J t) (h.compatible t ht)
  canonical := fun t ht => pullbackSquaredTensor_canonical M N f
    (h.J t) (h.tensor t) (h.canonical t ht)
  nowhereZero := fun t ht => pullbackSquaredTensor_ne_zero M N f
    (h.tensor t) (h.nowhereZero t ht)
  smoothJ := smoothNearInterval_almostComplex_pullback M N f h.J h.smoothJ
  smoothSection := smoothNearInterval_squaredTensor_pullback M N f h.tensor h.smoothSection

/-- The pulled-back representative only changes its form index using a
proved equality of actual two-forms. Its field and tensor stay literal. -/
def MaslovRepresentative.pullbackTo {n : ℕ} {M N : SmoothManifold (2 * n)}
    {eta : M.Form 2} {eta' : N.Form 2} (s : MaslovRepresentative N eta')
    (f : M.SmoothEquiv N) (heta : M.pullback N f eta' = eta) :
    MaslovRepresentative M eta :=
  { s.pullback f with compatible := by rw [← heta]; exact (s.pullback f).compatible }

/-- Pull back the actual homotopy, including joint smoothness on an open
neighborhood of all required times and points. -/
def MaslovHomotopy.pullback {n : ℕ} {M N : SmoothManifold (2 * n)}
    {eta : M.Form 2} {eta' : N.Form 2} {s₀ s₁ : MaslovRepresentative N eta'}
    (h : MaslovHomotopy s₀ s₁) (f : M.SmoothEquiv N)
    (heta : M.pullback N f eta' = eta) :
    MaslovHomotopy (s₀.pullbackTo f heta) (s₁.pullbackTo f heta) where
  family :=
    { h.family.pullback f with
      compatible := fun t ht => by
        rw [← heta]
        exact (h.family.pullback f).compatible t ht }
  sourceJ := by change pullbackAlmostComplex M N f (h.family.J 0) = _; rw [h.sourceJ]; rfl
  targetJ := by change pullbackAlmostComplex M N f (h.family.J 1) = _; rw [h.targetJ]; rfl
  sourceSection := by change pullbackSquaredTensor M N f (h.family.tensor 0) = _
                      rw [h.sourceSection]; rfl
  targetSection := by change pullbackSquaredTensor M N f (h.family.tensor 1) = _
                      rw [h.targetSection]; rfl

theorem MaslovHomotopic.pullback {n : ℕ} {M N : SmoothManifold (2 * n)}
    {eta : M.Form 2} {eta' : N.Form 2} {s₀ s₁ : MaslovRepresentative N eta'}
    (h : MaslovHomotopic s₀ s₁) (f : M.SmoothEquiv N)
    (heta : M.pullback N f eta' = eta) :
    MaslovHomotopic (s₀.pullbackTo f heta) (s₁.pullbackTo f heta) :=
  h.map (fun h => h.pullback f heta)

/-- Contravariant pullback of the existing smooth-homotopy quotient. The
two-form equality determines the source form index and is proved from
primitive preservation for strict completion identifications below. -/
def MaslovClass.pullback {n : ℕ} {M N : SmoothManifold (2 * n)}
    {eta : M.Form 2} {eta' : N.Form 2} (f : M.SmoothEquiv N)
    (heta : M.pullback N f eta' = eta) : MaslovClass N eta' → MaslovClass M eta :=
  Quot.map (fun s => s.pullbackTo f heta) (fun {_ _} h => MaslovHomotopic.pullback h f heta)

@[simp] theorem MaslovClass.pullback_mk {n : ℕ} {M N : SmoothManifold (2 * n)}
    {eta : M.Form 2} {eta' : N.Form 2} (f : M.SmoothEquiv N)
    (heta : M.pullback N f eta' = eta) (s : MaslovRepresentative N eta') :
    MaslovClass.pullback f heta (Quot.mk _ s) = Quot.mk _ (s.pullbackTo f heta) := rfl

@[ext] theorem MaslovRepresentative.ext {n : ℕ} {M : SmoothManifold (2 * n)}
    {eta : M.Form 2} {s t : MaslovRepresentative M eta}
    (hJ : s.J = t.J) (ht : s.tensor = t.tensor) : s = t := by
  cases s
  cases t
  cases hJ
  cases ht
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem pullbackAlmostComplex_refl {n : ℕ} (M : SmoothManifold (2 * n))
    (J : AlmostComplexField M) :
    pullbackAlmostComplex M M (Diffeomorph.refl 𝓘(ℝ, Model (2 * n)) M.Point ∞) J = J := by
  funext x
  change (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) id x).comp
    ((J x).comp (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) id x)) = J x
  simp only [mfderiv_id, ContinuousLinearMap.comp_id, ContinuousLinearMap.id_comp]

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem pullbackSquaredTensor_refl {n : ℕ} (M : SmoothManifold (2 * n))
    (s : M.Point → SquaredCanonicalTensor n) :
    pullbackSquaredTensor M M (Diffeomorph.refl 𝓘(ℝ, Model (2 * n)) M.Point ∞) s = s := by
  funext x
  ext v
  change s x (fun i => mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) id x (v i)) = s x v
  simp only [mfderiv_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The derivative chain rule gives contravariance of the actual complex
structures, using injectivity of the composite marking derivative. -/
theorem pullbackAlmostComplex_trans {n : ℕ} (M N P : SmoothManifold (2 * n))
    (f : M.SmoothEquiv N) (g : N.SmoothEquiv P) (J : AlmostComplexField P) :
    pullbackAlmostComplex M P (f.trans g) J =
      pullbackAlmostComplex M N f (pullbackAlmostComplex N P g J) := by
  funext x
  apply ContinuousLinearMap.ext
  intro v
  apply ((f.trans g).mfderivToContinuousLinearEquiv (by simp) x).injective
  change mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) (f.trans g) x
      (pullbackAlmostComplex M P (f.trans g) J x v) =
    mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) (f.trans g) x
      (pullbackAlmostComplex M N f (pullbackAlmostComplex N P g J) x v)
  rw [pullbackAlmostComplex_intertwines]
  have hd : mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) (f.trans g) x =
      (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) g (f x)).comp
        (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) f x) :=
    mfderiv_comp x (g.mdifferentiable (by simp) (f x)) (f.mdifferentiable (by simp) x)
  rw [hd]
  change J (g (f x)) (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) g (f x)
      (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) f x v)) =
    mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) g (f x)
      (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) f x
        (pullbackAlmostComplex M N f (pullbackAlmostComplex N P g J) x v))
  rw [pullbackAlmostComplex_intertwines, pullbackAlmostComplex_intertwines]

set_option backward.isDefEq.respectTransparency false in
theorem pullbackSquaredTensor_trans {n : ℕ} (M N P : SmoothManifold (2 * n))
    (f : M.SmoothEquiv N) (g : N.SmoothEquiv P) (s : P.Point → SquaredCanonicalTensor n) :
    pullbackSquaredTensor M P (f.trans g) s =
      pullbackSquaredTensor M N f (pullbackSquaredTensor N P g s) := by
  funext x
  ext v
  have hd := mfderiv_comp x (g.mdifferentiable (by simp) (f x))
    (f.mdifferentiable (by simp) x)
  change s (g (f x)) (fun i => mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n))
    (g ∘ f) x (v i)) = s (g (f x)) (fun i => mfderiv 𝓘(ℝ, Model (2 * n))
      𝓘(ℝ, Model (2 * n)) g (f x)
        (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) f x (v i)))
  rw [hd]
  rfl

@[simp] theorem MaslovRepresentative.pullbackTo_refl {n : ℕ}
    {M : SmoothManifold (2 * n)} {eta : M.Form 2} (s : MaslovRepresentative M eta)
    (h : M.pullback M (Diffeomorph.refl 𝓘(ℝ, Model (2 * n)) M.Point ∞) eta = eta) :
    s.pullbackTo (Diffeomorph.refl 𝓘(ℝ, Model (2 * n)) M.Point ∞) h = s := by
  apply MaslovRepresentative.ext
  · exact pullbackAlmostComplex_refl M s.J
  · exact pullbackSquaredTensor_refl M s.tensor

theorem MaslovRepresentative.pullbackTo_trans {n : ℕ} {M N P : SmoothManifold (2 * n)}
    {eta : M.Form 2} {eta' : N.Form 2} {eta'' : P.Form 2}
    (s : MaslovRepresentative P eta'') (f : M.SmoothEquiv N) (g : N.SmoothEquiv P)
    (hf : M.pullback N f eta' = eta) (hg : N.pullback P g eta'' = eta')
    (hfg : M.pullback P (f.trans g) eta'' = eta) :
    s.pullbackTo (f.trans g) hfg = (s.pullbackTo g hg).pullbackTo f hf := by
  apply MaslovRepresentative.ext
  · exact pullbackAlmostComplex_trans M N P f g s.J
  · exact pullbackSquaredTensor_trans M N P f g s.tensor

@[simp] theorem MaslovClass.pullback_refl {n : ℕ} {M : SmoothManifold (2 * n)}
    {eta : M.Form 2} (c : MaslovClass M eta)
    (h : M.pullback M (Diffeomorph.refl 𝓘(ℝ, Model (2 * n)) M.Point ∞) eta = eta) :
    MaslovClass.pullback (Diffeomorph.refl 𝓘(ℝ, Model (2 * n)) M.Point ∞) h c = c := by
  induction c using Quot.inductionOn with
  | h s => rw [MaslovClass.pullback_mk, s.pullbackTo_refl h]

/-- Contravariance on homotopy classes, with the source two-form determined
by the same actual composition of markings. -/
theorem MaslovClass.pullback_trans {n : ℕ} {M N P : SmoothManifold (2 * n)}
    {eta : M.Form 2} {eta' : N.Form 2} {eta'' : P.Form 2}
    (f : M.SmoothEquiv N) (g : N.SmoothEquiv P)
    (hf : M.pullback N f eta' = eta) (hg : N.pullback P g eta'' = eta')
    (hfg : M.pullback P (f.trans g) eta'' = eta) (c : MaslovClass P eta'') :
    MaslovClass.pullback (f.trans g) hfg c =
      MaslovClass.pullback f hf (MaslovClass.pullback g hg c) := by
  induction c using Quot.inductionOn with
  | h s => rw [MaslovClass.pullback_mk, MaslovClass.pullback_mk,
      MaslovClass.pullback_mk, s.pullbackTo_trans f g hf hg hfg]

/-- A marking gives an equivalence of the concrete homotopy classes, with
inverse induced by the actual inverse marking. -/
def MaslovClass.pullbackEquiv {n : ℕ} {M N : SmoothManifold (2 * n)}
    {eta : M.Form 2} {eta' : N.Form 2} (f : M.SmoothEquiv N)
    (hf : M.pullback N f eta' = eta) : MaslovClass N eta' ≃ MaslovClass M eta := by
  have hi : N.pullback M f.symm eta = eta' := by
    rw [← hf]
    exact M.pullback_symm_pullback N f eta'
  refine
    { toFun := MaslovClass.pullback f hf
      invFun := MaslovClass.pullback f.symm hi
      left_inv := ?_
      right_inv := ?_ }
  · intro c
    have he : f.symm.trans f = Diffeomorph.refl 𝓘(ℝ, Model (2 * n)) N.Point ∞ :=
      Diffeomorph.ext (fun x => f.apply_symm_apply x)
    have hc : N.pullback N (f.symm.trans f) eta' = eta' := by
      rw [he]
      exact N.pullback_id eta'
    rw [← MaslovClass.pullback_trans f.symm f hi hf hc c]
    simp only [he, MaslovClass.pullback_refl]
  · intro c
    have he : f.trans f.symm = Diffeomorph.refl 𝓘(ℝ, Model (2 * n)) M.Point ∞ :=
      Diffeomorph.ext (fun x => f.symm_apply_apply x)
    have hc : M.pullback M (f.trans f.symm) eta = eta := by
      rw [he]
      exact M.pullback_id eta
    rw [← MaslovClass.pullback_trans f f.symm hf hi hc c]
    simp only [he, MaslovClass.pullback_refl]

set_option backward.isDefEq.respectTransparency false in
/-- Primitive preservation supplies the symplectic-form equality needed
by class pullback, using the already proved exterior-derivative naturality. -/
theorem CompletionIdentification.pullback_symplecticForm {n : ℕ}
    {P Q : WitnessedPair n} (h : CompletionIdentification P Q) :
    P.ambientManifold.pullback Q.ambientManifold h.ambientEquiv Q.ambientSymplecticForm =
      P.ambientSymplecticForm := by
  change P.ambientManifold.pullback Q.ambientManifold h.ambientEquiv
    (Q.ambientManifold.exteriorDerivative Q.ambientCompletion.ambient.primitive) =
      P.ambientManifold.exteriorDerivative P.ambientCompletion.ambient.primitive
  have hd := P.ambientManifold.exteriorDerivative_pullback Q.ambientManifold
    h.ambientEquiv.toContMDiffMap Q.ambientCompletion.ambient.primitive
      Q.ambientCompletion.ambient.smooth_primitive
  exact hd.symm.trans (congrArg P.ambientManifold.exteriorDerivative h.primitive)

/-- Strict completion identifications act on the ambient classes by their
specified geometric diffeomorphism. -/
def CompletionIdentification.pullbackMaslovClass {n : ℕ} {P Q : WitnessedPair n}
    (h : CompletionIdentification P Q) :
    MaslovClass Q.ambientManifold Q.ambientSymplecticForm →
      MaslovClass P.ambientManifold P.ambientSymplecticForm :=
  MaslovClass.pullback h.ambientEquiv h.pullback_symplecticForm

/-- The literal family in a graded completion step is a homotopy to the
actual pulled-back target representative. -/
def MaslovCompletionLift.toHomotopy {n : ℕ} {M N : SmoothManifold (2 * n)}
    {eta : M.Form 2} {eta' : N.Form 2} {f : M.SmoothEquiv N}
    {source : MaslovRepresentative M eta} {target : MaslovRepresentative N eta'}
    (lift : MaslovCompletionLift M N eta eta' f source target)
    (heta : M.pullback N f eta' = eta) :
    MaslovHomotopy source (target.pullbackTo f heta) where
  family := lift.family
  sourceJ := lift.sourceJ
  targetJ := lift.targetJ
  sourceSection := lift.sourceSection
  targetSection := lift.targetSection

/-- A graded lift witnesses exactly equality with the class transported
by the same strict completion identification. Conversely, class equality
produces one concrete smooth homotopy and hence a graded lift. -/
theorem CompletionIdentification.gradedLift_iff_class_eq {n : ℕ} {P Q : WitnessedPair n}
    (h : CompletionIdentification P Q) (source : P.Maslov) (target : Q.Maslov) :
    Nonempty (GradedCompletionIdentification h source target) ↔
      (Quot.mk _ source : MaslovClass P.ambientManifold P.ambientSymplecticForm) =
        h.pullbackMaslovClass (Quot.mk _ target) := by
  change Nonempty (GradedCompletionIdentification h source target) ↔
    (Quot.mk _ source : MaslovClass P.ambientManifold P.ambientSymplecticForm) =
      Quot.mk _ (target.pullbackTo h.ambientEquiv h.pullback_symplecticForm)
  rw [MaslovClass.eq_iff_homotopic]
  constructor
  · rintro ⟨lift⟩
    exact ⟨lift.toHomotopy h.pullback_symplecticForm⟩
  · rintro ⟨homotopy⟩
    exact ⟨{
      family := homotopy.family
      sourceJ := homotopy.sourceJ
      targetJ := homotopy.targetJ
      sourceSection := homotopy.sourceSection
      targetSection := homotopy.targetSection }⟩

end FsFltz.Geometry
