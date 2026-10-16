import FsFltz.Geometry.IntrinsicCollarDefining
import FsFltz.Geometry.IntrinsicCollarGluingDifferential
import FsFltz.Geometry.IntrinsicGluingPrimitive

/-!
# A primitive on the actual boundaryless collar quotient

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 119–160, and `sec:lean`,
lines 783–814. The form is pushed through actual patch differentials of
the constructed mixed atlas. The same native collar proves compatibility.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology

namespace FsFltz.Geometry.IntrinsicCollarGluing

private theorem contDiffAt_oneForm_comp {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (a : G → F [⋀^Fin 1]→L[ℝ] ℝ) (B : G → E →L[ℝ] F) (z : G)
    (ha : ContDiffAt ℝ ∞ a z) (hB : ContDiffAt ℝ ∞ B z) :
    ContDiffAt ℝ ∞ (fun y => (a y).compContinuousLinearMap (B y)) z := by
  let eF := (ContinuousAlternatingMap.ofSubsingletonLIE
    (𝕜 := ℝ) (E := F) (F := ℝ) (0 : Fin 1)).toContinuousLinearEquiv
  let eE := (ContinuousAlternatingMap.ofSubsingletonLIE
    (𝕜 := ℝ) (E := E) (F := ℝ) (0 : Fin 1)).toContinuousLinearEquiv
  have h := (eF.symm.contDiff.contDiffAt.comp z ha).clm_comp hB
  have hs := eE.contDiff.contDiffAt.comp z h
  convert hs using 1
  ext y vs
  change a y (fun i => B y (vs i)) = a y (fun _ => B y (vs 0))
  congr 1
  funext i
  rw [Fin.eq_zero i]

/-- The local version of one-form pullback smoothness needed for inverse
germs of the actual open patch maps. -/
private theorem contDiffAt_formInChart_pullback {d e : ℕ}
    (X : SmoothManifold d) (N : SmoothManifold e) (g : X.Point → N.Point)
    (β : N.Form 1) (hβ : N.IsSmoothForm β) (a : X.Point) (y : Model d)
    (hy : y ∈ (chartAt (Model d) a).target)
    (hg : ContMDiffAt 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) ∞ g
      ((chartAt (Model d) a).symm y)) :
    ContDiffAt ℝ ∞ (X.formInChart a (X.pullback N g β)) y := by
  let c := chartAt (Model d) a
  let x := c.symm y
  let b := chartAt (Model e) (g x)
  let f := b ∘ g ∘ c.symm
  have hx : g x ∈ b.source := mem_chart_source _ _
  have hA : ContMDiffAt 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) ∞ c.symm y :=
    (contMDiffOn_chart_symm (I := 𝓘(ℝ, Model d)) (x := a)).contMDiffAt
      (c.open_target.mem_nhds hy)
  have hB : ContMDiffAt 𝓘(ℝ, Model e) 𝓘(ℝ, Model e) ∞ b (g x) :=
    (contMDiffOn_chart (I := 𝓘(ℝ, Model e)) (x := g x)).contMDiffAt
      (b.open_source.mem_nhds hx)
  have hf : ContDiffAt ℝ ∞ f y := (hB.comp y (hg.comp y hA)).contDiffAt
  have hcoeff : ContDiffAt ℝ ∞ (N.formInChart (g x) β) (f y) :=
    (hβ (g x)).contDiffAt (b.open_target.mem_nhds (b.map_source hx))
  have hs := contDiffAt_oneForm_comp (fun z => N.formInChart (g x) β (f z))
    (fderiv ℝ f) y (hcoeff.comp y hf) (hf.fderiv_right (by simp))
  have hnb : ∀ᶠ z in 𝓝 y, g (c.symm z) ∈ b.source :=
    (hg.continuousAt.comp (c.continuousAt_symm hy)).preimage_mem_nhds
      (b.open_source.mem_nhds hx)
  have hgd : ∀ᶠ z in 𝓝 x, MDifferentiableAt 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) g z := by
    have hn := (contMDiffAt_iff_contMDiffAt_nhds (n := 1) (by simp)).mp
      (hg.of_le (by simp))
    exact hn.mono (fun z hz => hz.mdifferentiableAt (by simp))
  apply hs.congr_of_eventuallyEq
  filter_upwards [c.open_target.mem_nhds hy, hnb,
    (c.continuousAt_symm hy).eventually hgd] with z hz hzb hzg
  exact X.formInChart_pullback N β a (g x) z hz hzb hzg

private theorem contDiffAt_formInChart_of_inverse {d : ℕ}
    (X N : SmoothManifold d) (γ : X.Form 1) (β : N.Form 1)
    (hβ : N.IsSmoothForm β) (i : N.Point → X.Point)
    (hi : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) ∞ i)
    (hrestrict : N.pullback X i γ = β) (a : X.Point) (y : Model d)
    (hy : y ∈ (chartAt (Model d) a).target) (g : X.Point → N.Point)
    (hg : ContMDiffAt 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) ∞ g
      ((chartAt (Model d) a).symm y))
    (heq : i ∘ g =ᶠ[𝓝 ((chartAt (Model d) a).symm y)] id) :
    ContDiffAt ℝ ∞ (X.formInChart a γ) y := by
  let c := chartAt (Model d) a
  let x := c.symm y
  have hgd : ∀ᶠ z in 𝓝 x, MDifferentiableAt 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) g z := by
    have hn := (contMDiffAt_iff_contMDiffAt_nhds (n := 1) (by simp)).mp
      (hg.of_le (by simp))
    exact hn.mono (fun z hz => hz.mdifferentiableAt (by simp))
  have hform : ∀ᶠ z in 𝓝 x, γ z = X.pullback N g β z := by
    filter_upwards [hgd, eventually_mem_nhds_iff.mpr heq] with z hgz hzn
    have hzi : z ∈ {q | i (g q) = q} := mem_of_mem_nhds hzn
    have heqz : i ∘ g =ᶠ[𝓝 z] id := hzn
    have hid := heqz.mfderiv_eq (I := 𝓘(ℝ, Model d)) (I' := 𝓘(ℝ, Model d))
    have hchain := mfderiv_comp z (hi.mdifferentiableAt (by simp)) hgz
    have hd : (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) i (g z)).comp
        (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) g z) = ContinuousLinearMap.id ℝ _ := by
      rw [← hchain]
      exact hid.trans (by rw [mfderiv_id]; rfl)
    have hr := congrFun hrestrict (g z)
    ext vs
    unfold SmoothManifold.pullback at hr ⊢
    rw [← hr]
    change γ z vs = γ (i (g z)) (fun n =>
      ((mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) i (g z)).comp
        (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) g z)) (vs n))
    rw [hd, hzi]
    rfl
  have hc : X.formInChart a γ =ᶠ[𝓝 y] X.formInChart a (X.pullback N g β) := by
    filter_upwards [(c.continuousAt_symm hy).eventually hform] with z hz
    exact congrArg (fun A => A.compContinuousLinearMap
      (X.inverseChartTangentMap a z)) hz
  exact (contDiffAt_formInChart_pullback X N g β hβ a y hy hg).congr_of_eventuallyEq hc

variable {k : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M] [T2Space M] [SecondCountableTopology M]
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

local instance gluedBandChartedSpace :
    ChartedSpace (Model (k + 1)) (Band δ (IntrinsicBoundary.Point k M)) := bandChartedSpace δ

local instance gluedBandIsManifold :
    IsManifold 𝓘(ℝ, Model (k + 1)) ∞ (Band δ (IntrinsicBoundary.Point k M)) := band_isManifold δ

private def interiorTangentEquiv (x : IntrinsicInterior.Point k M) :
    Model (k + 1) ≃L[ℝ] Model (k + 1) := by
  let := extensionChartedSpace hδ C hemb hboundary hzero
  exact (LinearEquiv.ofBijective
    (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1))
      (interiorIn (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val)) x).toLinearMap
    (bijective_mfderiv_interiorIn hδ C hemb hC hboundary hinv hzero x)).toContinuousLinearEquiv

private def cylinderTangentEquiv (p : Band δ (IntrinsicBoundary.Point k M)) :
    Model (k + 1) ≃L[ℝ] Model (k + 1) := by
  let := extensionChartedSpace hδ C hemb hboundary hzero
  exact (LinearEquiv.ofBijective
    (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1))
      (cylinder (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val)) p).toLinearMap
    (bijective_mfderiv_cylinder hδ C hemb hC hboundary hinv hzero p)).toContinuousLinearEquiv

private def pushInteriorPrimitive (α : IntrinsicLiouville.Form k M 1)
    (x : IntrinsicInterior.Point k M) : Model (k + 1) [⋀^Fin 1]→L[ℝ] ℝ :=
  (interiorPrimitive α x).compContinuousLinearMap
    (interiorTangentEquiv hδ C hemb hC hboundary hinv hzero x).symm.toContinuousLinearMap

private def pushCylinderPrimitive (α : IntrinsicLiouville.Form k M 1)
    (p : Band δ (IntrinsicBoundary.Point k M)) : Model (k + 1) [⋀^Fin 1]→L[ℝ] ℝ :=
  (cylinderPrimitive δ α p).compContinuousLinearMap
    (cylinderTangentEquiv hδ C hemb hC hboundary hinv hzero p).symm.toContinuousLinearMap

/-- A single actual one-form on the constructed boundaryless extension. Its
coefficients are transported by the inverses of the actual patch derivatives. -/
def gluedPrimitive (α : IntrinsicLiouville.Form k M 1) :
    (extensionManifold hδ C hemb hC hboundary hinv hzero).Form 1 := by
  classical
  let C₀ := fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val
  exact fun z => if hz : ∃ x, interiorIn C₀ x = z then
    pushInteriorPrimitive hδ C hemb hC hboundary hinv hzero α hz.choose
  else
    pushCylinderPrimitive hδ C hemb hC hboundary hinv hzero α
      ((native_open_cover hδ C hzero z).resolve_left hz).choose

private theorem gluedPrimitive_interior (α : IntrinsicLiouville.Form k M 1)
    (x : IntrinsicInterior.Point k M) :
    gluedPrimitive hδ C hemb hC hboundary hinv hzero α
      (interiorIn (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) x) =
        pushInteriorPrimitive hδ C hemb hC hboundary hinv hzero α x := by
  classical
  have hz : ∃ u, interiorIn (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) u =
      interiorIn (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) x := ⟨x, rfl⟩
  have he : hz.choose = x :=
    (isOpenEmbedding_interiorIn hδ _ hemb hboundary).injective hz.choose_spec
  simp only [gluedPrimitive, dite_eq_left hz, he]

/-- Exact preservation of the proved interior primitive. -/
theorem pullback_gluedPrimitive_interior (α : IntrinsicLiouville.Form k M 1) :
    (IntrinsicInterior.smoothManifold k M).pullback
      (extensionManifold hδ C hemb hC hboundary hinv hzero)
      (interiorIn (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val))
      (gluedPrimitive hδ C hemb hC hboundary hinv hzero α) = interiorPrimitive α := by
  funext x
  unfold SmoothManifold.pullback
  rw [gluedPrimitive_interior]
  ext vs
  change interiorPrimitive α x (fun i =>
    (interiorTangentEquiv hδ C hemb hC hboundary hinv hzero x).symm
      ((interiorTangentEquiv hδ C hemb hC hboundary hinv hzero x) (vs i))) = _
  simp only [ContinuousLinearEquiv.symm_apply_apply]

private theorem pushInteriorPrimitive_eq_pushCylinderPrimitive
    (α : IntrinsicLiouville.Form k M 1)
    (hα : IntrinsicLiouville.IsLocallyExtendibleForm α)
    (Z : (x : M) → TangentSpace (𝓡∂ (k + 1)) x)
    (hZ : IntrinsicLiouville.Contraction α (IntrinsicLiouville.exteriorDerivative α) Z)
    (hode : ∀ y, IsMIntegralCurveOn (fun t => C (t, y)) (fun x => -Z x) (Ico 0 δ))
    (x : IntrinsicInterior.Point k M) (p : Band δ (IntrinsicBoundary.Point k M))
    (hxp : interiorIn (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) x =
      cylinder (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) p) :
    pushInteriorPrimitive hδ C hemb hC hboundary hinv hzero α x =
      pushCylinderPrimitive hδ C hemb hC hboundary hinv hzero α p := by
  let := extensionChartedSpace hδ C hemb hboundary hzero
  let := extension_isManifold hδ C hemb hC hboundary hinv hzero
  let C₀ := fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val
  let i := interiorIn C₀
  let j := cylinder C₀
  obtain ⟨hp, hCp⟩ := (interiorIn_eq_cylinder_iff C₀ hboundary x p).mp hxp
  obtain ⟨g, hg, hgp, heq⟩ := cylinder_interior_germ C hC hboundary p x hxp.symm
  have hvaleq : (Subtype.val ∘ g) =ᶠ[𝓝 p] C ∘ Subtype.val := by
    filter_upwards [heq] with q hq
    obtain ⟨_, hCq⟩ := (interiorIn_eq_cylinder_iff C₀ hboundary (g q) q).mp hq.symm
    exact hCq.symm
  have hchain := mfderiv_comp p
    (IntrinsicInterior.contMDiff_val.mdifferentiableAt (by simp))
    (hg.mdifferentiableAt (by simp))
  have hvalder := (hvaleq.mfderiv_eq
    (I := 𝓘(ℝ, Model (k + 1))) (I' := 𝓡∂ (k + 1))).trans (by rfl)
  rw [hgp] at hchain
  have hcompat : (interiorPrimitive α x).compContinuousLinearMap
      (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) g p) =
        cylinderPrimitive δ α p := by
    rw [← pullbackForm_collar_eq_cylinderPrimitive α hα Z hZ C hδ hC hode hzero p hp]
    ext vs
    unfold interiorPrimitive IntrinsicLiouville.pullbackForm
    change α x.val (fun n => mfderiv 𝓘(ℝ, Model (k + 1)) (𝓡∂ (k + 1))
      Subtype.val x (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) g p (vs n))) = _
    rw [← hCp]
    change α (C p.val) (fun n =>
      ((mfderiv 𝓘(ℝ, Model (k + 1)) (𝓡∂ (k + 1)) Subtype.val x).comp
        (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) g p)) (vs n)) = _
    rw [← hchain, hvalder]
    rfl
  have hd := mfderiv_comp p
    ((contMDiff_interiorIn hδ C hemb hC hboundary hinv hzero).mdifferentiableAt (by simp))
    (hg.mdifferentiableAt (by simp))
  have heq' : j =ᶠ[𝓝 p] i ∘ g := heq
  have heqd := (heq'.symm.mfderiv_eq
    (I := 𝓘(ℝ, Model (k + 1))) (I' := 𝓘(ℝ, Model (k + 1)))).trans (by rfl)
  change mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) (i ∘ g) p =
    mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) j p at heqd
  rw [hgp, heqd] at hd
  ext vs
  let e := cylinderTangentEquiv hδ C hemb hC hboundary hinv hzero p
  let ws := fun n => e.symm (vs n)
  have hv : vs = fun n => e (ws n) := by
    funext n
    exact (e.apply_symm_apply (vs n)).symm
  rw [hv]
  change interiorPrimitive α x (fun n =>
    (interiorTangentEquiv hδ C hemb hC hboundary hinv hzero x).symm
      (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) j p (ws n))) =
        cylinderPrimitive δ α p (fun n => e.symm (e (ws n)))
  rw [hd]
  change interiorPrimitive α x (fun n =>
    (interiorTangentEquiv hδ C hemb hC hboundary hinv hzero x).symm
      ((interiorTangentEquiv hδ C hemb hC hboundary hinv hzero x)
        (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) g p (ws n)))) = _
  simp only [ContinuousLinearEquiv.symm_apply_apply]
  exact congrArg (fun A => A ws) hcompat

private theorem gluedPrimitive_cylinder
    (α : IntrinsicLiouville.Form k M 1)
    (hα : IntrinsicLiouville.IsLocallyExtendibleForm α)
    (Z : (x : M) → TangentSpace (𝓡∂ (k + 1)) x)
    (hZ : IntrinsicLiouville.Contraction α (IntrinsicLiouville.exteriorDerivative α) Z)
    (hode : ∀ y, IsMIntegralCurveOn (fun t => C (t, y)) (fun x => -Z x) (Ico 0 δ))
    (p : Band δ (IntrinsicBoundary.Point k M)) :
    gluedPrimitive hδ C hemb hC hboundary hinv hzero α
      (cylinder (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) p) =
        pushCylinderPrimitive hδ C hemb hC hboundary hinv hzero α p := by
  classical
  by_cases hz : ∃ x,
      interiorIn (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) x =
        cylinder (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) p
  · simp only [gluedPrimitive, dite_eq_left hz]
    exact pushInteriorPrimitive_eq_pushCylinderPrimitive hδ C hemb hC hboundary hinv hzero
      α hα Z hZ hode hz.choose p hz.choose_spec
  · have he : ((native_open_cover hδ C hzero
        (cylinder (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) p)).resolve_left hz).choose = p :=
      (cylinder_injective (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) hemb.injective)
        ((native_open_cover hδ C hzero
          (cylinder (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) p)).resolve_left hz).choose_spec
    simp only [gluedPrimitive, dite_eq_right hz, he]

/-- Exact preservation of the prescribed exponential primitive on the entire
two-sided cylinder, with compatibility proved from the same collar's ODE. -/
theorem pullback_gluedPrimitive_cylinder
    (α : IntrinsicLiouville.Form k M 1)
    (hα : IntrinsicLiouville.IsLocallyExtendibleForm α)
    (Z : (x : M) → TangentSpace (𝓡∂ (k + 1)) x)
    (hZ : IntrinsicLiouville.Contraction α (IntrinsicLiouville.exteriorDerivative α) Z)
    (hode : ∀ y, IsMIntegralCurveOn (fun t => C (t, y)) (fun x => -Z x) (Ico 0 δ)) :
    (bandManifold δ (IntrinsicBoundary.smoothManifold k M)).pullback
      (extensionManifold hδ C hemb hC hboundary hinv hzero)
      (cylinder (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val))
      (gluedPrimitive hδ C hemb hC hboundary hinv hzero α) = cylinderPrimitive δ α := by
  funext p
  unfold SmoothManifold.pullback
  rw [gluedPrimitive_cylinder hδ C hemb hC hboundary hinv hzero α hα Z hZ hode]
  ext vs
  change cylinderPrimitive δ α p (fun i =>
    (cylinderTangentEquiv hδ C hemb hC hboundary hinv hzero p).symm
      ((cylinderTangentEquiv hδ C hemb hC hboundary hinv hzero p) (vs i))) = _
  simp only [ContinuousLinearEquiv.symm_apply_apply]

 /-- Smoothness of the single constructed primitive follows from exact patch
pullbacks and produced inverse germs of the actual open patch maps. -/
theorem isSmoothForm_gluedPrimitive
    (α : IntrinsicLiouville.Form k M 1)
    (hα : IntrinsicLiouville.IsLocallyExtendibleForm α)
    (Z : (x : M) → TangentSpace (𝓡∂ (k + 1)) x)
    (hZ : IntrinsicLiouville.Contraction α (IntrinsicLiouville.exteriorDerivative α) Z)
    (hode : ∀ y, IsMIntegralCurveOn (fun t => C (t, y)) (fun x => -Z x) (Ico 0 δ)) :
    (extensionManifold hδ C hemb hC hboundary hinv hzero).IsSmoothForm
      (gluedPrimitive hδ C hemb hC hboundary hinv hzero α) := by
  let X := extensionManifold hδ C hemb hC hboundary hinv hzero
  let C₀ := fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val
  let i := interiorIn C₀
  let j := cylinder C₀
  let := extensionChartedSpace hδ C hemb hboundary hzero
  let := extension_isManifold hδ C hemb hC hboundary hinv hzero
  intro a y hy
  let z := (chartAt (Model (k + 1)) a).symm y
  rcases native_open_cover hδ C hzero z with ⟨u, hu⟩ | ⟨p, hp⟩
  · have hi := isOpenEmbedding_interiorIn hδ C₀ hemb hboundary
    have hatlas : (chartAt (Model (k + 1)) u).lift_openEmbedding hi ∈
        IsManifold.maximalAtlas 𝓘(ℝ, Model (k + 1)) ∞ X.Point := by
      apply IsManifold.subset_maximalAtlas
      exact Or.inl ⟨chartAt (Model (k + 1)) u,
        chart_mem_atlas (Model (k + 1)) u, rfl⟩
    obtain ⟨g, hg, _, heq⟩ := smooth_inverse_germ_of_lifted_chart hi u hatlas
    rw [hu] at hg heq
    exact (contDiffAt_formInChart_of_inverse X (IntrinsicInterior.smoothManifold k M)
      (gluedPrimitive hδ C hemb hC hboundary hinv hzero α) (interiorPrimitive α)
      (isSmoothForm_interiorPrimitive α hα) i
      (contMDiff_interiorIn hδ C hemb hC hboundary hinv hzero)
      (pullback_gluedPrimitive_interior hδ C hemb hC hboundary hinv hzero α)
      a y hy g hg heq).contDiffWithinAt
  · obtain ⟨g, hg, _, heq⟩ := cylinder_inverse_germ hδ C hemb hC hboundary hinv hzero p
    rw [hp] at hg heq
    exact (contDiffAt_formInChart_of_inverse X
      (bandManifold δ (IntrinsicBoundary.smoothManifold k M))
      (gluedPrimitive hδ C hemb hC hboundary hinv hzero α) (cylinderPrimitive δ α)
      (isSmoothForm_cylinderPrimitive δ α hα) j
      (contMDiff_cylinder hδ C hemb hC hboundary hinv hzero)
      (pullback_gluedPrimitive_cylinder hδ C hemb hC hboundary hinv hzero α hα Z hZ hode)
      a y hy g hg heq).contDiffWithinAt

end FsFltz.Geometry.IntrinsicCollarGluing
