import FsFltz.Geometry.IntrinsicCompletionPatch
import FsFltz.Geometry.IntrinsicCollarGluingDifferential

/-!
# Smooth atlas on the actual half-infinite intrinsic completion

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 142–158, and `sec:lean`,
lines 783–814. The finite native extension is one open patch of the actual
half-infinite quotient. The other is the literal cylinder `t < δ`, with no
lower bound on inward time. Their overlap retains the original coordinates.
The smoothness and rank results below are derived from the native collar;
neither a quotient atlas nor a completed ambient is an input.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology

namespace FsFltz.Geometry.IntrinsicCompletionGluing

/-- The genuine half-infinite cylinder is an open subset of the product. -/
def bandOpen (δ : ℝ) (B : Type) [TopologicalSpace B] : TopologicalSpace.Opens (ℝ × B) :=
  ⟨Band δ B, isOpen_Iio.prod isOpen_univ⟩

section Cylinder

variable {k : ℕ} {B : Type} [TopologicalSpace B] [ChartedSpace (Model k) B]
  [IsManifold 𝓘(ℝ, Model k) ∞ B]

/-- Product charts on the full half-infinite cylinder. -/
@[instance_reducible]
def bandProductChartedSpace (δ : ℝ) : ChartedSpace (ℝ × Model k) (Band δ B) :=
  inferInstanceAs (ChartedSpace (ModelProd ℝ (Model k)) (bandOpen δ B))

theorem bandProduct_isManifold (δ : ℝ) :
    letI := bandProductChartedSpace (k := k) (B := B) δ
    IsManifold 𝓘(ℝ, ℝ × Model k) ∞ (Band δ B) := by
  let := bandProductChartedSpace (k := k) (B := B) δ
  rw [modelWithCornersSelf_prod]
  exact inferInstanceAs
    (IsManifold (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) ∞ (bandOpen δ B))

/-- The full cylinder is expressed in the ambient Euclidean model. -/
@[instance_reducible]
def bandChartedSpace (δ : ℝ) : ChartedSpace (Model (k + 1)) (Band δ B) := by
  letI := bandProductChartedSpace (k := k) (B := B) δ
  exact linearRechart (M := Band δ B) (IntrinsicCollarGluing.bandModelEquiv k)

theorem band_isManifold (δ : ℝ) :
    letI := bandChartedSpace (k := k) (B := B) δ
    IsManifold 𝓘(ℝ, Model (k + 1)) ∞ (Band δ B) := by
  let := bandProductChartedSpace (k := k) (B := B) δ
  let := bandProduct_isManifold (k := k) (B := B) δ
  exact linearRechart_isManifold (M := Band δ B) (IntrinsicCollarGluing.bandModelEquiv k)

/-- Smoothness of the actual product coordinates on the entire cylinder. -/
theorem contMDiff_band_val (δ : ℝ) :
    letI := bandChartedSpace (k := k) (B := B) δ
    ContMDiff 𝓘(ℝ, Model (k + 1)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) ∞
      (Subtype.val : Band δ B → ℝ × B) := by
  let := bandProductChartedSpace (k := k) (B := B) δ
  let := bandProduct_isManifold (k := k) (B := B) δ
  have hr := contMDiff_linearRechart_id_symm (M := Band δ B)
    (IntrinsicCollarGluing.bandModelEquiv k)
  have hv := contMDiff_subtype_val
    (I := 𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) (n := ∞) (U := bandOpen δ B)
  let := bandChartedSpace (k := k) (B := B) δ
  exact hv.comp hr

section SmoothMaps

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X]

/-- The full cylinder's smoothness is exactly that of its product coordinates. -/
theorem contMDiffAt_band_iff_val {δ : ℝ} {f : X → Band δ B} {x : X} :
    letI := bandChartedSpace (k := k) (B := B) δ
    ContMDiffAt I 𝓘(ℝ, Model (k + 1)) ∞ f x ↔
      ContMDiffAt I (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) ∞ (Subtype.val ∘ f) x := by
  let := bandProductChartedSpace (k := k) (B := B) δ
  let := bandProduct_isManifold (k := k) (B := B) δ
  have hfraw := (ContMDiffAt.subtypeVal_comp_iff (I := I)
    (I' := 𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) (bandOpen δ B) f x).symm
  have hforward := contMDiff_linearRechart_id (M := Band δ B)
    (IntrinsicCollarGluing.bandModelEquiv k)
  have hreverse := contMDiff_linearRechart_id_symm (M := Band δ B)
    (IntrinsicCollarGluing.bandModelEquiv k)
  rw [modelWithCornersSelf_prod] at hforward hreverse
  let := bandChartedSpace (k := k) (B := B) δ
  constructor
  · intro hf
    exact hfraw.mp (hreverse.contMDiffAt.comp x hf)
  · intro hf
    exact hforward.contMDiffAt.comp x (hfraw.mpr hf)

/-- Restriction to the full open cylinder preserves local smoothness. -/
theorem contMDiffAt_from_band {δ : ℝ} {f : ℝ × B → X} (p : Band δ B) :
    letI := bandChartedSpace (k := k) (B := B) δ
    ContMDiffAt 𝓘(ℝ, Model (k + 1)) I ∞ (f ∘ Subtype.val) p ↔
      ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) I ∞ f p.val := by
  let := bandProductChartedSpace (k := k) (B := B) δ
  let := bandProduct_isManifold (k := k) (B := B) δ
  have hfraw := contMDiffAt_subtype_iff
    (I := 𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) (I' := I) (n := ∞)
    (U := bandOpen δ B) (f := f) (x := p)
  have hforward := contMDiff_linearRechart_id (M := Band δ B)
    (IntrinsicCollarGluing.bandModelEquiv k)
  have hreverse := contMDiff_linearRechart_id_symm (M := Band δ B)
    (IntrinsicCollarGluing.bandModelEquiv k)
  rw [modelWithCornersSelf_prod] at hforward hreverse
  let := bandChartedSpace (k := k) (B := B) δ
  constructor
  · intro hf
    have hh := hf.comp p (hforward p)
    exact hfraw.mp hh
  · intro hf
    have hh := (hfraw.mpr hf).comp p (hreverse p)
    exact hh

end SmoothMaps

/-- The finite window includes smoothly without changing any coordinate. -/
theorem contMDiff_finiteBandIn (δ : ℝ) :
    letI := IntrinsicCollarGluing.bandChartedSpace (k := k) (B := B) δ
    letI := bandChartedSpace (k := k) (B := B) δ
    ContMDiff 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞
      (finiteBandIn : IntrinsicCollarGluing.Band δ B → Band δ B) := by
  let := IntrinsicCollarGluing.bandChartedSpace (k := k) (B := B) δ
  let := bandChartedSpace (k := k) (B := B) δ
  intro p
  apply contMDiffAt_band_iff_val.mpr
  exact (IntrinsicCollarGluing.contMDiff_band_val δ).contMDiffAt

end Cylinder

section Native

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

local instance fullBandCharts : ChartedSpace (Model (k + 1))
    (Band δ (IntrinsicBoundary.Point k M)) := bandChartedSpace δ

local instance fullBandSmooth : IsManifold 𝓘(ℝ, Model (k + 1)) ∞
    (Band δ (IntrinsicBoundary.Point k M)) := band_isManifold δ

local instance finiteBandCharts : ChartedSpace (Model (k + 1))
    (IntrinsicCollarGluing.Band δ (IntrinsicBoundary.Point k M)) :=
  IntrinsicCollarGluing.bandChartedSpace δ

local instance finiteBandSmooth : IsManifold 𝓘(ℝ, Model (k + 1)) ∞
    (IntrinsicCollarGluing.Band δ (IntrinsicBoundary.Point k M)) :=
  IntrinsicCollarGluing.band_isManifold δ

/-- The finite window has a smooth coordinate inverse germ in the full cylinder.
The fallback is an actual supplied point of the window, so no inhabitance is assumed. -/
theorem finiteBand_inverse_germ
    (q : IntrinsicCollarGluing.Band δ (IntrinsicBoundary.Point k M)) :
    ∃ g : Band δ (IntrinsicBoundary.Point k M) →
      IntrinsicCollarGluing.Band δ (IntrinsicBoundary.Point k M),
      ContMDiffAt 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ g (finiteBandIn q) ∧
        g (finiteBandIn q) = q ∧
          ∀ᶠ p in 𝓝 (finiteBandIn q), finiteBandIn (g p) = p := by
  let g := IntrinsicCollarGluing.intoBand q
    (Subtype.val : Band δ (IntrinsicBoundary.Point k M) → ℝ × IntrinsicBoundary.Point k M)
  refine ⟨g, IntrinsicCollarGluing.contMDiffAt_intoBand q _
    (contMDiff_band_val δ).contMDiffAt q.property, ?_, ?_⟩
  · apply Subtype.ext
    exact IntrinsicCollarGluing.intoBand_val q _ q.property
  · have hn : ∀ᶠ p : Band δ (IntrinsicBoundary.Point k M) in 𝓝 (finiteBandIn q),
        -δ < p.val.1 :=
      (continuous_fst.comp continuous_subtype_val).continuousAt.eventually
        (Ioi_mem_nhds q.property.1.1)
    filter_upwards [hn] with p hp
    apply Subtype.ext
    exact IntrinsicCollarGluing.intoBand_val q _
      (show p.val ∈ IntrinsicCollarGluing.Band δ (IntrinsicBoundary.Point k M) from
        ⟨⟨hp, p.property.1⟩, mem_univ _⟩)

/-- The literal finite coordinate inclusion has an invertible actual differential. -/
theorem bijective_mfderiv_finiteBandIn
    (q : IntrinsicCollarGluing.Band δ (IntrinsicBoundary.Point k M)) :
    Function.Bijective (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1))
      (finiteBandIn : IntrinsicCollarGluing.Band δ (IntrinsicBoundary.Point k M) →
        Band δ (IntrinsicBoundary.Point k M)) q) := by
  obtain ⟨g, hg, hgp, heq⟩ := finiteBand_inverse_germ q
  have hleft : g ∘ finiteBandIn =ᶠ[𝓝 q] id := by
    have hn := continuous_finiteBandIn.continuousAt.eventually heq
    filter_upwards [hn] with p hp
    exact finiteBandIn_injective hp
  have hd := mfderiv_comp q (hg.mdifferentiableAt (by simp))
    ((contMDiff_finiteBandIn δ).mdifferentiableAt (by simp))
  have hid : mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1))
      (g ∘ finiteBandIn) q = ContinuousLinearMap.id ℝ _ := by
    exact hleft.mfderiv_eq.trans (by rw [mfderiv_id]; rfl)
  rw [hid] at hd
  have hi : Function.Injective (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1))
      (finiteBandIn : IntrinsicCollarGluing.Band δ (IntrinsicBoundary.Point k M) →
        Band δ (IntrinsicBoundary.Point k M)) q) := by
    intro v w hvw
    have heval (a : TangentSpace 𝓘(ℝ, Model (k + 1)) q) := congrArg (fun A => A a) hd
    exact (heval v).trans ((congrArg
      (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) g (finiteBandIn q)) hvw).trans
        (heval w).symm)
  exact ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩

include hδ hemb in
omit [IsManifold (𝓡∂ (k + 1)) ∞ M] in
/-- The two actual patch maps have exactly the finite coordinate window as overlap. -/
theorem finiteIn_eq_cylinder_iff
    (x : IntrinsicCollarGluing.Extension (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val))
    (p : Band δ (IntrinsicBoundary.Point k M)) :
    finiteIn (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) x =
      cylinder (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) p ↔
        ∃ q : IntrinsicCollarGluing.Band δ (IntrinsicBoundary.Point k M),
          IntrinsicCollarGluing.cylinder
            (fun r : Half δ (IntrinsicBoundary.Point k M) => C r.val) q = x ∧
          finiteBandIn q = p := by
  constructor
  · intro h
    have hp : p ∈ cylinder (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) ⁻¹'
        (finiteIn (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) '' {x}) :=
      ⟨x, rfl, h⟩
    rw [preimage_cylinder_image_finiteIn _ hδ hemb.injective] at hp
    exact hp
  · rintro ⟨q, rfl, rfl⟩
    rfl

include hδ hemb hC hboundary hinv hzero in
/-- The finite-to-full transition is the produced finite cylinder inverse
followed by the literal coordinate inclusion. -/
theorem finite_cylinder_germ
    (x : IntrinsicCollarGluing.Extension (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val))
    (p : Band δ (IntrinsicBoundary.Point k M))
    (hxp : finiteIn (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) x =
      cylinder (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) p) :
    letI := IntrinsicCollarGluing.extensionChartedSpace hδ C hemb hboundary hzero
    ∃ g : IntrinsicCollarGluing.Extension
      (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) →
      Band δ (IntrinsicBoundary.Point k M),
      ContMDiffAt 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ g x ∧ g x = p ∧
        ∀ᶠ y in 𝓝 x,
          finiteIn (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) y =
            cylinder (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) (g y) := by
  let := IntrinsicCollarGluing.extensionChartedSpace hδ C hemb hboundary hzero
  let := IntrinsicCollarGluing.extension_isManifold hδ C hemb hC hboundary hinv hzero
  obtain ⟨q, rfl, rfl⟩ := (finiteIn_eq_cylinder_iff hδ C hemb x p).mp hxp
  obtain ⟨g, hg, hgq, heq⟩ :=
    IntrinsicCollarGluing.cylinder_inverse_germ hδ C hemb hC hboundary hinv hzero q
  refine ⟨finiteBandIn ∘ g, (contMDiff_finiteBandIn δ).contMDiffAt.comp _ hg,
    congrArg finiteBandIn hgq, ?_⟩
  filter_upwards [heq] with y hy
  exact (congrArg (finiteIn (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val)) hy).symm

include hδ hemb hC hboundary hinv hzero in
/-- The full-to-finite transition restricts the same product coordinates
to the finite window and then uses its already smooth cylinder map. -/
theorem cylinder_finite_germ
    (p : Band δ (IntrinsicBoundary.Point k M))
    (x : IntrinsicCollarGluing.Extension (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val))
    (hpx : cylinder (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) p =
      finiteIn (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) x) :
    letI := IntrinsicCollarGluing.extensionChartedSpace hδ C hemb hboundary hzero
    ∃ g : Band δ (IntrinsicBoundary.Point k M) →
      IntrinsicCollarGluing.Extension (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val),
      ContMDiffAt 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ g p ∧ g p = x ∧
        ∀ᶠ q in 𝓝 p,
          cylinder (fun r : Half δ (IntrinsicBoundary.Point k M) => C r.val) q =
            finiteIn (fun r : Half δ (IntrinsicBoundary.Point k M) => C r.val) (g q) := by
  let := IntrinsicCollarGluing.extensionChartedSpace hδ C hemb hboundary hzero
  let := IntrinsicCollarGluing.extension_isManifold hδ C hemb hC hboundary hinv hzero
  obtain ⟨q, rfl, rfl⟩ := (finiteIn_eq_cylinder_iff hδ C hemb x p).mp hpx.symm
  obtain ⟨g, hg, hgq, heq⟩ := finiteBand_inverse_germ q
  refine ⟨IntrinsicCollarGluing.cylinder
      (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) ∘ g,
    (IntrinsicCollarGluing.contMDiff_cylinder hδ C hemb hC hboundary hinv hzero).contMDiffAt.comp _ hg,
    congrArg _ hgq, ?_⟩
  filter_upwards [heq] with p hp
  exact (congrArg (cylinder (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val)) hp).symm

omit [IsManifold (𝓡∂ (k + 1)) ∞ M] in
/-- The finite native patch and unbounded cylinder cover this quotient literally. -/
theorem completion_open_cover
    (x : Space (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val)) :
    (∃ u, finiteIn (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) u = x) ∨
      ∃ p, cylinder (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) p = x := by
  rcases jointly_surjective _ x with ⟨y, rfl⟩ | ⟨p, rfl⟩
  · exact Or.inl ⟨IntrinsicCollarGluing.original _ y, rfl⟩
  · exact Or.inr ⟨p, rfl⟩

/-- The constructed smooth atlas on the actual half-infinite quotient topology. -/
@[instance_reducible]
def completionChartedSpace : ChartedSpace (Model (k + 1))
    (Space (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val)) := by
  let := IntrinsicCollarGluing.extensionChartedSpace hδ C hemb hboundary hzero
  exact IntrinsicCollarGluing.openCoverChartedSpace
    (isOpenEmbedding_finiteIn _ hδ hemb.injective)
    (isOpenEmbedding_cylinder _ hemb) (completion_open_cover C)

include hC hinv in
/-- Smoothness of this quotient atlas follows from the two derived overlap germs. -/
theorem completion_isManifold :
    letI := completionChartedSpace hδ C hemb hboundary hzero
    IsManifold 𝓘(ℝ, Model (k + 1)) ∞
      (Space (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val)) :=
  by
  let := IntrinsicCollarGluing.extensionChartedSpace hδ C hemb hboundary hzero
  let := IntrinsicCollarGluing.extension_isManifold hδ C hemb hC hboundary hinv hzero
  exact IntrinsicCollarGluing.openCover_isManifold _ _ (completion_open_cover C)
    (finite_cylinder_germ hδ C hemb hC hboundary hinv hzero)
    (cylinder_finite_germ hδ C hemb hC hboundary hinv hzero)

include hC hinv

/-- The same finite native extension embeds smoothly into the full quotient. -/
theorem contMDiff_finiteIn :
    letI := IntrinsicCollarGluing.extensionChartedSpace hδ C hemb hboundary hzero
    letI := completionChartedSpace hδ C hemb hboundary hzero
    ContMDiff 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞
      (finiteIn (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val)) := by
  let := IntrinsicCollarGluing.extensionChartedSpace hδ C hemb hboundary hzero
  let := IntrinsicCollarGluing.extension_isManifold hδ C hemb hC hboundary hinv hzero
  exact IntrinsicCollarGluing.contMDiff_openCover_inclusion _ _ (completion_open_cover C)
    (completion_isManifold hδ C hemb hC hboundary hinv hzero)

/-- Smoothness of the entire unbounded cylinder in the constructed atlas. -/
theorem contMDiff_cylinder :
    letI := completionChartedSpace hδ C hemb hboundary hzero
    ContMDiff 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞
      (cylinder (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val)) := by
  let := IntrinsicCollarGluing.extensionChartedSpace hδ C hemb hboundary hzero
  let := IntrinsicCollarGluing.extension_isManifold hδ C hemb hC hboundary hinv hzero
  exact IntrinsicCollarGluing.contMDiff_openCover_inclusion_right _ _ (completion_open_cover C)
    (completion_isManifold hδ C hemb hC hboundary hinv hzero)

/-- Each finite-patch point has an actual smooth inverse germ. -/
theorem finiteIn_inverse_germ
    (u : IntrinsicCollarGluing.Extension
      (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val)) :
    letI := IntrinsicCollarGluing.extensionChartedSpace hδ C hemb hboundary hzero
    letI := completionChartedSpace hδ C hemb hboundary hzero
    ∃ g : Space (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) →
      IntrinsicCollarGluing.Extension (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val),
      ContMDiffAt 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ g
        (finiteIn (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) u) ∧
        g (finiteIn (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) u) = u ∧
          ∀ᶠ z in 𝓝 (finiteIn (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) u),
            finiteIn (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) (g z) = z := by
  let := IntrinsicCollarGluing.extensionChartedSpace hδ C hemb hboundary hzero
  let := IntrinsicCollarGluing.extension_isManifold hδ C hemb hC hboundary hinv hzero
  let := completionChartedSpace hδ C hemb hboundary hzero
  let := completion_isManifold hδ C hemb hC hboundary hinv hzero
  apply IntrinsicCollarGluing.smooth_inverse_germ_of_lifted_chart
    (isOpenEmbedding_finiteIn _ hδ hemb.injective) u
  apply IsManifold.subset_maximalAtlas
  exact Or.inl ⟨chartAt (Model (k + 1)) u, chart_mem_atlas _ u, rfl⟩

/-- Every point of the full cylinder has an actual smooth inverse germ. -/
theorem cylinder_inverse_germ (p : Band δ (IntrinsicBoundary.Point k M)) :
    letI := completionChartedSpace hδ C hemb hboundary hzero
    ∃ g : Space (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) →
      Band δ (IntrinsicBoundary.Point k M),
      ContMDiffAt 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ g
        (cylinder (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) p) ∧
        g (cylinder (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) p) = p ∧
          ∀ᶠ z in 𝓝 (cylinder (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) p),
            cylinder (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) (g z) = z := by
  let := IntrinsicCollarGluing.extensionChartedSpace hδ C hemb hboundary hzero
  let := completionChartedSpace hδ C hemb hboundary hzero
  let := completion_isManifold hδ C hemb hC hboundary hinv hzero
  apply IntrinsicCollarGluing.smooth_inverse_germ_of_lifted_chart
    (isOpenEmbedding_cylinder _ hemb) p
  apply IsManifold.subset_maximalAtlas
  exact Or.inr ⟨chartAt (Model (k + 1)) p, chart_mem_atlas _ p, rfl⟩

/-- The finite patch inclusion has an invertible actual differential. -/
theorem bijective_mfderiv_finiteIn
    (u : IntrinsicCollarGluing.Extension
      (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val)) :
    letI := IntrinsicCollarGluing.extensionChartedSpace hδ C hemb hboundary hzero
    letI := completionChartedSpace hδ C hemb hboundary hzero
    Function.Bijective (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1))
      (finiteIn (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val)) u) := by
  let := IntrinsicCollarGluing.extensionChartedSpace hδ C hemb hboundary hzero
  let := IntrinsicCollarGluing.extension_isManifold hδ C hemb hC hboundary hinv hzero
  let := completionChartedSpace hδ C hemb hboundary hzero
  have hi := IntrinsicCollarGluing.injective_mfderiv_openCover_inclusion _ _
    (completion_open_cover C) (completion_isManifold hδ C hemb hC hboundary hinv hzero) u
  exact ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩

/-- The unbounded cylinder identifies the actual tangent spaces at every radius. -/
theorem bijective_mfderiv_cylinder (p : Band δ (IntrinsicBoundary.Point k M)) :
    letI := completionChartedSpace hδ C hemb hboundary hzero
    Function.Bijective (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1))
      (cylinder (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val)) p) := by
  let := completionChartedSpace hδ C hemb hboundary hzero
  let := completion_isManifold hδ C hemb hC hboundary hinv hzero
  let j := cylinder (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val)
  obtain ⟨g, hg, hgp, heq⟩ := cylinder_inverse_germ hδ C hemb hC hboundary hinv hzero p
  have hleft : g ∘ j =ᶠ[𝓝 p] id := by
    have hn := (continuous_cylinder
      (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val)).continuousAt.eventually heq
    filter_upwards [hn] with q hq
    exact cylinder_injective _ hemb.injective hq
  have hd := mfderiv_comp p (hg.mdifferentiableAt (by simp))
    ((contMDiff_cylinder hδ C hemb hC hboundary hinv hzero).mdifferentiableAt (by simp))
  have hid : mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) (g ∘ j) p =
      ContinuousLinearMap.id ℝ _ := by
    exact hleft.mfderiv_eq.trans (by rw [mfderiv_id]; rfl)
  rw [hid] at hd
  have hi : Function.Injective (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) j p) := by
    intro v w hvw
    have heval (a : TangentSpace 𝓘(ℝ, Model (k + 1)) p) := congrArg (fun A => A a) hd
    exact (heval v).trans ((congrArg
      (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) g (j p)) hvw).trans (heval w).symm)
  exact ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩

/-- Smoothness of the literal native inclusion across its original boundary seam. -/
theorem contMDiff_original :
    letI := completionChartedSpace hδ C hemb hboundary hzero
    ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞
      (original (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val)) := by
  let := IntrinsicCollarGluing.extensionChartedSpace hδ C hemb hboundary hzero
  let := completionChartedSpace hδ C hemb hboundary hzero
  exact (contMDiff_finiteIn hδ C hemb hC hboundary hinv hzero).comp
    (IntrinsicCollarGluing.contMDiff_original hδ C hemb hC hboundary hinv hzero)

/-- The native inclusion has full differential also at the seam, through the
same finite native extension and the same open finite patch map. -/
theorem bijective_mfderiv_original (x : M) :
    letI := completionChartedSpace hδ C hemb hboundary hzero
    Function.Bijective (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1))
      (original (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val)) x) := by
  let := IntrinsicCollarGluing.extensionChartedSpace hδ C hemb hboundary hzero
  let := completionChartedSpace hδ C hemb hboundary hzero
  have hd := mfderiv_comp x
    ((contMDiff_finiteIn hδ C hemb hC hboundary hinv hzero).mdifferentiableAt (by simp))
    ((IntrinsicCollarGluing.contMDiff_original hδ C hemb hC hboundary hinv hzero).mdifferentiableAt
      (by simp))
  have heq : finiteIn (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) ∘
      IntrinsicCollarGluing.original
        (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) =
      original (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) := rfl
  rw [heq] at hd
  rw [hd]
  exact (bijective_mfderiv_finiteIn hδ C hemb hC hboundary hinv hzero _).comp
    (IntrinsicCollarGluing.bijective_mfderiv_original hδ C hemb hC hboundary hinv hzero x)

/-- The actual completed carrier as a boundaryless smooth manifold. Its
Hausdorff topology and second countability are the proved quotient properties. -/
def completionManifold [T2Space M] [SecondCountableTopology M] : SmoothManifold (k + 1) where
  Point := Space (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val)
  topology := inferInstance
  charts := completionChartedSpace hδ C hemb hboundary hzero
  hausdorff := t2Space_space hδ _ hemb
  secondCountable := secondCountableTopology_space hδ _ hemb hboundary hzero
  smooth := completion_isManifold hδ C hemb hC hboundary hinv hzero

end Native

end FsFltz.Geometry.IntrinsicCompletionGluing
