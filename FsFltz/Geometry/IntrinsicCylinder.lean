import FsFltz.Geometry.IntrinsicCollarGluing
import FsFltz.QuotientGeometry

/-!
# The two-sided intrinsic collar cylinder in the ambient Euclidean model

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 119–160, and `sec:lean`,
lines 783–814. This is the open two-sided cylinder of the boundaryless gluing.
Its product atlas is recharted by an explicit linear coordinate insertion.
No boundary point, positive width, or smooth extension of the collar is
assumed to construct this atlas.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology

namespace FsFltz.Geometry.IntrinsicCollarGluing

/-- The cylinder band is open, independently of whether it is nonempty. -/
def bandOpen (δ : ℝ) (B : Type) [TopologicalSpace B] : TopologicalSpace.Opens (ℝ × B) :=
  ⟨Band δ B, isOpen_Ioo.prod isOpen_univ⟩

/-- Time is the first coordinate; the boundary coordinates follow it. -/
def bandModelEquiv (k : ℕ) : (ℝ × Model k) ≃L[ℝ] Model (k + 1) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun p => WithLp.toLp 2 (Fin.cons p.1 p.2)
      invFun := fun v => (v 0, boundaryDrop k v)
      left_inv := by
        intro p
        apply Prod.ext
        · rfl
        · exact PiLp.ext (fun _ => rfl)
      right_inv := by
        intro v
        apply PiLp.ext
        intro i
        exact Fin.cases rfl (fun _ => rfl) i
      map_add' := by
        intro p q
        apply PiLp.ext
        intro i
        exact Fin.cases rfl (fun _ => rfl) i
      map_smul' := by
        intro r p
        apply PiLp.ext
        intro i
        exact Fin.cases rfl (fun _ => rfl) i }

@[simp] theorem bandModelEquiv_zero {k : ℕ} (p : ℝ × Model k) :
    bandModelEquiv k p 0 = p.1 := rfl

@[simp] theorem bandModelEquiv_succ {k : ℕ} (p : ℝ × Model k) (i : Fin k) :
    bandModelEquiv k p i.succ = p.2 i := rfl

variable {k : ℕ} {B : Type} [TopologicalSpace B] [ChartedSpace (Model k) B]
  [IsManifold 𝓘(ℝ, Model k) ∞ B]

/-- The inherited product charts, expressed with the ordinary product model. -/
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

/-- The cylinder uses the same Euclidean dimension as the native ambient. -/
@[instance_reducible]
def bandChartedSpace (δ : ℝ) : ChartedSpace (Model (k + 1)) (Band δ B) := by
  letI := bandProductChartedSpace (k := k) (B := B) δ
  exact linearRechart (M := Band δ B) (bandModelEquiv k)

theorem band_isManifold (δ : ℝ) :
    letI := bandChartedSpace (k := k) (B := B) δ
    IsManifold 𝓘(ℝ, Model (k + 1)) ∞ (Band δ B) := by
  let := bandProductChartedSpace (k := k) (B := B) δ
  let := bandProduct_isManifold (k := k) (B := B) δ
  exact linearRechart_isManifold (M := Band δ B) (bandModelEquiv k)

/-- The recharted open cylinder has a smooth inclusion into the ordinary product. -/
theorem contMDiff_band_val (δ : ℝ) :
    letI := bandChartedSpace (k := k) (B := B) δ
    ContMDiff 𝓘(ℝ, Model (k + 1)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) ∞
      (Subtype.val : Band δ B → ℝ × B) := by
  let := bandProductChartedSpace (k := k) (B := B) δ
  let := bandProduct_isManifold (k := k) (B := B) δ
  have hr := contMDiff_linearRechart_id_symm (M := Band δ B) (bandModelEquiv k)
  have hv := contMDiff_subtype_val
    (I := 𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) (n := ∞) (U := bandOpen δ B)
  let := bandChartedSpace (k := k) (B := B) δ
  exact hv.comp hr

section SmoothMaps

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X]

/-- A map into the recharted cylinder is smooth exactly when its ordinary
product inclusion is smooth. -/
theorem contMDiffAt_band_iff_val {δ : ℝ} {f : X → Band δ B} {x : X} :
    letI := bandChartedSpace (k := k) (B := B) δ
    ContMDiffAt I 𝓘(ℝ, Model (k + 1)) ∞ f x ↔
      ContMDiffAt I (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) ∞ (Subtype.val ∘ f) x := by
  let := bandProductChartedSpace (k := k) (B := B) δ
  let := bandProduct_isManifold (k := k) (B := B) δ
  have hfraw := (ContMDiffAt.subtypeVal_comp_iff (I := I)
    (I' := 𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) (bandOpen δ B) f x).symm
  have hforward := contMDiff_linearRechart_id (M := Band δ B) (bandModelEquiv k)
  have hreverse := contMDiff_linearRechart_id_symm (M := Band δ B) (bandModelEquiv k)
  rw [modelWithCornersSelf_prod] at hforward hreverse
  let := bandChartedSpace (k := k) (B := B) δ
  constructor
  · intro hf
    exact hfraw.mp (hreverse.contMDiffAt.comp x hf)
  · intro hf
    exact hforward.contMDiffAt.comp x (hfraw.mpr hf)

/-- Restricting an ordinary product map to the cylinder and recharting the
source does not change its smoothness at a cylinder point. -/
theorem contMDiffAt_from_band {δ : ℝ} {f : ℝ × B → X} (p : Band δ B) :
    letI := bandChartedSpace (k := k) (B := B) δ
    ContMDiffAt 𝓘(ℝ, Model (k + 1)) I ∞ (f ∘ Subtype.val) p ↔
      ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) I ∞ f p.val := by
  let := bandProductChartedSpace (k := k) (B := B) δ
  let := bandProduct_isManifold (k := k) (B := B) δ
  have hfraw := contMDiffAt_subtype_iff
    (I := 𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) (I' := I) (n := ∞)
    (U := bandOpen δ B) (f := f) (x := p)
  have hforward := contMDiff_linearRechart_id (M := Band δ B) (bandModelEquiv k)
  have hreverse := contMDiff_linearRechart_id_symm (M := Band δ B) (bandModelEquiv k)
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

/-- The boundaryless cylinder with the actual open-subset topology. -/
def bandManifold (δ : ℝ) (B : SmoothManifold k) : SmoothManifold (k + 1) where
  Point := Band δ B.Point
  topology := inferInstance
  charts := bandChartedSpace δ
  hausdorff := inferInstance
  secondCountable := inferInstance
  smooth := band_isManifold δ

end FsFltz.Geometry.IntrinsicCollarGluing
