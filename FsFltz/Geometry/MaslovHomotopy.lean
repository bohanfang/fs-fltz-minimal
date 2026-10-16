import FsFltz.Geometry.Maslov
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Equivalence of concrete smooth Maslov homotopies

Source: `geoemtric-part-fsf.tex`, `def:maslov`, lines 212–244, and
`sec:lean`, lines 794–814. The constructions use the actual jointly smooth
complex structures and nowhere-zero sections of `MaslovFamily`.
Concatenation uses smooth parameter functions with constant endpoint collars.
It does not assume contractibility of compatible almost complex structures
or the identification of the tensor model with the canonical line bundle.
-/

noncomputable section
open scoped Manifold ContDiff
open Set Filter

namespace FsFltz.Geometry

/-- Concatenate arbitrary time-dependent data after making each end constant
on a collar. The two reparametrizations take values in `[0,1]` on all of `ℝ`. -/
def smoothConcat {A : Type*} (f g : ℝ → A) (t : ℝ) : A :=
  if t ≤ 1 / 2 then f (Real.smoothTransition (4 * t))
  else g (Real.smoothTransition (4 * t - 3))

theorem smoothConcat_eq_left {A : Type*} {f g : ℝ → A}
    (hfg : f 1 = g 0) {t : ℝ} (ht : t < 3 / 4) :
    smoothConcat f g t = f (Real.smoothTransition (4 * t)) := by
  by_cases h : t ≤ 1 / 2
  · simp only [smoothConcat, ite_eq_left h]
  · have hl : 1 ≤ 4 * t := by linarith
    have hr : 4 * t - 3 ≤ 0 := by linarith
    simp only [smoothConcat, ite_eq_right h, Real.smoothTransition.one_of_one_le hl,
      Real.smoothTransition.zero_of_nonpos hr, hfg]

theorem smoothConcat_eq_right {A : Type*} {f g : ℝ → A}
    (hfg : f 1 = g 0) {t : ℝ} (ht : 1 / 4 < t) :
    smoothConcat f g t = g (Real.smoothTransition (4 * t - 3)) := by
  by_cases h : t ≤ 1 / 2
  · have hl : 1 ≤ 4 * t := by linarith
    have hr : 4 * t - 3 ≤ 0 := by linarith
    simp only [smoothConcat, ite_eq_left h, Real.smoothTransition.one_of_one_le hl,
      Real.smoothTransition.zero_of_nonpos hr, hfg]
  · simp only [smoothConcat, ite_eq_right h]

@[simp] theorem smoothConcat_zero {A : Type*} (f g : ℝ → A) :
    smoothConcat f g 0 = f 0 := by
  norm_num [smoothConcat, Real.smoothTransition.zero]

@[simp] theorem smoothConcat_one {A : Type*} (f g : ℝ → A) :
    smoothConcat f g 1 = g 1 := by
  norm_num [smoothConcat, Real.smoothTransition.one]

theorem map_smoothConcat {A B : Type*} (k : A → B) (f g : ℝ → A) (t : ℝ) :
    k (smoothConcat f g t) = smoothConcat (fun t => k (f t)) (fun t => k (g t)) t := by
  unfold smoothConcat
  split <;> rfl

namespace SmoothNearInterval

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Smooth changes of time preserving the parameter interval preserve its
open-neighborhood regularity, without a uniform collar assumption. -/
theorem reparam {s : Set E} {f : ℝ × E → F} (hf : SmoothNearInterval s f)
    {r : ℝ → ℝ} (hr : ContDiff ℝ ∞ r)
    (hmem : MapsTo r parameterInterval parameterInterval) :
    SmoothNearInterval s (fun p => f (r p.1, p.2)) := by
  rcases hf with ⟨U, hU, hsub, hsmooth⟩
  let R : ℝ × E → ℝ × E := fun p => (r p.1, p.2)
  have hR : ContDiff ℝ ∞ R := (hr.comp contDiff_fst).prodMk contDiff_snd
  refine ⟨R ⁻¹' U, hU.preimage hR.continuous, ?_, ?_⟩
  · intro p hp
    exact hsub ⟨hmem hp.1, hp.2⟩
  · exact hsmooth.comp hR.contDiffOn (fun _ hp => hp)

/-- A smooth section gives a constant family on the whole time axis. -/
theorem constant {s : Set E} (hs : IsOpen s) {f : E → F}
    (hf : ContDiffOn ℝ ∞ f s) :
    SmoothNearInterval s (fun p => f p.2) := by
  refine ⟨univ ×ˢ s, isOpen_univ.prod hs, ?_, ?_⟩
  · intro p hp
    exact ⟨mem_univ _, hp.2⟩
  · exact hf.comp contDiff_snd.contDiffOn (fun _ hp => hp.2)

/-- The collar overlap makes the piecewise formula smooth on an actual open
neighborhood, even when the spatial set and its collar are noncompact. -/
theorem concat {s : Set E} {f g : ℝ × E → F}
    (hf : SmoothNearInterval s f) (hg : SmoothNearInterval s g)
    (hfg : ∀ x, f (1, x) = g (0, x)) :
    SmoothNearInterval s
      (fun p => smoothConcat (fun t => f (t, p.2)) (fun t => g (t, p.2)) p.1) := by
  rcases hf with ⟨U, hU, hsubU, hsmoothU⟩
  rcases hg with ⟨V, hV, hsubV, hsmoothV⟩
  let R : ℝ × E → ℝ × E := fun p => (Real.smoothTransition (4 * p.1), p.2)
  let S : ℝ × E → ℝ × E := fun p => (Real.smoothTransition (4 * p.1 - 3), p.2)
  have hR : ContDiff ℝ ∞ R := by
    exact (Real.smoothTransition.contDiff.comp
      (contDiff_const.mul contDiff_fst)).prodMk contDiff_snd
  have hS : ContDiff ℝ ∞ S := by
    exact (Real.smoothTransition.contDiff.comp
      ((contDiff_const.mul contDiff_fst).sub contDiff_const)).prodMk contDiff_snd
  let L : Set (ℝ × E) := {p | p.1 < 3 / 4}
  let H : Set (ℝ × E) := {p | 1 / 4 < p.1}
  have hL : IsOpen L := isOpen_lt continuous_fst continuous_const
  have hH : IsOpen H := isOpen_lt continuous_const continuous_fst
  refine ⟨(R ⁻¹' U ∩ L) ∪ (S ⁻¹' V ∩ H),
    ((hU.preimage hR.continuous).inter hL).union
      ((hV.preimage hS.continuous).inter hH), ?_, ?_⟩
  · intro p hp
    have hRp : R p ∈ U := hsubU
      ⟨⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩, hp.2⟩
    have hSp : S p ∈ V := hsubV
      ⟨⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩, hp.2⟩
    by_cases ht : p.1 < 3 / 4
    · exact Or.inl ⟨hRp, ht⟩
    · exact Or.inr ⟨hSp, by dsimp [H]; linarith⟩
  · intro p hp
    rcases hp with hp | hp
    · have hfR : ContDiffAt ℝ ∞ (f ∘ R) p :=
        (hsmoothU.contDiffAt (hU.mem_nhds hp.1)).comp p hR.contDiffAt
      apply (hfR.congr_of_eventuallyEq ?_).contDiffWithinAt
      filter_upwards [hL.mem_nhds hp.2] with q hq
      exact smoothConcat_eq_left (hfg q.2) hq
    · have hgS : ContDiffAt ℝ ∞ (g ∘ S) p :=
        (hsmoothV.contDiffAt (hV.mem_nhds hp.1)).comp p hS.contDiffAt
      apply (hgS.congr_of_eventuallyEq ?_).contDiffWithinAt
      filter_upwards [hH.mem_nhds hp.2] with q hq
      exact smoothConcat_eq_right (hfg q.2) hq

end SmoothNearInterval

namespace MaslovHomotopy

variable {n : ℕ} {M : SmoothManifold (2 * n)} {eta : M.Form 2}
  {s₀ s₁ s₂ : MaslovRepresentative M eta}

/-- The constant representative, with smooth extension across both ends. -/
def refl (s : MaslovRepresentative M eta) : MaslovHomotopy s s where
  family :=
    { J := fun _ => s.J
      tensor := fun _ => s.tensor
      compatible := fun _ _ => s.compatible
      canonical := fun _ _ => s.canonical
      nowhereZero := fun _ _ => s.nowhereZero
      smoothJ := fun a => SmoothNearInterval.constant
        (chartAt (Model (2 * n)) a).open_target (s.compatible.1 a)
      smoothSection := fun a => SmoothNearInterval.constant
        (chartAt (Model (2 * n)) a).open_target (s.smooth a) }
  sourceJ := rfl
  targetJ := rfl
  sourceSection := rfl
  targetSection := rfl

/-- Reverse the actual family by the smooth substitution `t ↦ 1 - t`. -/
def symm (h : MaslovHomotopy s₀ s₁) : MaslovHomotopy s₁ s₀ where
  family :=
    { J := fun t => h.family.J (1 - t)
      tensor := fun t => h.family.tensor (1 - t)
      compatible := fun t ht => h.family.compatible (1 - t)
        ⟨by linarith [ht.2], by linarith [ht.1]⟩
      canonical := fun t ht => h.family.canonical (1 - t)
        ⟨by linarith [ht.2], by linarith [ht.1]⟩
      nowhereZero := fun t ht => h.family.nowhereZero (1 - t)
        ⟨by linarith [ht.2], by linarith [ht.1]⟩
      smoothJ := fun a => (h.family.smoothJ a).reparam
        (contDiff_const.sub contDiff_id)
        (fun t ht => ⟨by linarith [ht.2], by linarith [ht.1]⟩)
      smoothSection := fun a => (h.family.smoothSection a).reparam
        (contDiff_const.sub contDiff_id)
        (fun t ht => ⟨by linarith [ht.2], by linarith [ht.1]⟩) }
  sourceJ := by simpa using h.targetJ
  targetJ := by simpa using h.sourceJ
  sourceSection := by simpa using h.targetSection
  targetSection := by simpa using h.sourceSection

/-- Smooth concatenation of the compatible structures and nowhere-zero
sections, using constant collars to retain joint smoothness at the join. -/
def trans (h : MaslovHomotopy s₀ s₁) (k : MaslovHomotopy s₁ s₂) :
    MaslovHomotopy s₀ s₂ where
  family :=
    { J := smoothConcat h.family.J k.family.J
      tensor := smoothConcat h.family.tensor k.family.tensor
      compatible := fun t _ => by
        unfold smoothConcat
        split
        · exact h.family.compatible _
            ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
        · exact k.family.compatible _
            ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
      canonical := fun t _ x => by
        unfold smoothConcat
        split
        · exact h.family.canonical _
            ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩ x
        · exact k.family.canonical _
            ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩ x
      nowhereZero := fun t _ x => by
        unfold smoothConcat
        split
        · exact h.family.nowhereZero _
            ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩ x
        · exact k.family.nowhereZero _
            ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩ x
      smoothJ := fun a => by
        have hjoin : ∀ y, almostComplexInChart M a (h.family.J 1) y =
            almostComplexInChart M a (k.family.J 0) y := by
          intro y
          rw [h.targetJ, k.sourceJ]
        convert (h.family.smoothJ a).concat (k.family.smoothJ a) hjoin using 1
        funext p
        exact map_smoothConcat (fun J => almostComplexInChart M a J p.2)
          h.family.J k.family.J p.1
      smoothSection := fun a => by
        have hjoin : ∀ y, squaredTensorInChart M a (h.family.tensor 1) y =
            squaredTensorInChart M a (k.family.tensor 0) y := by
          intro y
          rw [h.targetSection, k.sourceSection]
        convert (h.family.smoothSection a).concat (k.family.smoothSection a) hjoin using 1
        funext p
        exact map_smoothConcat (fun s => squaredTensorInChart M a s p.2)
          h.family.tensor k.family.tensor p.1 }
  sourceJ := by simpa using h.sourceJ
  targetJ := by simpa using k.targetJ
  sourceSection := by simpa using h.sourceSection
  targetSection := by simpa using k.targetSection

end MaslovHomotopy

namespace MaslovHomotopic

variable {n : ℕ} {M : SmoothManifold (2 * n)} {eta : M.Form 2}
  {s₀ s₁ s₂ : MaslovRepresentative M eta}

theorem refl (s : MaslovRepresentative M eta) : MaslovHomotopic s s :=
  ⟨MaslovHomotopy.refl s⟩

theorem symm (h : MaslovHomotopic s₀ s₁) : MaslovHomotopic s₁ s₀ :=
  h.map MaslovHomotopy.symm

theorem trans (h : MaslovHomotopic s₀ s₁) (k : MaslovHomotopic s₁ s₂) :
    MaslovHomotopic s₀ s₂ := by
  rcases h with ⟨h⟩
  rcases k with ⟨k⟩
  exact ⟨h.trans k⟩

theorem equivalence : Equivalence (MaslovHomotopic (M := M) (eta := eta)) :=
  ⟨refl, symm, trans⟩

end MaslovHomotopic

namespace MaslovClass

variable {n : ℕ} {M : SmoothManifold (2 * n)} {eta : M.Form 2}

/-- The generated quotient has precisely the concrete smooth homotopy
relation: its equality can be witnessed by one smooth compatible family. -/
theorem eq_iff_homotopic (s₀ s₁ : MaslovRepresentative M eta) :
    (Quot.mk _ s₀ : MaslovClass M eta) = Quot.mk _ s₁ ↔ MaslovHomotopic s₀ s₁ := by
  constructor
  · intro h
    have hg : Relation.EqvGen (MaslovHomotopic (M := M) (eta := eta)) s₀ s₁ :=
      Quot.eqvGen_exact h
    clear h
    induction hg with
    | rel _ _ h => exact h
    | refl s => exact MaslovHomotopic.refl s
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  · exact Quot.sound

end MaslovClass

end FsFltz.Geometry
