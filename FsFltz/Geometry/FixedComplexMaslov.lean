import FsFltz.Geometry.CompatibleComplexPath

/-!
# Maslov classes with a fixed compatible complex structure

Source: `geoemtric-part-fsf.tex`, `def:maslov`, lines 212–232, and
`sec:lean`, lines 794–814. A fixed-structure representative is the existing
smooth nowhere-zero squared canonical section with its complex structure
fixed. Its homotopies keep that structure fixed, including on the smooth
extension beyond the parameter interval.

Normalizing a varying-structure homotopy gives a fixed-structure homotopy.
When the endpoints already have the fixed structure, normalization leaves
their sections unchanged. Thus allowing the structure to vary identifies
no additional fixed-structure section classes.
Conversely, the constructed compatible path joins every representative to
its normalization. This proves the equivalence with the existing varying-J
quotient without assuming a path or a homotopy as additional input.
-/

noncomputable section
open scoped Manifold ContDiff

namespace FsFltz.Geometry

namespace MaslovRepresentative

theorem ext_structure_tensor {n : ℕ} {M : SmoothManifold (2 * n)}
    {eta : M.Form 2} {s t : MaslovRepresentative M eta}
    (hJ : s.J = t.J) (hs : s.tensor = t.tensor) : s = t := by
  cases s
  cases t
  cases hJ
  cases hs
  rfl

@[simp] theorem changeCompatibleStructure_self {n : ℕ}
    {M : SmoothManifold (2 * n)} {eta : M.Form 2}
    (s : MaslovRepresentative M eta) :
    s.changeCompatibleStructure s.J s.compatible = s := by
  have ht : (s.changeCompatibleStructure s.J s.compatible).tensor = s.tensor := by
    funext x
    exact transportSquaredTensor_self _ (s.compatible.2.1 x) _
  exact ext_structure_tensor rfl ht

/-- The explicit compatible path produces the actual section homotopy;
no compatible path is an additional premise. -/
theorem homotopic_changeCompatibleStructure {n : ℕ}
    {M : SmoothManifold (2 * n)} {eta : M.Form 2}
    (s : MaslovRepresentative M eta) (J : AlmostComplexField M)
    (hJ : IsCompatibleAlmostComplex M eta J) :
    MaslovHomotopic s (s.changeCompatibleStructure J hJ) := by
  obtain ⟨P, h₀, h₁, hc, hs⟩ :=
    exists_smooth_compatibleComplexPath M eta s.J J s.compatible hJ
  have h := s.homotopyChangeCompatibleStructure P hc hs h₀
  subst J
  exact ⟨h⟩

end MaslovRepresentative

/-- Existing geometric representatives whose compatible structure is fixed. -/
abbrev FixedComplexMaslovRepresentative {n : ℕ} (M : SmoothManifold (2 * n))
    (eta : M.Form 2) (J : AlmostComplexField M) :=
  {s : MaslovRepresentative M eta // s.J = J}

/-- A smooth section homotopy in one fixed squared canonical bundle. -/
def FixedComplexMaslovHomotopic {n : ℕ} {M : SmoothManifold (2 * n)}
    {eta : M.Form 2} {J : AlmostComplexField M}
    (s₀ s₁ : FixedComplexMaslovRepresentative M eta J) : Prop :=
  ∃ h : MaslovHomotopy s₀.val s₁.val, ∀ t, h.family.J t = J

namespace FixedComplexMaslovRepresentative

variable {n : ℕ} {M : SmoothManifold (2 * n)} {eta : M.Form 2}
  {J : AlmostComplexField M}

/-- Transport to the already fixed structure is literally the same section. -/
theorem change_eq (s : FixedComplexMaslovRepresentative M eta J)
    (hJ : IsCompatibleAlmostComplex M eta J) :
    s.val.changeCompatibleStructure J hJ = s.val := by
  apply MaslovRepresentative.ext_structure_tensor s.property.symm
  funext x
  change transportSquaredTensor (s.val.J x) (J x) (s.val.tensor x) = s.val.tensor x
  rw [s.property]
  exact transportSquaredTensor_self _ (hJ.2.1 x) _

/-- Every existing smooth varying-structure homotopy between fixed-structure
sections normalizes to a smooth homotopy in their original bundle. -/
theorem homotopic_iff (s₀ s₁ : FixedComplexMaslovRepresentative M eta J) :
    FixedComplexMaslovHomotopic s₀ s₁ ↔ MaslovHomotopic s₀.val s₁.val := by
  constructor
  · rintro ⟨h, _⟩
    exact ⟨h⟩
  · rintro ⟨h⟩
    have hJ : IsCompatibleAlmostComplex M eta J := s₀.property ▸ s₀.val.compatible
    have h₀ := s₀.change_eq hJ
    have h₁ := s₁.change_eq hJ
    let k := h.changeCompatibleStructure J hJ
    refine ⟨{
      family := k.family
      sourceJ := s₀.property.symm
      targetJ := s₁.property.symm
      sourceSection := k.sourceSection.trans (congrArg MaslovRepresentative.tensor h₀)
      targetSection := k.targetSection.trans (congrArg MaslovRepresentative.tensor h₁)
    }, fun _ => rfl⟩

end FixedComplexMaslovRepresentative

/-- Homotopy classes of smooth nonzero sections at one fixed compatible J. -/
def FixedComplexMaslovClass {n : ℕ} (M : SmoothManifold (2 * n))
    (eta : M.Form 2) (J : AlmostComplexField M) :=
  Quot (FixedComplexMaslovHomotopic (M := M) (eta := eta) (J := J))

namespace FixedComplexMaslovClass

variable {n : ℕ} {M : SmoothManifold (2 * n)} {eta : M.Form 2}
  {J : AlmostComplexField M}

/-- Forget that the structure was fixed; the underlying section is unchanged. -/
def toMaslovClass : FixedComplexMaslovClass M eta J → MaslovClass M eta :=
  Quot.map Subtype.val (fun a b h => (a.homotopic_iff b).mp h)

/-- A varying-J homotopy cannot collapse distinct fixed-J section classes. -/
theorem toMaslovClass_injective :
    Function.Injective (toMaslovClass (M := M) (eta := eta) (J := J)) := by
  intro a b
  induction a using Quot.inductionOn with
  | h a =>
    induction b using Quot.inductionOn with
    | h b =>
      intro hab
      exact Quot.sound ((a.homotopic_iff b).mpr
        ((MaslovClass.eq_iff_homotopic a.val b.val).mp hab))

/-- Equality in the quotient is exactly one smooth homotopy of sections
with the complex structure fixed throughout. -/
theorem eq_iff_homotopic (a b : FixedComplexMaslovRepresentative M eta J) :
    (Quot.mk _ a : FixedComplexMaslovClass M eta J) = Quot.mk _ b ↔
      FixedComplexMaslovHomotopic a b := by
  constructor
  · intro h
    exact (a.homotopic_iff b).mpr ((MaslovClass.eq_iff_homotopic a.val b.val).mp
      (congrArg toMaslovClass h))
  · exact Quot.sound

/-- Normalize every representative, with well-definedness supplied by the
actual joint section-transport theorem. -/
def normalize (hJ : IsCompatibleAlmostComplex M eta J) :
    MaslovClass M eta → FixedComplexMaslovClass M eta J :=
  Quot.map (fun s => ⟨s.changeCompatibleStructure J hJ, rfl⟩)
    (by
      intro a b h
      rcases h with ⟨h⟩
      exact ⟨h.changeCompatibleStructure J hJ, fun _ => rfl⟩)

theorem normalize_toMaslovClass (hJ : IsCompatibleAlmostComplex M eta J)
    (a : FixedComplexMaslovClass M eta J) :
    normalize hJ (toMaslovClass a) = a := by
  induction a using Quot.inductionOn with
  | h a =>
    change Quot.mk _ (⟨a.val.changeCompatibleStructure J hJ, rfl⟩ :
      FixedComplexMaslovRepresentative M eta J) = Quot.mk _ a
    congr 1
    exact Subtype.ext (a.change_eq hJ)

/-- Every varying-structure class is represented in the fixed bundle,
using the constructed compatible path to certify the section homotopy. -/
theorem toMaslovClass_normalize (hJ : IsCompatibleAlmostComplex M eta J)
    (a : MaslovClass M eta) : toMaslovClass (normalize hJ a) = a := by
  induction a using Quot.inductionOn with
  | h a =>
    exact (Quot.sound (a.homotopic_changeCompatibleStructure J hJ)).symm

/-- Fixed-J section classes in the tensor encoding and the encoded
varying-J classes are equivalent, with normalization as the explicit inverse.
The native vertical-family bundle correspondence is a separate bridge. -/
def equivMaslovClass (hJ : IsCompatibleAlmostComplex M eta J) :
    FixedComplexMaslovClass M eta J ≃ MaslovClass M eta where
  toFun := toMaslovClass
  invFun := normalize hJ
  left_inv := normalize_toMaslovClass hJ
  right_inv := toMaslovClass_normalize hJ

@[simp] theorem equivMaslovClass_apply_mk (hJ : IsCompatibleAlmostComplex M eta J)
    (a : FixedComplexMaslovRepresentative M eta J) :
    equivMaslovClass hJ (Quot.mk _ a) = Quot.mk _ a.val := rfl

@[simp] theorem equivMaslovClass_symm_apply_mk (hJ : IsCompatibleAlmostComplex M eta J)
    (a : MaslovRepresentative M eta) :
    (equivMaslovClass hJ).symm (Quot.mk _ a) =
      Quot.mk _ (⟨a.changeCompatibleStructure J hJ, rfl⟩ :
        FixedComplexMaslovRepresentative M eta J) := rfl

end FixedComplexMaslovClass

end FsFltz.Geometry
