import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Sites.Limits
import PrimalitySheafVerification.ManuscriptAudit.EtaleCechDirectSum

/-! The native Čech cochains of a product of sheaves are exact
in each positive degree in which all factors are exact. -/

namespace ManuscriptAudit.EtaleCechProduct

open AlgebraicTopology CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
open EtaleCechDirectSum

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {C : Type*} [Category* C] [HasFiniteLimits C]
variable {J : GrothendieckTopology C} {U T : C} (f : U ⟶ T)
variable {I : Type} (P : I → Sheaf J AddCommGrpCat.{0})

private abbrev Ab := AddCommGrpCat.{0}

private abbrev projection (a : I) :
    Cech f (∏ᶜ P).obj ⟶ Cech f (P a).obj :=
  (cochains f).map (Pi.π P a).hom

private abbrev evalAt (n : ℕ) : Sheaf J Ab ⥤ Ab :=
  sheafToPresheaf J Ab ⋙ (evaluation Cᵒᵖ Ab).obj ((Arrow.mk f).cechNerve.rightOp.obj ⦋n⦌)

private def evalProductIso (n : ℕ) :
    (Cech f (∏ᶜ P).obj).X n ≅ ∏ᶜ fun a ↦ (Cech f (P a).obj).X n :=
  PreservesProduct.iso (evalAt f (J := J) n) P

private def tuples (n : ℕ) :
    (Cech f (∏ᶜ P).obj).X n ≃ (∀ a, (Cech f (P a).obj).X n) :=
  (evalProductIso f P n).addCommGroupIsoToAddEquiv.toEquiv.trans (Concrete.productEquiv _)

private theorem tuples_apply (n : ℕ) (z : (Cech f (∏ᶜ P).obj).X n) (a : I) :
    tuples f P n z a = (projection f P a).f n z := by
  let Q := fun a ↦ (Cech f (P a).obj).X n
  let E := evalAt f (J := J) n
  have h : (evalProductIso f P n).hom ≫ Pi.π Q a = (projection f P a).f n := by
    change (PreservesProduct.iso E P).hom ≫ Pi.π (fun i ↦ E.obj (P i)) a =
      E.map (Pi.π P a)
    rw [PreservesProduct.iso_hom]
    exact piComparison_comp_π E P a
  change Concrete.productEquiv Q ((evalProductIso f P n).hom z) a = _
  rw [Concrete.productEquiv_apply_apply]
  exact ConcreteCategory.congr_hom h z

/-- For the actual product, a tuple of primitives gives a primitive
of any Čech cocycle in a degree where all factors are exact. -/
theorem product_exactAt_succ (n : ℕ) (h : ∀ a, (Cech f (P a).obj).ExactAt (n + 1)) :
    (Cech f (∏ᶜ P).obj).ExactAt (n + 1) := by
  classical
  apply (cochainExactAt_succ_iff _ n).mpr
  intro z hz
  let q := projection f P
  have hZ (a : I) : (Cech f (P a).obj).d (n + 1) (n + 2) ((q a).f (n + 1) z) = 0 := by
    have hm : (Cech f (P a).obj).d (n + 1) (n + 2) ((q a).f (n + 1) z) =
        (q a).f (n + 2) ((Cech f (∏ᶜ P).obj).d (n + 1) (n + 2) z) :=
      ConcreteCategory.congr_hom ((q a).comm (n + 1) (n + 2)) z
    rw [hm, hz]
    exact ((q a).f (n + 2)).hom.map_zero
  choose y hy using fun a ↦
    (cochainExactAt_succ_iff _ n).mp (h a) ((q a).f (n + 1) z) (hZ a)
  let w := (tuples f P n).symm y
  refine ⟨w, (tuples f P (n + 1)).injective ?_⟩
  funext a
  rw [tuples_apply, tuples_apply]
  have hm := ConcreteCategory.congr_hom ((q a).comm n (n + 1)) w
  change (Cech f (P a).obj).d n (n + 1) ((q a).f n w) =
    (q a).f (n + 1) ((Cech f (∏ᶜ P).obj).d n (n + 1) w) at hm
  change (q a).f (n + 1) ((Cech f (∏ᶜ P).obj).d n (n + 1) w) = (q a).f (n + 1) z
  rw [← hm]
  have hw : (q a).f n w = y a :=
    (tuples_apply f P n w a).symm.trans
      (congrFun ((tuples f P n).apply_symm_apply y) a)
  rw [hw, hy]

end

end ManuscriptAudit.EtaleCechProduct

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.EtaleCechProduct.product_exactAt_succ
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
