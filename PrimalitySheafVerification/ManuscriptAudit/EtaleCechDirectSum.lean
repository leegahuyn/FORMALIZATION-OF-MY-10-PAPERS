import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.AlgebraicTopology.CechNerve
import PrimalitySheafVerification.ManuscriptAudit.FiniteSupportEtaleSheaf

/-! The native Čech cohomology of a finite-support sum is computed componentwise. -/

namespace ManuscriptAudit.EtaleCechDirectSum

open AlgebraicGeometry AlgebraicTopology CategoryTheory CategoryTheory.Limits Opposite
open FiniteSupportPresheaf
open scoped Simplicial

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v

variable {C : Type u} [Category.{v} C] [HasFiniteLimits C]
variable {U T : C} (f : U ⟶ T)

private abbrev Ab := AddCommGrpCat.{0}

/-- The alternating Čech cochains of an additive presheaf on the actual arrow. -/
def cochains : (Cᵒᵖ ⥤ Ab) ⥤ CochainComplex Ab ℕ :=
  (CategoryTheory.Functor.whiskeringLeft _ _ _).obj (Arrow.mk f).cechNerve.rightOp ⋙
    alternatingCofaceMapComplex Ab

abbrev Cech (P : Cᵒᵖ ⥤ Ab) := (cochains f).obj P

/-- Positive cochain exactness in terms of actual cycles and boundaries. -/
theorem cochainExactAt_succ_iff (K : CochainComplex Ab ℕ) (n : ℕ) :
    K.ExactAt (n + 1) ↔ ∀ z : K.X (n + 1), K.d (n + 1) (n + 2) z = 0 →
      ∃ y : K.X n, K.d n (n + 1) y = z := by
  exact (K.exactAt_iff' (i := n) (j := n + 1) (k := n + 2)
    (CochainComplex.prev_nat_succ n) (CochainComplex.next ℕ (n + 1))).trans ShortComplex.ab_exact_iff

variable {I : Type} (P : I → Cᵒᵖ ⥤ Ab)

private abbrev degree (n : ℕ) : Cᵒᵖ := (Arrow.mk f).cechNerve.rightOp.obj ⦋n⦌

private theorem d_component (i j : ℕ) (a : I) (z : sections P (degree f i)) :
    (show sections P (degree f j) from (Cech f (directSum P)).d i j z) a =
      (Cech f (P a)).d i j (z a) := by
  let e := (cochains f).map (component P a)
  exact (ConcreteCategory.congr_hom (e.comm i j) z).symm

/-- Each cycle in the finite-support sum has a boundary supported on
the same finite set, if all the components are exact in that degree. -/
theorem directSum_exactAt_succ (n : ℕ) (h : ∀ a, (Cech f (P a)).ExactAt (n + 1)) :
    (Cech f (directSum P)).ExactAt (n + 1) := by
  classical
  apply (cochainExactAt_succ_iff _ (n := n)).mpr
  intro z hz
  change sections P (degree f (n + 1)) at z
  have hz' (a : I) : (Cech f (P a)).d (n + 1) (n + 2) (z a) = 0 :=
    (d_component f P (n + 1) (n + 2) a z).symm.trans
      (congrArg (fun t : sections P (degree f (n + 2)) ↦ t a) hz)
  choose y hy using fun a ↦ (cochainExactAt_succ_iff (Cech f (P a)) n).mp (h a) (z a) (hz' a)
  let w : sections P (degree f n) := DFinsupp.mk z.support (fun a ↦ y a.val)
  refine ⟨w, ?_⟩
  change (show sections P (degree f (n + 1)) from (Cech f (directSum P)).d n (n + 1) w) = z
  apply DFinsupp.ext
  intro a
  rw [d_component f P n (n + 1) a w]
  by_cases ha : a ∈ z.support
  · change (Cech f (P a)).d n (n + 1)
      ((DFinsupp.mk z.support (fun i ↦ y i.val)) a) = z a
    rw [DFinsupp.mk_of_mem ha, hy]
  · change ((Cech f (P a)).d n (n + 1)).hom
      ((DFinsupp.mk z.support (fun i ↦ y i.val)) a) = z a
    rw [DFinsupp.mk_of_notMem ha, map_zero]
    symm
    by_contra hza
    exact ha ((DFinsupp.mem_support_toFun z a).mpr hza)

/-- Positive Čech cohomology of the actual finite-support affine étale
sheaf vanishes whenever that of its individual summands vanishes. -/
theorem affineEtaleDirectSum_H_succ_isZero
    {S : Scheme.{0}} [HasFiniteLimits S.AffineEtale] {V W : S.AffineEtale} (g : V ⟶ W)
    (A : I → Sheaf (Scheme.AffineEtale.topology S) Ab) (n : ℕ)
    (h : ∀ a, IsZero ((Cech g (A a).obj).homology (n + 1))) :
    IsZero ((Cech g (affineEtaleDirectSum S A).obj).homology (n + 1)) := by
  apply HomologicalComplex.ExactAt.isZero_homology
  exact directSum_exactAt_succ g (fun a ↦ (A a).obj) n
    (fun a ↦ ((Cech g (A a).obj).exactAt_iff_isZero_homology (n + 1)).mpr (h a))

end

end ManuscriptAudit.EtaleCechDirectSum

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.EtaleCechDirectSum.cochainExactAt_succ_iff,
      ``ManuscriptAudit.EtaleCechDirectSum.directSum_exactAt_succ,
      ``ManuscriptAudit.EtaleCechDirectSum.affineEtaleDirectSum_H_succ_isZero] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
