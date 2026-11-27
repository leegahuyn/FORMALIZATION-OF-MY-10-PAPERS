import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import PrimalitySheafVerification.ManuscriptAudit.EtaleObjectRestriction
import PrimalitySheafVerification.ManuscriptAudit.GeometricSkyscraperHigherCohomology

/-! Restricting a geometric skyscraper to an actual open subsite. -/

namespace ManuscriptAudit.OpenEtaleSkyscraperRestriction

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open EtaleObjectRestriction GeometricSkyscraperCohomology

noncomputable section

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] etaleSiteHasExt

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
variable {Ω : Type u} [Field Ω] [IsSepClosed Ω]

private def fiberEquiv (t : Spec (.of Ω) ⟶ U) (W : U.Etale) :
    (Scheme.pointSmallEtale (t ≫ j)).fiber.obj ((postcompose j).obj W) ≃
      (Scheme.pointSmallEtale t).fiber.obj W where
  toFun s := Over.homMk s.left (by
    have hs : s.left ≫ (W.hom ≫ j) = t ≫ j := Over.w s
    exact (cancel_mono j).mp ((Category.assoc _ _ _).trans hs))
  invFun s := Over.homMk s.left (by
    change s.left ≫ (W.hom ≫ j) = t ≫ j
    rw [← Category.assoc, show s.left ≫ W.hom = t from Over.w s])
  left_inv s := CostructuredArrow.hom_ext rfl
  right_inv s := CostructuredArrow.hom_ext rfl

/-- A geometric point factoring through an open gives the same fibers
on the actual open-site postcomposition functor. -/
def fiberPostcomposeIso (t : Spec (.of Ω) ⟶ U) :
    postcompose j ⋙ (Scheme.pointSmallEtale (t ≫ j)).fiber ≅
      (Scheme.pointSmallEtale t).fiber :=
  NatIso.ofComponents (fun W ↦ (fiberEquiv j t W).toIso) (fun {W V} f ↦ by
    apply ConcreteCategory.hom_ext
    intro s
    exact CostructuredArrow.hom_ext rfl)

/-- The actual restriction of a skyscraper at a point inside the open
is the skyscraper at its factorization. -/
def restrictionInsideIso (t : Spec (.of Ω) ⟶ U) (M : AddCommGrpCat.{u}) :
    (restriction j).obj ((Scheme.pointSmallEtale (t ≫ j)).skyscraperSheaf M) ≅
      (Scheme.pointSmallEtale t).skyscraperSheaf M := by
  let G := postcompose j
  let Φ := Scheme.pointSmallEtale (t ≫ j)
  let Ψ := Scheme.pointSmallEtale t
  let P := (piFunctor.{u} (C := AddCommGrpCat.{u})).obj M
  let e : G ⋙ Φ.fiber ≅ Ψ.fiber := fiberPostcomposeIso j t
  apply (fullyFaithfulSheafToPresheaf U.smallEtaleTopology AddCommGrpCat.{u}).preimageIso
  change G.op ⋙ (Φ.fiber.op ⋙ P) ≅ Ψ.fiber.op ⋙ P
  exact (CategoryTheory.Functor.associator _ _ _).symm ≪≫
    CategoryTheory.Functor.isoWhiskerRight
      ((CategoryTheory.Functor.opComp _ _).symm ≪≫ (CategoryTheory.NatIso.op e).symm) P

/-- Restricting a geometric skyscraper with no factorization through
the open gives the zero sheaf. -/
theorem restrictionOutside_isZero (s : Spec (.of Ω) ⟶ X)
    (hs : ¬ ∃ t : Spec (.of Ω) ⟶ U, t ≫ j = s) (M : AddCommGrpCat.{u}) :
    IsZero ((restriction j).obj ((Scheme.pointSmallEtale s).skyscraperSheaf M)) := by
  let Φ := Scheme.pointSmallEtale s
  let F := (restriction j).obj (Φ.skyscraperSheaf M)
  have hObj (V : U.Etaleᵒᵖ) : IsZero (F.obj.obj V) := by
    change IsZero (∏ᶜ fun _ : Φ.fiber.obj ((postcompose j).obj V.unop) ↦ M)
    rw [IsZero.iff_id_eq_zero]
    apply Pi.hom_ext
    intro a
    have ha : a.left ≫ (V.unop.hom ≫ j) = s := Over.w a
    exact (hs ⟨a.left ≫ V.unop.hom, (Category.assoc _ _ _).trans ha⟩).elim
  rw [IsZero.iff_id_eq_zero]
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  exact (hObj V).eq_of_src _ _

/-- The restriction of any geometric skyscraper to an open has zero
positive ordinary étale cohomology. -/
theorem restriction_H_succ_subsingleton (s : Spec (.of Ω) ⟶ X)
    (M : AddCommGrpCat.{u}) (n : ℕ) :
    Subsingleton (Sheaf.H ((restriction j).obj ((Scheme.pointSmallEtale s).skyscraperSheaf M))
      (n + 1)) := by
  by_cases h : ∃ t : Spec (.of Ω) ⟶ U, t ≫ j = s
  · obtain ⟨t, rfl⟩ := h
    let e := ((Sheaf.functorH U.smallEtaleTopology (n + 1)).mapIso
      (restrictionInsideIso j t M)).addCommGroupIsoToAddEquiv
    have hT := geometricSkyscraperH_succ_subsingleton (Scheme.pointSmallEtale t) M n
    exact ⟨fun a b ↦ e.injective (hT.elim _ _)⟩
  · let H := Sheaf.functorH U.smallEtaleTopology (n + 1)
    have hZ := H.map_isZero (restrictionOutside_isZero j s h M)
    have hid := (IsZero.iff_id_eq_zero _).mp hZ
    exact subsingleton_of_forall_eq 0 (fun x ↦ ConcreteCategory.congr_hom hid x)

end

end ManuscriptAudit.OpenEtaleSkyscraperRestriction

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.OpenEtaleSkyscraperRestriction.restrictionInsideIso,
      ``ManuscriptAudit.OpenEtaleSkyscraperRestriction.restrictionOutside_isZero,
      ``ManuscriptAudit.OpenEtaleSkyscraperRestriction.restriction_H_succ_subsingleton] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
