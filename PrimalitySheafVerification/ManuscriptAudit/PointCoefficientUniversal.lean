import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.PointCoefficientSheaf
import PrimalitySheafVerification.ManuscriptAudit.ZariskiSkyscraperHigherCohomology

/-! Morphisms into the point-coefficient sheaf are families of maps from stalks. -/

namespace ManuscriptAudit.PointCoefficientUniversal

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open PointCoefficientSheaf ClosedSupportDetection

noncomputable section

variable {X : TopCat.{0}} (P : Set X) (A : P → Type)
variable [∀ p : P, AddCommGroup (A p)]

private abbrev G := AddCommGrpCat.{0}

private def atNeighborhood (p : P) (U : OpenNhds p.val) :
    (presheaf P A).obj (op ((OpenNhds.inclusion p.val).obj U)) ⟶ G.of (A p) :=
  G.ofHom
    { toFun := fun s => s ⟨p, U.property⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }

/-- Evaluation of a genuine germ at the chosen coefficient. -/
def stalkEvaluation (p : P) :
    (presheaf P A).stalk p.val ⟶ G.of (A p) := by
  refine colimit.desc ((OpenNhds.inclusion p.val).op ⋙ presheaf P A)
    { pt := G.of (A p)
      ι :=
        { app := fun U => atNeighborhood P A p U.unop
          naturality := ?_ } }
  intro U V f
  apply ConcreteCategory.hom_ext
  intro s
  rfl

theorem stalkEvaluation_germ (p : P) (U : Opens X) (hp : p.val ∈ U)
    (s : Sections P A U) :
    stalkEvaluation P A p ((presheaf P A).germ U p.val hp s) = s ⟨p, hp⟩ := by
  let F := presheaf P A
  let W : OpenNhds p.val := ⟨U, hp⟩
  have h : F.germ U p.val hp ≫ stalkEvaluation P A p = atNeighborhood P A p W := by
    apply colimit.ι_desc
  have h' := congrArg (fun k : F.obj (op U) ⟶ G.of (A p) => k s) h
  exact h'

variable (F : AbelianSheaf X)

private abbrev StalkAt (p : P) : AbelianSheaf X ⥤ G :=
  TopCat.Sheaf.forget G X ⋙ TopCat.Presheaf.stalkFunctor G p.val

/-- Assemble a map on sections by applying each designated stalk map to its germ. -/
def fromStalks (φ : ∀ p : P, (StalkAt P p).obj F ⟶ G.of (A p)) :
    F ⟶ sheaf P A :=
  ⟨{
    app := fun U =>
      G.ofHom
        { toFun := fun s q => φ q.val (F.obj.germ U.unop q.val.val q.property s)
          map_zero' := by funext q; simp
          map_add' := by intro s t; funext q; simp }
    naturality := by
      intro U V f
      apply ConcreteCategory.hom_ext
      intro s
      funext q
      change φ q.val (F.obj.germ V.unop q.val.val q.property (F.obj.map f s)) =
        φ q.val (F.obj.germ U.unop q.val.val (f.unop.le q.property) s)
      rw [F.obj.germ_res_apply'] }⟩

/-- The stalk maps associated to a map into the point-coefficient sheaf. -/
def toStalks (f : F ⟶ sheaf P A) (p : P) : (StalkAt P p).obj F ⟶ G.of (A p) :=
  (StalkAt P p).map f ≫ stalkEvaluation P A p

theorem fromStalks_toStalks (f : F ⟶ sheaf P A) :
    fromStalks P A F (toStalks P A F f) = f := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply ConcreteCategory.hom_ext
  intro s
  funext q
  change stalkEvaluation P A q.val
      ((TopCat.Presheaf.stalkFunctor G q.val.val).map f.hom
        (F.obj.germ U.unop q.val.val q.property s)) = f.hom.app U s q
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply, stalkEvaluation_germ]

theorem fromStalks_natural {E : AbelianSheaf X} (f : E ⟶ F)
    (φ : ∀ p : P, (StalkAt P p).obj F ⟶ G.of (A p)) :
    f ≫ fromStalks P A F φ =
      fromStalks P A E (fun p => (StalkAt P p).map f ≫ φ p) := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply ConcreteCategory.hom_ext
  intro s
  funext q
  change φ q.val (F.obj.germ U.unop q.val.val q.property (f.hom.app U s)) =
    φ q.val ((TopCat.Presheaf.stalkFunctor G q.val.val).map f.hom
      (E.obj.germ U.unop q.val.val q.property s))
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]

/-- Families of injective groups give an injective point-coefficient sheaf even for infinite P. -/
theorem injective_of_coefficients [∀ p : P, Injective (G.of (A p))] :
    Injective (sheaf P A) := by
  constructor
  intro E H g f hf
  letI : ∀ p : P, (StalkAt P p).PreservesMonomorphisms :=
    fun p => TopCat.Presheaf.stalkFunctor_preserves_mono (C := G) p.val
  let ψ (p : P) : (StalkAt P p).obj H ⟶ G.of (A p) :=
    Injective.factorThru (toStalks P A E g p) ((StalkAt P p).map f)
  refine ⟨fromStalks P A H ψ, ?_⟩
  rw [fromStalks_natural]
  have h : (fun p : P => (StalkAt P p).map f ≫ ψ p) = toStalks P A E g := by
    funext p
    exact Injective.comp_factorThru _ _
  rw [h, fromStalks_toStalks]

end
end ManuscriptAudit.PointCoefficientUniversal

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.PointCoefficientUniversal.stalkEvaluation_germ,
      ``ManuscriptAudit.PointCoefficientUniversal.fromStalks_toStalks,
      ``ManuscriptAudit.PointCoefficientUniversal.fromStalks_natural,
      ``ManuscriptAudit.PointCoefficientUniversal.injective_of_coefficients] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
