import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspOriginGeometricDirectImage
import PrimalitySheafVerification.ManuscriptAudit.GeometricSkyscraperHZero

/-!
# Surjectivity of degree-zero evaluation at a geometric point

Every value in a constant stalk comes from a global constant section.
A map from the constant sheaf to a geometric skyscraper therefore
surjects on degree-zero cohomology whenever its stalk adjoint is an
isomorphism. The statement applies to the actual rational direct image.
-/

namespace ManuscriptAudit.GeometricSkyscraperCohomology

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open ManuscriptAudit.SmallEtaleBaseChange ManuscriptAudit.SmallEtaleGeometricBaseChange

universe u

noncomputable section

attribute [local instance] etaleSiteHasExt IsFiltered.isConnected

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev C := AddCommGrpCat.{u}

variable {X : Scheme.{u}} (Φ : X.smallEtaleTopology.Point.{u})
variable (M : C.{u})

/-- The germ map of any displayed neighborhood is surjective for an actual constant sheaf. -/
theorem constantEtaleGerm_surjective (T : X.Etale) (t : Φ.fiber.obj T) :
    Function.Surjective (Φ.toPresheafFiber T t
      ((constantSheaf X.smallEtaleTopology C.{u}).obj M).obj) := by
  let P := (Functor.const X.Etaleᵒᵖ).obj M
  let Q := ((constantSheaf X.smallEtaleTopology C.{u}).obj M).obj
  let η : P ⟶ Q := toSheafify X.smallEtaleTopology P
  let b := Φ.toPresheafFiber T t P
  let c := Φ.toPresheafFiber T t Q
  let a := Φ.isColimitPresheafFiberCocone P
  let d := isColimitConstCocone (Φ.fiber.Elementsᵒᵖ) M
  let e : Φ.presheafFiber.obj P ≅ M := IsColimit.coconePointUniqueUpToIso a d
  have h₀ : b ≫ e.hom = 𝟙 M :=
    IsColimit.comp_coconePointUniqueUpToIso_hom a d (op ⟨T, t⟩)
  letI : IsIso (b ≫ e.hom) := by rw [h₀]; infer_instance
  letI : IsIso b := IsIso.of_isIso_comp_right b e.hom
  letI : IsIso (Φ.presheafFiber.map η) :=
    inferInstanceAs (IsIso (Φ.presheafFiber.map (toSheafify X.smallEtaleTopology P)))
  have h : η.app (op T) ≫ c = b ≫ Φ.presheafFiber.map η :=
    (Φ.toPresheafFiber_naturality η T t).symm
  have hs : Function.Surjective (η.app (op T) ≫ c) := by
    rw [h]
    exact (ConcreteCategory.bijective_of_isIso _).surjective
  intro y
  obtain ⟨m, hm⟩ := hs y
  exact ⟨η.app (op T) m, hm⟩

/-- If the adjoint through the actual point is an isomorphism, the
map from constant global cohomology to the skyscraper is surjective. -/
theorem HZero_surjective_of_stalkAdjoint_iso (N : C.{u})
    (f : (constantSheaf X.smallEtaleTopology C.{u}).obj M ⟶ Φ.skyscraperSheaf N)
    (hf : IsIso (Φ.sheafFiber.map f ≫ Φ.skyscraperSheafAdjunction.counit.app N)) :
    Function.Surjective (Sheaf.H.map f 0) := by
  let F := (constantSheaf X.smallEtaleTopology C.{u}).obj M
  let G := Φ.skyscraperSheaf N
  let T := ⊤_ X.Etale
  let hT := terminalIsTerminal (C := X.Etale)
  letI : Unique (Φ.fiber.obj T) := Φ.uniqueFiberObj T hT
  let t : Φ.fiber.obj T := default
  let q : G.obj.obj (op T) ⟶ N := Pi.π (fun _ : Φ.fiber.obj T => N) t
  letI : IsIso q :=
    inferInstanceAs (IsIso (productUniqueIso (fun _ : Φ.fiber.obj T => N)).hom)
  let a := Φ.skyscraperSheafAdjunction (A := C.{u})
  let k : Φ.presheafFiber.obj F.obj ⟶ N := (a.homEquiv F N).symm f
  have hk : k = Φ.sheafFiber.map f ≫ a.counit.app N :=
    (a.homEquiv_counit F N f).symm
  letI : IsIso k := hk ▸ hf
  have h : f.hom.app (op T) ≫ q = Φ.toPresheafFiber T t F.obj ≫ k :=
    (Φ.toPresheafFiber_skyscraperPresheafHomEquiv_symm f.hom T t).symm
  have hs : Function.Surjective (f.hom.app (op T) ≫ q) := by
    rw [h]
    exact (ConcreteCategory.bijective_of_isIso k).surjective.comp
      (constantEtaleGerm_surjective Φ M T t)
  let eF := Sheaf.H.equiv₀ F hT
  let eG := Sheaf.H.equiv₀ G hT
  intro y
  obtain ⟨z, hz⟩ := hs (q (eG y))
  refine ⟨eF.symm z, eG.injective ((ConcreteCategory.bijective_of_isIso q).injective ?_)⟩
  change q (Sheaf.H.equiv₀ G hT (Sheaf.H.map f 0 (eF.symm z))) = q (eG y)
  rw [← Sheaf.H.equiv₀_naturality, AddEquiv.apply_symm_apply]
  exact hz

/-- The canonical evaluation on the constant sheaf, defined by the native constant stalk iso. -/
def constantToGeometricSkyscraper :
    (constantSheaf X.smallEtaleTopology C.{u}).obj M ⟶ Φ.skyscraperSheaf M :=
  (Φ.skyscraperSheafAdjunction.homEquiv _ M) (constantEtaleStalkIso Φ M).hom

theorem constantToGeometricSkyscraper_HZero_surjective :
    Function.Surjective (Sheaf.H.map (constantToGeometricSkyscraper Φ M) 0) := by
  let F := (constantSheaf X.smallEtaleTopology C.{u}).obj M
  let a := Φ.skyscraperSheafAdjunction (A := C.{u})
  let f := constantToGeometricSkyscraper Φ M
  apply HZero_surjective_of_stalkAdjoint_iso Φ M M
  have h : Φ.sheafFiber.map f ≫ a.counit.app M = (constantEtaleStalkIso Φ M).hom :=
    (a.homEquiv_counit F M f).symm.trans ((a.homEquiv F M).symm_apply_apply _)
  change IsIso (Φ.sheafFiber.map f ≫ a.counit.app M)
  rw [h]
  infer_instance

variable (K : Type u) [Field K] [IsSepClosed K]
variable (o : Spec (CommRingCat.of K) ⟶ X)

/-- Evaluation into the actual small étale direct image from a separably closed point. -/
def constantToRationalDirectImage :
    (constantSheaf X.smallEtaleTopology C.{u}).obj M ⟶
      (directImage o C.{u}).obj
        ((constantSheaf (Spec (CommRingCat.of K)).smallEtaleTopology C.{u}).obj M) :=
  constantToGeometricSkyscraper (Scheme.pointSmallEtale o) M ≫
    (rationalPointConstantDirectImageIso K o M).inv

theorem constantToRationalDirectImage_HZero_surjective :
    Function.Surjective (Sheaf.H.map (constantToRationalDirectImage M K o) 0) := by
  let f := constantToGeometricSkyscraper (Scheme.pointSmallEtale o) M
  let g := (rationalPointConstantDirectImageIso K o M).symm
  let e := ((Sheaf.functorH X.smallEtaleTopology 0).mapIso g).addCommGroupIsoToAddEquiv
  intro y
  obtain ⟨x, hx⟩ := constantToGeometricSkyscraper_HZero_surjective (Scheme.pointSmallEtale o) M
    (e.symm y)
  refine ⟨x, ?_⟩
  change Sheaf.H.map (f ≫ g.hom) 0 x = y
  rw [Sheaf.H.map_comp_apply, hx]
  exact e.apply_symm_apply y

end

end ManuscriptAudit.GeometricSkyscraperCohomology

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.GeometricSkyscraperCohomology.constantEtaleGerm_surjective,
      ``ManuscriptAudit.GeometricSkyscraperCohomology.HZero_surjective_of_stalkAdjoint_iso,
      ``ManuscriptAudit.GeometricSkyscraperCohomology.constantToGeometricSkyscraper_HZero_surjective,
      ``ManuscriptAudit.GeometricSkyscraperCohomology.constantToRationalDirectImage_HZero_surjective] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
