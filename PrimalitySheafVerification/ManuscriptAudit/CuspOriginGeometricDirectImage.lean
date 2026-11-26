import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Sites.Point.Conservative
import PrimalitySheafVerification.ManuscriptAudit.SmallEtaleGeometricSkyscraperPushforward

/-!
# The constant sheaf at the separably closed cusp residue field

Over a separably closed field the identity geometric point is conservative.
Its category of pointed neighborhoods has an initial object. The skyscraper
counit there is evaluation at the unique index, so constants are identified
with the skyscrapers on that residue-field site.
-/

namespace ManuscriptAudit.SmallEtaleGeometricBaseChange

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite SmallEtaleBaseChange

noncomputable section

universe u

private abbrev C := AddCommGrpCat.{u}

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] IsFiltered.isConnected

/-- A constant abelian étale sheaf has the given coefficient group as each point stalk. -/
def constantEtaleStalkIso {X : Scheme.{u}} (Φ : X.smallEtaleTopology.Point.{u}) (M : C.{u}) :
    Φ.sheafFiber.obj ((constantSheaf X.smallEtaleTopology C.{u}).obj M) ≅ M := by
  let P := (Functor.const X.Etaleᵒᵖ).obj M
  exact (Φ.presheafToSheafCompSheafFiberIso C.{u}).app P ≪≫
    IsColimit.coconePointUniqueUpToIso (Φ.isColimitPresheafFiberCocone P)
      (isColimitConstCocone _ M)

variable (K : Type u) [Field K] [IsSepClosed K]

private abbrev S := Spec (CommRingCat.of K)
private abbrev p := Scheme.pointSmallEtale (𝟙 (S K))
private abbrev T : (S K).Etale := Scheme.Etale.mk (𝟙 (S K))
private abbrev x : (p K).fiber.obj (T K) := 𝟙 (Over.mk (𝟙 (S K)))

private def identityPointInitial :
    IsInitial (⟨T K, x K⟩ : (p K).fiber.Elements) := by
  let e := Scheme.Etale.forgetFullyFaithful (S K)
  refine IsInitial.ofUniqueHom (fun W => ⟨e.preimage W.2, ?_⟩) ?_
  · change (𝟙 _ ≫ (Scheme.Etale.forget (S K)).map (e.preimage W.2)) = W.2
    simp only [Category.id_comp, e.map_preimage]
  · intro W f
    apply Subtype.ext
    apply (Scheme.Etale.forget (S K)).map_injective
    have hf := f.property
    change (𝟙 _ ≫ (Scheme.Etale.forget (S K)).map f.val) = W.2 at hf
    simpa only [Category.id_comp, e.map_preimage] using hf

private theorem identityPointCounitIsIso (M : C.{u}) :
    IsIso ((p K).skyscraperSheafAdjunction.counit.app M) := by
  let Φ := p K
  let P := Φ.skyscraperPresheaf M
  let f := Φ.toPresheafFiber (T K) (x K) P
  let a := Φ.skyscraperSheafAdjunction (A := C.{u})
  letI : IsIso f := (Φ.isColimitPresheafFiberCocone P).isIso_ι_app_of_isTerminal _
    (identityPointInitial K).op
  letI : Unique (Φ.fiber.obj (T K)) :=
    ⟨⟨x K⟩, fun y => (Over.mkIdTerminal (X := S K)).hom_ext y (x K)⟩
  have hCounit : a.counit.app M = Φ.skyscraperPresheafHomEquiv.symm (𝟙 P) := by
    rw [← Φ.skyscraperSheafAdjunction_homEquiv_symm_apply (𝟙 (Φ.skyscraperSheaf M)),
      Adjunction.homEquiv_counit, Functor.map_id, Category.id_comp]
  have h : f ≫ a.counit.app M = Pi.π (fun _ : Φ.fiber.obj (T K) => M) (x K) := by
    rw [hCounit, Φ.toPresheafFiber_skyscraperPresheafHomEquiv_symm]
    simp
  letI : IsIso (f ≫ a.counit.app M) := by
    rw [h]
    exact (productUniqueIso (fun _ : Φ.fiber.obj (T K) => M)).isIso_hom
  exact IsIso.of_isIso_comp_left f (a.counit.app M)

private theorem identityPointReflectsIso {F Q : Sheaf (S K).smallEtaleTopology C.{u}} (f : F ⟶ Q)
    [IsIso ((p K).sheafFiber.map f)] : IsIso f := by
  let P := ObjectProperty.ofObj (fun _ : Unit => p K)
  have hP : P.IsConservativeFamilyOfPoints :=
    Scheme.isConservative_pointSmallEtale (fun _ : Unit => 𝟙 (S K)) (by
      ext y
      simp)
  letI : ∀ q : P.FullSubcategory, IsIso (q.obj.sheafFiber.map f) := fun q => by
    obtain ⟨_, hq⟩ := (ObjectProperty.ofObj_iff (fun _ : Unit => p K) q.obj).mp q.property
    rw [← hq]
    infer_instance
  exact (hP.jointlyReflectIsomorphisms C.{u}).isIso f

/-- On a separably closed field, the constant étale sheaf is the skyscraper of the identity point. -/
def separablyClosedConstantSkyscraperIso (M : C.{u}) :
    (constantSheaf (S K).smallEtaleTopology C.{u}).obj M ≅ (p K).skyscraperSheaf M := by
  let Φ := p K
  let a := Φ.skyscraperSheafAdjunction (A := C.{u})
  let e := constantEtaleStalkIso Φ M
  let f := (a.homEquiv _ M) e.hom
  have h : Φ.sheafFiber.map f ≫ a.counit.app M = e.hom := by
    rw [← a.homEquiv_counit]
    exact (a.homEquiv _ _).symm_apply_apply _
  letI : IsIso (a.counit.app M) := identityPointCounitIsIso K M
  letI : IsIso (Φ.sheafFiber.map f ≫ a.counit.app M) := by rw [h]; infer_instance
  letI : IsIso (Φ.sheafFiber.map f) := IsIso.of_isIso_comp_right _ _
  letI : IsIso f := identityPointReflectsIso K f
  exact asIso f

/-- Actual direct image of the constant sheaf from a separably closed rational point. -/
def rationalPointConstantDirectImageIso {X : Scheme.{u}} (o : S K ⟶ X) (M : C.{u}) :
    (directImage o C.{u}).obj ((constantSheaf (S K).smallEtaleTopology C.{u}).obj M) ≅
      (Scheme.pointSmallEtale o).skyscraperSheaf M :=
  (directImage o C.{u}).mapIso (separablyClosedConstantSkyscraperIso K M) ≪≫
    (geometricSkyscraperDirectImageIso o (𝟙 (S K))).app M ≪≫
      eqToIso (by rw [Category.id_comp])

/-- The constant sheaf's actual direct image from the rational cusp origin is
the geometric skyscraper at that origin. -/
def cuspOriginConstantDirectImageIso (M : C.{u}) :
    (directImage (cuspOrigin K) C.{u}).obj ((constantSheaf (S K).smallEtaleTopology C.{u}).obj M) ≅
      (Scheme.pointSmallEtale (cuspOrigin K)).skyscraperSheaf M :=
  rationalPointConstantDirectImageIso K (cuspOrigin K) M

end

end ManuscriptAudit.SmallEtaleGeometricBaseChange

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.SmallEtaleGeometricBaseChange.constantEtaleStalkIso,
      ``ManuscriptAudit.SmallEtaleGeometricBaseChange.separablyClosedConstantSkyscraperIso,
      ``ManuscriptAudit.SmallEtaleGeometricBaseChange.rationalPointConstantDirectImageIso,
      ``ManuscriptAudit.SmallEtaleGeometricBaseChange.cuspOriginConstantDirectImageIso] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
