import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Sites.Point.Skyscraper

/-!
# The skyscraper stalk at a point with single-lift refinements

If each pointed neighborhood refines to one with a unique lift of the
point, the native skyscraper counit is an isomorphism. The proof checks
the actual stalk sections using the projections of the skyscraper.
-/

namespace ManuscriptAudit.SmallEtaleGeometricBaseChange

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u v w

variable {D : Type v} [Category.{w} D] {J : GrothendieckTopology D}
variable (Φ : J.Point.{u}) [LocallySmall.{u} D]

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

theorem skyscraperCounit_isIso_of_unique_refinements
    (h : ∀ (W : D) (w : Φ.fiber.obj W), ∃ (V : D) (g : V ⟶ W) (v : Φ.fiber.obj V),
      Φ.fiber.map g v = w ∧ Subsingleton (Φ.fiber.obj V))
    (M : AddCommGrpCat.{u}) :
    IsIso (Φ.skyscraperSheafAdjunction.counit.app M) := by
  let F := Φ.skyscraperSheaf M
  let P := F.obj
  let adj := Φ.skyscraperSheafAdjunction (A := AddCommGrpCat.{u})
  let ε : Φ.presheafFiber.obj P ⟶ M := adj.counit.app M
  have hCounit : ε = Φ.skyscraperPresheafHomEquiv.symm (𝟙 P) := by
    calc
      ε = (adj.homEquiv F M).symm (𝟙 F) := by
        symm
        calc
          (adj.homEquiv F M).symm (𝟙 F) =
              (Φ.sheafFiber (A := AddCommGrpCat.{u})).map (𝟙 F) ≫ adj.counit.app M :=
            adj.homEquiv_counit F M (𝟙 F)
          _ = 𝟙 ((Φ.sheafFiber (A := AddCommGrpCat.{u})).obj F) ≫ adj.counit.app M :=
            congrArg (fun g => g ≫ adj.counit.app M)
              ((Φ.sheafFiber (A := AddCommGrpCat.{u})).map_id F)
          _ = ε := Category.id_comp _
      _ = Φ.skyscraperPresheafHomEquiv.symm (𝟙 P) :=
        Φ.skyscraperSheafAdjunction_homEquiv_symm_apply (𝟙 F)
  have projection (W : D) (w : Φ.fiber.obj W) :
      Φ.toPresheafFiber W w P ≫ ε = Pi.π (fun _ : Φ.fiber.obj W => M) w := by
    calc
      Φ.toPresheafFiber W w P ≫ ε =
          Φ.toPresheafFiber W w P ≫ Φ.skyscraperPresheafHomEquiv.symm (𝟙 P) :=
        congrArg (fun f : Φ.presheafFiber.obj P ⟶ M => Φ.toPresheafFiber W w P ≫ f) hCounit
      _ = _ :=
        (Φ.toPresheafFiber_skyscraperPresheafHomEquiv_symm (𝟙 P) W w).trans
          (Category.id_comp _)
  rw [← isIso_iff_of_reflects_iso ε (forget AddCommGrpCat.{u}), isIso_iff_bijective]
  constructor
  · intro b c hbc
    obtain ⟨W, w, b', c', rfl, rfl⟩ := Φ.toPresheafFiber_jointly_surjective₂ b c
    obtain ⟨V, g, v, hv, hsub⟩ := h W w
    letI : Unique (Φ.fiber.obj V) := ⟨⟨v⟩, fun z => hsub.allEq z v⟩
    let q : P.obj (op V) ⟶ M := Pi.π (fun _ : Φ.fiber.obj V => M) v
    have hq : P.map g.op ≫ q = Φ.toPresheafFiber W w P ≫ ε := by
      calc
        P.map g.op ≫ q = P.map g.op ≫ (Φ.toPresheafFiber V v P ≫ ε) :=
          congrArg (fun f : P.obj (op V) ⟶ M => P.map g.op ≫ f) (projection V v).symm
        _ = _ := by rw [← Category.assoc, Φ.toPresheafFiber_w, hv]
    letI : IsIso q := (productUniqueIso (fun _ : Φ.fiber.obj V => M)).isIso_hom
    have hqbc : q (P.map g.op b') = q (P.map g.op c') := by
      change (P.map g.op ≫ q) b' = (P.map g.op ≫ q) c'
      rw [hq]
      exact hbc
    exact (Φ.toPresheafFiber_eq_iff' W w b' c').mpr
      ⟨V, g, v, hv, (ConcreteCategory.bijective_of_isIso q).injective hqbc⟩
  · intro m
    obtain ⟨z⟩ := (IsCofiltered.nonempty : Nonempty Φ.fiber.Elements)
    let l : M ⟶ P.obj (op z.1) := Pi.lift (fun _ : Φ.fiber.obj z.1 => 𝟙 M)
    refine ⟨Φ.toPresheafFiber z.1 z.2 P (l m), ?_⟩
    have hl : l ≫ (Φ.toPresheafFiber z.1 z.2 P ≫ ε) = 𝟙 M :=
      (congrArg (fun f : P.obj (op z.1) ⟶ M => l ≫ f) (projection z.1 z.2)).trans
        (Pi.lift_π _ _)
    exact congrArg (fun f : M ⟶ M => f m) hl

end

end ManuscriptAudit.SmallEtaleGeometricBaseChange

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.SmallEtaleGeometricBaseChange.skyscraperCounit_isIso_of_unique_refinements
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
