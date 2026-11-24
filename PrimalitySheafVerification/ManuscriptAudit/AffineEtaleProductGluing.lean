import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Surjective
import Mathlib.AlgebraicGeometry.Sites.AffineEtale

/-!
# Gluing lifts along the components of a finite affine product

The affine étale scheme of a finite product of rings is covered by its
component spectra. Distinct components have empty intersections, and
each component inclusion is monic. Sections of an abelian sheaf on the
components glue uniquely on the product.
-/

namespace ManuscriptAudit.AffineEtaleProductGluing

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u v

variable {X : Scheme.{u}}

private abbrev underlying (X : Scheme.{u}) : X.AffineEtale ⥤ Scheme.{u} :=
  Scheme.AffineEtale.Spec X ⋙ Scheme.Etale.forget X ⋙ Over.forget X

private theorem cover_of_jointly_surjective {U : X.AffineEtale}
    {ι : Type v} (V : ι → X.AffineEtale) (f : ∀ i, V i ⟶ U)
    (h : ∀ x : (underlying X).obj U, ∃ i, ∃ y : (underlying X).obj (V i),
      (underlying X).map (f i) y = x) :
    Sieve.ofArrows V f ∈ Scheme.AffineEtale.topology X U := by
  rw [Scheme.AffineEtale.topology, Functor.mem_inducedTopology_iff_of_isCoverDense,
    Sieve.functorPushforward_ofArrows]
  apply (Scheme.ofArrows_mem_smallEtaleTopology_iff _).mpr
  ext x
  simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
  exact h x

private theorem sections_subsingleton_of_empty
    (I : Sheaf (Scheme.AffineEtale.topology X) AddCommGrpCat.{u})
    (W : X.AffineEtale) [IsEmpty ((underlying X).obj W)] :
    Subsingleton (I.obj.obj (op W)) := by
  let V : PEmpty → X.AffineEtale := PEmpty.elim
  let f : ∀ i, V i ⟶ W := PEmpty.elim
  have hCov := cover_of_jointly_surjective V f (fun x => isEmptyElim x)
  let P := I.obj ⋙ forget AddCommGrpCat.{u}
  have hI : Presieve.IsSheaf (Scheme.AffineEtale.topology X) P :=
    (isSheaf_iff_isSheaf_of_type _ P).mp ((sheafCompose _ (forget AddCommGrpCat.{u})).obj I).property
  obtain ⟨t, _, ht⟩ :=
    (Presieve.isSheafFor_arrows_iff (P := P) f).mp (hI.isSheafFor _ hCov)
      (fun i => PEmpty.elim i) (fun i => PEmpty.elim i)
  exact ⟨fun a b => (ht a (fun i => PEmpty.elim i)).trans (ht b (fun i => PEmpty.elim i)).symm⟩

variable {ι : Type u} (B : ι → CommRingCat.{u})

/-- The ring product of the given finite affine family. -/
abbrev productRing : CommRingCat.{u} := CommRingCat.of (∀ i, B i)

private abbrev componentMap (i : ι) : Spec (B i) ⟶ Spec (productRing B) :=
  Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun i => (B i : Type u)) i))

variable (g : Spec (productRing B) ⟶ X) [Etale g]

/-- The affine étale object associated with the ring product. -/
noncomputable def productObject : X.AffineEtale := Scheme.AffineEtale.mk g

/-- A component equipped with the same structure map by composition. -/
noncomputable def componentObject (i : ι) : X.AffineEtale :=
  Scheme.AffineEtale.mk (componentMap B i ≫ g)

/-- The open component inclusion on the actual affine étale site. -/
noncomputable def componentArrow (i : ι) : componentObject B g i ⟶ productObject B g :=
  MorphismProperty.CostructuredArrow.homMk
    (CommRingCat.ofHom (Pi.evalRingHom (fun i => (B i : Type u)) i)).op trivial rfl

variable [Finite ι]

private theorem component_cover :
    Sieve.ofArrows (componentObject B g) (componentArrow B g) ∈
      Scheme.AffineEtale.topology X (productObject B g) := by
  apply cover_of_jointly_surjective
  intro x
  change ↑(Spec (productRing B)) at x
  have hs : Function.Surjective (Scheme.sigmaSpec B) :=
    (inferInstance : Surjective (Scheme.sigmaSpec B)).surj
  obtain ⟨z, rfl⟩ := hs x
  obtain ⟨⟨i, y⟩, rfl⟩ := (Scheme.sigmaMk (fun i => Spec (B i))).surjective z
  refine ⟨i, y, ?_⟩
  change componentMap B i y =
    Scheme.sigmaSpec B (Scheme.sigmaMk (fun i => Spec (B i)) ⟨i, y⟩)
  rw [Scheme.sigmaMk_mk, ← Scheme.Hom.comp_apply, Scheme.ι_sigmaSpec]

set_option backward.isDefEq.respectTransparency false in
/-- Sections on the affine open components of a finite product glue uniquely. -/
theorem glue_sections
    (I : Sheaf (Scheme.AffineEtale.topology X) AddCommGrpCat.{u})
    (s : ∀ i, I.obj.obj (op (componentObject B g i))) :
    ∃! z : I.obj.obj (op (productObject B g)),
      ∀ i, I.obj.map (componentArrow B g i).op z = s i := by
  let P := I.obj ⋙ forget AddCommGrpCat.{u}
  have hI : Presieve.IsSheaf (Scheme.AffineEtale.topology X) P :=
    (isSheaf_iff_isSheaf_of_type _ P).mp ((sheafCompose _ (forget AddCommGrpCat.{u})).obj I).property
  have hs : Presieve.Arrows.Compatible P (componentArrow B g) s := by
    intro i j W p q hpq
    change I.obj.map p.op (s i) = I.obj.map q.op (s j)
    have hw : (underlying X).map p ≫ componentMap B i =
        (underlying X).map q ≫ componentMap B j := by
      simpa only [Functor.map_comp] using (underlying X).congr_map hpq
    by_cases hij : i = j
    · subst j
      have hpq' : p = q :=
        (underlying X).map_injective ((cancel_mono (componentMap B i)).mp hw)
      rw [hpq']
    · have hw' : (underlying X).map p ≫ Sigma.ι (fun i => Spec (B i)) i =
          (underlying X).map q ≫ Sigma.ι (fun i => Spec (B i)) j := by
        apply (cancel_mono (Scheme.sigmaSpec B)).mp
        simpa only [Category.assoc, Scheme.ι_sigmaSpec] using hw
      letI : IsEmpty ((underlying X).obj W) :=
        Scheme.isEmpty_of_commSq_sigmaι_of_ne ⟨hw'⟩ hij
      exact (sections_subsingleton_of_empty I W).elim _ _
  exact (Presieve.isSheafFor_arrows_iff (P := P) (componentArrow B g)).mp
    (hI.isSheafFor _ (component_cover B g)) s hs

/-- Componentwise lifts of one product section glue to a lift on the product. -/
theorem exists_lift_from_component_lifts
    {I Q : Sheaf (Scheme.AffineEtale.topology X) AddCommGrpCat.{u}}
    (q : I ⟶ Q) (x : Q.obj.obj (op (productObject B g)))
    (h : ∀ i, ∃ s : I.obj.obj (op (componentObject B g i)),
      q.hom.app (op (componentObject B g i)) s =
        Q.obj.map (componentArrow B g i).op x) :
    ∃ y : I.obj.obj (op (productObject B g)), q.hom.app (op (productObject B g)) y = x := by
  classical
  choose s hs using h
  obtain ⟨y, hy, _⟩ := glue_sections B g I s
  obtain ⟨z, _, hz⟩ := glue_sections B g Q (fun i => Q.obj.map (componentArrow B g i).op x)
  refine ⟨y, ?_⟩
  have hqy : ∀ i, Q.obj.map (componentArrow B g i).op (q.hom.app (op (productObject B g)) y) =
      Q.obj.map (componentArrow B g i).op x := by
    intro i
    rw [← NatTrans.naturality_apply, hy, hs]
  exact (hz _ hqy).trans (hz x (fun _ => rfl)).symm

end ManuscriptAudit.AffineEtaleProductGluing

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineEtaleProductGluing.glue_sections,
      ``ManuscriptAudit.AffineEtaleProductGluing.exists_lift_from_component_lifts] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
